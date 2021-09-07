open Base
open Stdio

(* 
   ARCHITECTURE:
       input -> parse -> actualize -> (interpret | compile)

       A string input is parsed into a parse tree (a bit more useful than tokenization),
       which is then converted to a full abstract syntax tree (AST), which can then be
       either interpreted with a tree-walk or compiled into bytecode.
 *)

(*
    REFERENCES:
        - Revised^5 Report on the Algorithmic Language Scheme
        - Revised^7 Report on the Algorithmic Language Scheme
        - Structure and Interpretation of Computer Programs
        - Crafting Interpreters
        - random blog posts on the internet about Lisp/Scheme
*)

let print str =
    Out_channel.output_string stdout str;
    Out_channel.output_string stdout "\n";
    Out_channel.flush stdout;

type lisp_parse =
    | Atom of string
    | IntegerLiteral of int
    | FloatLiteral of float
    | BooleanLiteral of bool
    | StringLiteral of string
    | Quote of lisp_parse
    | List of lisp_parse list
[@@deriving show]

(* Returns a parse tree of type lisp_parse *)
let parse = 
    let open Angstrom in

    let lp = char '(' <?> "lparen" in
    let rp = char ')' <?> "rparen" in
    let quote = char '\'' <?> "quote" in

    let num =
        take_while1 (function
            | '\x20' | '\x0a' | '\x0d' | '\x09'
            | '(' | ')' | ':' | ',' -> false
            | _ -> true)
        >>= fun s ->
        try return (IntegerLiteral (Int.of_string s))
        with _ ->
        try return (FloatLiteral (Float.of_string s))
        with _ -> fail "invalid number literal" in

    let string =
        char '"' *> take_while1 (function '"' -> false | _ -> true) <* char '"' <?> "string literal"
        >>| fun x -> StringLiteral x in
    
    let boolean_true =
        Angstrom.string "#t" <?> "boolean literal"
        >>| fun _ -> BooleanLiteral true in

    let boolean_false =
        Angstrom.string "#f" <?> "boolean literal"
        >>| fun _ -> BooleanLiteral false in

    let atom = take_while1 (function ' ' | '(' | ')' | '\'' | '"' -> false | _ -> true) <?> "atom"
        >>| fun x -> Atom x in

    let ws = skip_while (function
      | '\x20' | '\x0a' | '\x0d' | '\x09' -> true
      | _ -> false) in

    let lisp = fix (fun lisp ->
        let ele = choice [num; string; boolean_true; boolean_false; atom] in
        let list = lp *> many (ws *> lisp <* ws) <* rp >>| fun x -> List x in
        (both (option '\x00' quote) (list <|> ele)
        >>| fun res -> match res with
        | ('\'', x) -> Quote x
        | (_, x) -> x)
    ) in

    parse_string ~consume:All lisp

(* the abstract syntax tree representation for this lisp *)
type lisp =
    (* A reference type, which resides in a location in memory *)
    | Object of reference ref

    (* Primitive expressions/values *)
    | Integer of int
    | Float of float
    | Boolean of bool
    | Symbol of string
    | Char of char
    | Quote of lisp

and reference = {is_mutable: bool; value: reference_value}
and reference_value =
    (* Homebrewed linked list *)
    | Pair of pair

    (* | Vector of lisp Array.t *)

    (* a string *)
    | String of string

    (* a compound procedure, which holds both a closure and the procedure itself *)
    | Lambda of environment * lisp

    (* a builtin procedure, which can only be accessed from the initial environment *)
    | Builtin of (lisp -> lisp)

and pair = Nil | CC of lisp * lisp
and environment = {
    parent: environment ref option;
    table: (string, lisp) Hashtbl.t
}

exception SyntaxError of string

let is_syntactic_keyword = function
    | "and" | "or" | "set!"
    | "if" | "lambda" | "begin" -> true
    | _ -> false

let _null = { is_mutable = false; value = Pair Nil }

let null = Object (ref _null)

let rec actualize (parse_tree: lisp_parse): lisp =
    match parse_tree with
    | Atom x -> Symbol x
    | IntegerLiteral x -> Integer x
    | FloatLiteral x -> Float x
    | BooleanLiteral x -> Boolean x

    (* string constants are not mutable *)
    | StringLiteral x -> Object (ref { is_mutable = false; value = String x })

    | Quote x -> Quote (actualize x)

    | List x -> (
        match x with
        (* Empty list *)
        | [] -> null

        (* parsing pairs with dot notation *)
        | hd :: Atom "." :: tl :: [] ->
                Object (ref {
                    is_mutable = true;
                    value = Pair (CC ((actualize hd), (actualize tl)));
                })
        | _ :: Atom "." :: _ ->
                raise (SyntaxError "Incorrect usage of . notation")

        (* Otherwise, a standard list *)
        | hd :: tl ->
                Object (ref {
                    is_mutable = true;
                    value = Pair (CC ((actualize hd), (actualize (List tl))));
        })

    )

let rec is_proper_list (ls: lisp) =
    match ls with
    | Object {contents = {is_mutable = _; value = Pair Nil } } -> true
    | Object {contents = {is_mutable = _; value = Pair (CC (_, tl)) } } -> is_proper_list tl
    | _ -> false

let rec to_list (ls: lisp) =
    match ls with
    | Object {contents = {is_mutable = _; value = Pair Nil } } -> []
    | Object {contents = {is_mutable = _; value = Pair (CC (hd, tl)) } } -> hd :: to_list tl
    | _ -> assert false

let rec show_lisp (ast: lisp) =
    match ast with
    | list when is_proper_list list -> "(" ^ String.concat ~sep:" " (List.map (to_list list) ~f:show_lisp) ^ ")"
    | Object { contents = {is_mutable = _; value = y}} -> show_reference_value y

    (* Primitives are immutable and reside on the stack (at least, behavior-wise) *)
    | Integer x -> Int.to_string x
    | Float x -> Float.to_string x
    | Boolean x -> Bool.to_string x
    | Symbol x -> x
    | Char x -> Char.to_string x
    | Quote x -> "'" ^ (show_lisp x)

and show_reference_value rv =
    match rv with
    | Lambda (_, _) -> "Compound procedure"
    | Builtin _ -> "Builtin procedure"
    | Pair Nil -> "()"
    | Pair (CC (a, b)) -> "(" ^ (show_lisp a) ^ " . " ^ (show_lisp b) ^ ")"
    | String x -> "\"" ^ x ^ "\""

(* Eval / Apply *)
exception RuntimeError of string

let rec env_lookup (env: environment) symbol =
    match symbol with
    | Symbol name -> (
        match env with
        (* root environment *)
        | { parent = None; table = t } -> (
            match Hashtbl.find t name with
            | None -> raise (RuntimeError ("Unbound variable " ^ name))
            | Some value -> value
        )
        | { parent = Some p; table = t } -> (
            match Hashtbl.find t name with
            | None -> env_lookup !p (Symbol name)
            | Some value -> value
        )
    )
    | _ -> raise (RuntimeError "cannot lookup a non-symbol")

let is_undefined (env: environment) symbol: bool =
    match symbol with
    | Symbol name -> (
        try
            match env_lookup env (Symbol name) with
            | _ -> false
        with
        | RuntimeError _ -> true
    )
    | _ -> raise (RuntimeError "cannot lookup a non-symbol")

let car list =
    match list with
    | (Object { contents = {is_mutable = _; value = Pair p} }) -> (
        match p with
        | Nil -> raise (RuntimeError "cannot take car of an empty list")
        | (CC (hd, _)) -> hd
    )
    | _ -> raise (RuntimeError "cannot take the car of this object")

let cdr list =
    match list with
    | (Object { contents = {is_mutable = _; value = Pair p} }) -> (
        match p with
        | Nil -> raise (RuntimeError "cannot take cdr of an empty list")
        | (CC (_, tl)) -> tl
    )
    | _ -> raise (RuntimeError "cannot take the cdr of this object")

let cadr = Fn.compose car cdr
let cddr = Fn.compose cdr cdr

let is_null x =
    match x with
    | Object { contents = {is_mutable = _; value = Pair Nil } } -> true
    | _ -> false

let is_symbol x =
    match x with
    | Symbol _ -> true
    | _ -> false

let is_list x =
    match x with
    | Object { contents = { is_mutable = _; value = Pair _ } } -> true
    | _ -> false

let env_new parent =
    match parent with
    | Some parent_env -> { parent = Some (ref parent_env); table = Hashtbl.create(module String) }
    | None -> { parent = None; table = Hashtbl.create(module String) }

let env_set env ~key ~data =
    match env with
    | { parent = _; table = hashtbl } -> Hashtbl.set hashtbl ~key:key ~data:data

let rec map_list ~f list =
    match list with
    | Object { contents = { is_mutable = _; value = Pair Nil } } as null -> null
    | Object { contents = { is_mutable = m; value = Pair (CC (hd, tl)) } } -> (
        Object (ref { is_mutable = m; value = Pair (CC ((f hd), map_list ~f:f tl)) } )
    )
    | _ -> raise (RuntimeError "Cannot call map on non-lists")

let cons a b =
    Object (ref { is_mutable = true; value = Pair (CC (a, b))})

let fold_list list ~init ~f =
    let rec iter ls acc =
        if is_null ls then acc
        else iter (cdr ls) (f acc (car ls))
    in
    iter list init

let length_list list =
    let rec iter ls acc =
        if (is_null ls) then acc
        else (iter (cdr ls) (1 + acc))
    in
    iter list 0

let wrap_in_begin lisp =
    Object (ref { is_mutable = true; value = Pair (CC (Symbol "begin", lisp))})

let rec eval (env: environment) (ast: lisp): lisp = 
    match ast with
    (* Primitive values evaluate to themselves *)
    | Integer x -> Integer x
    | Float x -> Float x
    | Boolean x -> Boolean x
    | Char x -> Char x
    | Symbol x -> env_lookup env (Symbol x)
    | Quote x -> x

    (*** Object types ***)

    (* objects which evaluate to themselves *)
    | Object { contents = { is_mutable = _; value = String _ } } as str -> str
    | Object { contents = { is_mutable = _; value = Pair Nil } } as empty_list -> empty_list
    | Object { contents = { is_mutable = _; value = Lambda (_, _) } } as procedure -> procedure
    | Object { contents = { is_mutable = _; value = Builtin _ } } as procedure -> procedure

    (* These evaluate as a special form as long as their syntactic keyword has not been defined as a variable *)
    | Object { contents = { is_mutable = _; value = Pair (CC (Symbol "if", tl)) } }
        when is_undefined env (Symbol "if") -> (
            let condition, tl2 = car tl, cdr tl in
            let consequent, tl3 = car tl2, cdr tl2 in
            if is_null tl3 then (
                let cond = eval env condition in
                match cond with
                | Boolean false -> null
                | _ -> eval env consequent
            ) else (
                let alternate, tl4 = car tl3, cdr tl3 in
                if not (is_null tl4) then
                    raise (SyntaxError "ill-formed if")
                else (
                    let cond = eval env condition in
                    match cond with
                    | Boolean false -> eval env alternate
                    | _ -> eval env consequent
                )
            )
        )
    | Object { contents = { is_mutable = _; value = Pair (CC (Symbol "lambda", rest)) } }
        when is_undefined env (Symbol "lambda") -> 
            (
                Object (ref { is_mutable = false; value = Lambda (env, rest) })
            )

    | Object { contents = { is_mutable = m; value = Pair (CC (Symbol "begin", rest)) } }
        when is_undefined env (Symbol "begin") -> 
            (
                if is_null rest then
                    null
                else if (length_list rest = 1) then
                    eval env (car rest)
                else (
                    let _ = eval env (car rest) in
                    eval env (Object (ref { is_mutable = m; value = Pair (CC (Symbol "begin", cdr rest))}))
                )
            )

    | Object { contents = { is_mutable = _; value = Pair (CC (Symbol "define", rest)) } }
        when is_undefined env (Symbol "define") -> 
            (
                try
                    let formals = car rest in
                    let body = cdr rest in
                    match formals with
                    | Symbol name -> (
                        if (length_list body = 1) then (
                            env_set env ~key:name ~data:(eval env (car body));
                            null
                        ) else (
                            raise (RuntimeError "")
                        )
                    )
                    | Object { contents = { is_mutable = _; value = Pair (CC (Symbol f, args)) } } -> (
                        let proc = Object (ref { is_mutable = false; value = Lambda (env, cons args (cons (Symbol "begin") (cdr rest))) }) in
                        env_set env ~key:f ~data:proc;
                        null
                    )
                    | _ -> raise (RuntimeError "")
                with
                | RuntimeError msg -> print msg; raise (SyntaxError "Incorrect usage of define")
            )

    (* all other procedure calls *)
    | Object { contents = { is_mutable = _; value = Pair (CC (hd, tl)) } } -> (
        apply env (eval env hd) (map_list ~f:(eval env) tl)
    )

and apply (env: environment) procedure args =
    match procedure with
    | Object { contents = { is_mutable = _; value = Builtin f} } -> f args
    | Object { contents = { is_mutable = _; value = Lambda (closure, lambda)} } -> (
        let formals = car lambda in
        let body = cons (Symbol "begin") (cdr lambda) in
        (* print ("Formals: " ^ (show_lisp formals));
        print ("Body: " ^ (show_lisp body)); *)
        if is_null formals then
            eval env body
        else
            let new_env = env_new (Some closure) in
            let rec zip_args formals params func_env =
                if is_null formals then (* Out of both formals and params *)
                    if is_null params then
                        (* done *)
                        ()
                    else
                        (* still params remaining *)
                        raise (RuntimeError "Procedure called with too many arguments")
                else if is_symbol formals then (* when last argument is dotted *)
                    match formals with
                    | Symbol name -> (
                        env_set func_env ~key:name ~data:params
                    )
                    | _ -> assert false
                else
                    let _ = match (car formals) with
                    | Symbol name -> (
                        try
                            let p = car params in
                            env_set func_env ~key:name ~data:p
                        with
                        | RuntimeError _ -> raise (RuntimeError "Procedure called with too few arguments")
                    )
                    | _ -> raise (SyntaxError "Invalid argument syntax")
                    in
                    zip_args (cdr formals) (cdr params) func_env
            in
            let _ = zip_args formals args new_env in
            eval new_env body
    )
    | x -> raise (RuntimeError ((show_lisp x) ^ " cannot be applied"))

(*** Builtin functions ***)
let global_env = env_new None

(* Functions that automatically promote from Integer to Float *)
let _make_poly f_name f_int f_float =
    fun x ->
    match x with
    | Integer a -> f_int a
    | Float a -> f_float a
    | _ -> raise (RuntimeError ("Incorrect type of argument to " ^ f_name))

let _make_poly2 f_name f_int f_float =
    fun x -> fun y ->
    match (x, y) with
    | (Integer a, Integer b) -> f_int a b
    | (Float a, Integer b) -> f_float a (Float.of_int b)
    | (Integer a, Float b) -> f_float (Float.of_int a) b
    | (Float a, Float b) -> f_float a b
    | (_, _) -> raise (RuntimeError ("Incorrect type of arguments to " ^ f_name))

let _box_int x =
    Integer x
let _box_float x =
    Float x

let _add args = fold_list args ~init:(Integer 0) ~f:(_make_poly2 "+" (fun x -> fun y -> _box_int(x+y)) (fun x -> fun y -> _box_float(x +. y)))
let _mul args = fold_list args ~init:(Integer 1) ~f:(_make_poly2 "*" (fun x -> fun y -> _box_int(x*y)) (fun x -> fun y -> _box_float(x *. y)))

let _sub args = 
    if (is_null args) then
        raise (RuntimeError "- must receive at least 1 argument")
    else if (length_list args = 1) then
        (_make_poly "-" (fun x -> _box_int(-x)) (fun x -> _box_float (-. x)) (car args))
    else
        fold_list (cdr args) ~init:(car args) ~f:(_make_poly2 "-" (fun x -> fun y -> _box_int(x - y) ) (fun x -> fun y -> _box_float (x -. y) ))

let _div args = 
    if (is_null args) then
        raise (RuntimeError "- must receive at least 1 argument")
    else if (length_list args = 1) then
        (_make_poly2 "/" (fun x -> fun y -> _box_int(x / y) ) (fun x -> fun y -> _box_float(x /. y))) (Integer 1) (car args)
    else
        fold_list (cdr args) ~init:(car args) ~f:(_make_poly2 "/" (fun x -> fun y -> _box_int(x / y) ) (fun x -> fun y -> _box_float(x /. y)))

(* map over a list by pairs *)
let rec _map2 ~f args =
    if (length_list args <= 1) then
        null
    else
        let a = car args in
        let b = car (cdr args) in
        let res = f a b in
        cons res (_map2 ~f (cdr args))

let _and b1 b2 =
    match (b1, b2) with
    | (Boolean true, Boolean true) -> Boolean true
    | _ -> Boolean false

let _lt args =
    if (length_list args <= 1) then
        Boolean true
    else
        let to_bool a b =
            match (a, b) with
            | (Integer a, Integer b) -> Boolean (Poly.(<) a b)
            | (Float a, Integer b) -> Boolean (Poly.(<) a (Float.of_int b))
            | (Integer a, Float b) -> Boolean (Poly.(<) (Float.of_int a) b)
            | (Float a, Float b) -> Boolean (Poly.(<) a b)
            | (_, _) -> raise (RuntimeError ("Incorrect type of arguments to <"))
        in
        let bools = _map2 ~f:to_bool args in
        fold_list bools ~f:_and ~init:(Boolean true)

let _ =
    env_set global_env ~key:"+" ~data:(Object (ref {is_mutable = false; value = Builtin _add}));
    env_set global_env ~key:"-" ~data:(Object (ref {is_mutable = false; value = Builtin _sub}));
    env_set global_env ~key:"*" ~data:(Object (ref {is_mutable = false; value = Builtin _mul}));
    env_set global_env ~key:"/" ~data:(Object (ref {is_mutable = false; value = Builtin _div}));
    env_set global_env ~key:"<" ~data:(Object (ref {is_mutable = false; value = Builtin _lt}))

(* REPL *)
exception EndOfInput

let count_char c str =
    String.count str ~f:(fun x -> if phys_equal x c then true else false)

let _ = 
    let over = ref false in
    while not !over do
        try
            let buf = Buffer.create 16 in
            let loop_over = ref false in
            let _ = while not !loop_over do
                match In_channel.input_line stdin with
                | Some input -> (
                    Buffer.add_string buf input;
                    let lps = count_char '(' (Buffer.contents buf) in
                    let rps = count_char ')' (Buffer.contents buf) in
                    if phys_equal lps rps then
                        loop_over := true
                    else if rps > lps then 
                        raise (SyntaxError "too many right parentheses")
                    )
                | None -> raise EndOfInput
            done in
            match parse (Buffer.contents buf) with
            | Ok res -> (
                (* print (show_lisp_parse res); *)
                let ast = actualize res in
                (* print (show_lisp ast); *)
                try
                    let result = eval global_env ast in
                    print (show_lisp result)
                with
                | RuntimeError msg -> print ("RuntimeError: " ^ msg)
                | SyntaxError msg -> print ("SyntaxError: " ^ msg)
            )
            | Error msg -> print msg;
            ;
        with
        | SyntaxError msg -> print msg
        | EndOfInput -> over := true
    done;

(*

let unbox_boolean x =
    match x with
    | Boolean y -> y
    | _ -> raise (RuntimeError ((show_lisp x) ^ "could not be unboxed as boolean"))

let rec _and args =
    match args with
    | [] -> raise (RuntimeError "and requires at least 2 arguments")
    | [_] -> raise (RuntimeError "and requires at least 2 arguments")
    | Boolean x :: Boolean y :: [] -> x && y
    | Boolean x :: Boolean y :: xs -> if (x && y) then _and (Boolean y :: xs) else false
    | _ -> raise (RuntimeError "and can only be called on booleans")

let rec _or args =
    match args with
    | [] -> raise (RuntimeError "or requires at least 2 arguments")
    | [_] -> raise (RuntimeError "or requires at least 2 arguments")
    | Boolean x :: Boolean y :: [] -> x || y
    | Boolean x :: Boolean y :: xs -> if (x || y) then true else _or (Boolean y :: xs)
    | _ -> raise (RuntimeError "or can only be called on booleans")
    
let _not args =
    match args with
    | [] -> raise (RuntimeError "not requires 1 argument")
    | [Boolean x] -> not x
    | _ -> raise (RuntimeError "and can only be called on booleans")

let rec lt args =
    match args with
    | [] -> raise (RuntimeError "< requires at least 2 arguments")
    | [_] -> raise (RuntimeError "< requires at least 2 arguments")
    | Number x :: Number y :: [] -> Float.(<) x y
    | Number x :: Number y :: xs -> (Float.(<) x y) && lt (Number y :: xs)
    | _ -> raise (RuntimeError "< only supports arguments of type number")

let rec lte args =
    match args with
    | [] -> raise (RuntimeError "<= requires at least 2 arguments")
    | [_] -> raise (RuntimeError "<= requires at least 2 arguments")
    | Number x :: Number y :: [] -> Float.(<=) x y
    | Number x :: Number y :: xs -> (Float.(<=) x y) && lte (Number y :: xs)
    | _ -> raise (RuntimeError "<= only supports arguments of type number")

let rec gt args =
    match args with
    | [] -> raise (RuntimeError "> requires at least 2 arguments")
    | [_] -> raise (RuntimeError "> requires at least 2 arguments")
    | Number x :: Number y :: [] -> Float.(>) x y
    | Number x :: Number y :: xs -> (Float.(>) x y) && gt (Number y :: xs)
    | _ -> raise (RuntimeError "> only supports arguments of type number")

let rec gte args =
    match args with
    | [] -> raise (RuntimeError "> requires at least 2 arguments")
    | [_] -> raise (RuntimeError "> requires at least 2 arguments")
    | Number x :: Number y :: [] -> Float.(>=) x y
    | Number x :: Number y :: xs -> (Float.(>=) x y) && gte (Number y :: xs)
    | _ -> raise (RuntimeError ">= only supports arguments of type number")

let rec eq args =
    match args with
    | [] -> raise (RuntimeError "= requires at least 2 arguments")
    | [_] -> raise (RuntimeError "= requires at least 2 arguments")
    | Number x :: Number y :: [] -> Float.(=) x y
    | Number x :: Number y :: xs -> (Float.(=) x y) && eq (Number y :: xs)
    | Boolean x :: Boolean y :: [] -> Bool.(=) x y
    | Boolean x :: Boolean y :: xs -> (Bool.(=) x y) && eq (Boolean y :: xs)
    | String x :: String y :: [] -> String.(=) x y
    | String x :: String y :: xs -> (String.(=) x y) && eq (String y :: xs)
    | _ -> raise (RuntimeError "= only supports arguments of the same type")

let rec equal args =
    match args with
    | [] -> raise (RuntimeError "equal? requires at least 2 arguments")
    | [_] -> raise (RuntimeError "equal? requires at least 2 arguments")
    | Boolean x :: Boolean y :: [] -> Bool.(=) x y
    | Symbol x :: Symbol y :: [] -> String.(=) x y
    | Number x :: Number y :: [] -> Float.(=) x y
    | List [] :: List [] :: [] -> true
    | String x :: String y :: [] -> String.(=) x y
    | Pair x :: Pair y :: [] -> List.equal (fun a -> fun b -> equal [a; b] ) x y
    | List x :: List y :: [] -> List.equal (fun a -> fun b -> equal [a; b] ) x y
    | _ -> false

let unbox_atom x =
    match x with
    | Atom x -> x
    | _ -> raise (RuntimeError ("Error unboxing " ^ (show_lisp x)))

(* definition should be a two-element list of [identifier; expression] *)
let define_var env var definition =
    env_set env ~key:var ~data:definition

let map l f =
    match l with
    | List x -> List (List.map x ~f:f)
    | _ -> raise (RuntimeError "Cannot map non-list types")

let show args =
    List.iter args ~f:(fun x -> print (show_lisp x))

let cons args =
    match args with
    | x :: List y :: [] -> List (x :: y)
    | x :: y :: [] -> Pair (x :: y :: [])
    | _ -> raise (RuntimeError "cons requires exactly 2 arguments")

let car args =
    match args with
    | [List (hd :: _)] -> hd
    | [Pair (hd :: _)] -> hd
    | _ -> raise (RuntimeError "car requires exactly 1 argument")

let cdr (args: lisp list) =
    match args with
    | [List (_ :: tl)] -> List tl
    | [Pair (_ :: tl :: [])] -> tl
    | [List []] -> raise (RuntimeError "Illegal datum")
    | _ -> raise (RuntimeError "cdr requires exactly 1 argument")

let is_number args =
    match args with
    | [] -> raise (RuntimeError "number? requires exactly 1 argument")
    | [Number _] -> true
    | _ -> false

let is_boolean args =
    match args with
    | [] -> raise (RuntimeError "boolean? requires exactly 1 argument")
    | [Boolean _] -> true
    | _ -> false

let is_string args =
    match args with
    | [] -> raise (RuntimeError "string? requires exactly 1 argument")
    | [String _] -> true
    | _ -> false

let is_symbol args =
    match args with
    | [] -> raise (RuntimeError "symbol? requires exactly 1 argument")
    | [Symbol _] -> true
    | _ -> false

let is_pair args =
    match args with
    | [] -> raise (RuntimeError "pair? requires exactly 1 argument")
    | [Pair _] -> true
    | [List _] -> true
    | _ -> false

let is_null args =
    match args with
    | [] -> raise (RuntimeError "null? requires exactly 1 argument")
    | [List []] -> true
    | _ -> false

let is_list args =
    match args with
    | [] -> raise (RuntimeError "list? requires exactly 1 argument")
    | [List _] -> true
    | _ -> false

let is_proc args =
    match args with
    | [] -> raise (RuntimeError "list? requires exactly 1 argument")
    | Lambda (_, _) :: _ -> true
    | _ -> false

let rec apply (env: environment) (fn: lisp) (args: lisp list) =
    let _ = env in
    match fn with
    (* builtins (forces arguments to be evaluated) *)
    | Atom "+" -> Number (sum args)
    | Atom "*" -> Number (prod args)
    | Atom "/" -> Number (div args)
    | Atom "-" -> Number (sub args)
    | Atom "<" -> Boolean (lt args)
    | Atom ">" -> Boolean (gt args)
    | Atom "<=" -> Boolean (lte args)
    | Atom ">=" -> Boolean (gte args)
    | Atom "=" -> Boolean (eq args)
    | Atom "and" -> Boolean (_and args)
    | Atom "or" -> Boolean (_or args)
    | Atom "not" -> Boolean (_not args)
    | Atom "show" -> show args; nil
    | Atom "cons" -> cons args
    | Atom "car" -> car args
    | Atom "cdr" -> cdr args
    | Atom "equal?" -> Boolean (equal args)
    | Atom "number?" -> Boolean (is_number args)
    | Atom "boolean?" -> Boolean (is_boolean args)
    | Atom "string?" -> Boolean (is_string args)
    | Atom "symbol?" -> Boolean (is_symbol args)
    | Atom "pair?" -> Boolean (is_pair args)
    | Atom "null?" -> Boolean (is_null args)
    | Atom "list?" -> Boolean (is_list args)
    | Atom "procedure?" -> Boolean (is_proc args)
    | Atom "apply" -> (match args with
                        | x :: xs -> apply env x xs
                        | [] -> raise (RuntimeError "invalid apply")
    )
    | Lambda (List (Atom "lambda" :: List formals :: List definition :: []), closure) -> (
        (* applies a lambda by defining each formal parameter as its corresponding arguments in a new child environment
            and then evaluating it like normal *)
        if (not (phys_equal (List.count formals) (List.count args))) then
            let zipped = List.zip_exn (List.map formals ~f:unbox_atom) args in
            let e = env_new (Some closure) in
            let _ = List.iter zipped ~f:(fun (a, b) -> env_set e ~key:a ~data:b) in
            eval e (List definition)
        else
            raise (RuntimeError "incorrect number of arguments")
    )
    | _ -> raise (RuntimeError (show_lisp fn ^ "cannot be applied to " ^ String.concat (List.map args ~f:show_lisp)))

and eval env ast =
    match ast with
    (* primitives (self-evaluating) *)
    | List [] -> List []
    | Number x -> Number x
    | String x -> String x
    | Boolean x -> Boolean x
    | Symbol x -> Symbol x
    | Pair x -> Pair x
    (* special forms *)
    | Quote (Atom x) -> Symbol (String.lowercase x)
    | Quote x -> x
    | List (Atom "quote" :: List xs :: []) -> List xs
    | List (Atom "quote" :: Number xs :: []) -> Number xs
    | List (Atom "quote" :: String xs :: []) -> String xs
    | List (Atom "quote" :: Boolean xs :: []) -> Boolean xs
    | List (Atom "quote" :: _) -> raise (RuntimeError "incorrect usage of quote")
    | List (Atom "if" :: cond :: _then :: _else :: []) -> if (unbox_boolean (eval env cond)) then eval env _then else eval env _else
    | List (Atom "if" :: _) -> raise (RuntimeError "incorrect usage of if")
    | List (Atom "cond" :: List (Atom "else" :: y :: []) :: _) -> eval env y
    | List (Atom "cond" :: List (x :: y :: []) :: xs) -> if unbox_boolean (eval env x) then eval env y else eval env (List (Atom "cond" :: xs))
    | List (Atom "lambda" :: _) as x -> Lambda (x, ref env) (* special Lambda variant to hold both lambda and closure *)
    | Lambda (_, _) as x -> x
    | List (Atom "begin" :: exprs) ->
            (* evaluates all of the expressions and returns the result of the last one *)
            let result = ref nil in
            let _ = List.iter exprs ~f:(fun x -> result := eval env x) in
            !result
    | List (Atom "define" :: Atom var :: body) when (List.length body) > 0 ->
            (* (define var ...exprs) is reduced to (define var (begin ...exprs)) *)
            define_var env var (eval env (List (Atom "begin" :: body))); nil
    | List (Atom "define" :: List formals :: body) -> (
            match formals with
            | [] -> raise (RuntimeError "incorrect usage of define")
            (* (define (f a b c) <body>) is reduced to (define f (lambda (a b c) <body>)) *)
            | Atom var :: args -> define_var env var (eval env (List (Atom "lambda" :: List args :: List (Atom "begin" :: body) :: []))); nil
            | _ -> raise (RuntimeError "incorrect usage of define")
    )
    | List (Atom "define" :: _) -> raise (RuntimeError "incorrect usage of define")
    (* eval/apply *)
    | List (hd::tl) -> apply env (eval env hd) (List.map tl ~f:(eval env))
    | Atom x -> env_lookup env x


let _ =
    let debug = true in
    let global = env_new None in
    (* builtin functions *)
    let _ = env_set global ~key:"+" ~data:(Atom "+") in
    let _ = env_set global ~key:"-" ~data:(Atom "-") in
    let _ = env_set global ~key:"*" ~data:(Atom "*") in
    let _ = env_set global ~key:"/" ~data:(Atom "/") in
    let _ = env_set global ~key:"<" ~data:(Atom "<") in
    let _ = env_set global ~key:">" ~data:(Atom ">") in
    let _ = env_set global ~key:"<" ~data:(Atom "<=") in
    let _ = env_set global ~key:">=" ~data:(Atom ">=") in
    let _ = env_set global ~key:"=" ~data:(Atom "=") in
    let _ = env_set global ~key:"and" ~data:(Atom "and") in
    let _ = env_set global ~key:"or" ~data:(Atom "or") in
    let _ = env_set global ~key:"not" ~data:(Atom "not") in
    let _ = env_set global ~key:"show" ~data:(Atom "show") in
    let _ = env_set global ~key:"cons" ~data:(Atom "cons") in
    let _ = env_set global ~key:"car" ~data:(Atom "car") in
    let _ = env_set global ~key:"cdr" ~data:(Atom "cdr") in
    let _ = env_set global ~key:"equal?" ~data:(Atom "equal?") in
    let _ = env_set global ~key:"number?" ~data:(Atom "number?") in
    let _ = env_set global ~key:"boolean?" ~data:(Atom "boolean?") in
    let _ = env_set global ~key:"string?" ~data:(Atom "string?") in
    let _ = env_set global ~key:"symbol?" ~data:(Atom "symbol?") in
    let _ = env_set global ~key:"pair?" ~data:(Atom "pair?") in
    let _ = env_set global ~key:"null?" ~data:(Atom "null?") in
    let _ = env_set global ~key:"list?" ~data:(Atom "list?") in
    let _ = env_set global ~key:"procedure?" ~data:(Atom "procedure?") in
    let _ = env_set global ~key:"apply" ~data:(Atom "apply") in
    let over = ref false in
    while not !over do
        try
            let buf = Buffer.create 16 in
            let loop_over = ref false in
            let _ = while not !loop_over do
                match In_channel.input_line stdin with
                | Some input -> (
                    Buffer.add_string buf input;
                    let lps = count_char '(' (Buffer.contents buf) in
                    let rps = count_char ')' (Buffer.contents buf) in
                    if phys_equal lps rps then
                        loop_over := true
                    else if rps > lps then 
                        raise (SyntaxError "too many right parentheses")
                    )
                | None -> raise EndOfInput
            done in
            (* if debug then print (Buffer.contents buf); *)
            let res = match parse (Buffer.contents buf) with
                | Ok x -> if debug then print (show_lisp x); eval global x
                | Error msg -> String msg
            in
            print (" -> " ^ show_lisp res ^ "\n");
        with
        | RuntimeError msg -> print msg
        | UndefinedIdentifier msg -> print msg
        | SyntaxError msg -> print msg
        | EndOfInput -> over := true
    done;
    print "Goodbye!" *)
