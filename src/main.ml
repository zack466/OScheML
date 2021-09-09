open Base
open Stdio

(*
    OScheML - a R5RS-inspired Scheme written in a single file of OCaml
*)

(* 
   ARCHITECTURE:
       input -> parse -> actualize -> eval

       A string input is parsed into a parse tree (a bit more useful than tokenization),
       which is then converted to a full abstract syntax tree (AST), which can then be
       interpreted with a recursive tree-walk (eval/apply).
 *)

(*
    REFERENCES:
        - Revised^5 Report on the Algorithmic Language Scheme
        - Revised^7 Report on the Algorithmic Language Scheme
        - Structure and Interpretation of Computer Programs
        - Crafting Interpreters
        - random blog posts on the internet about Lisp/Scheme
*)

(** Utility functions **)
let print str =
    Out_channel.output_string stdout str;
    Out_channel.output_string stdout "\n";
    Out_channel.flush stdout;

(*** PARSING ***)
type lisp_parse =
    | Atom of string
    | IntegerLiteral of int
    | FloatLiteral of float
    | BooleanLiteral of bool
    | StringLiteral of string
    | CharLiteral of char
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

    let _char = string "#\\" *>
    ((string "space" >>| fun _ -> CharLiteral ' ')
    <|> (string "newline" >>| fun _ -> CharLiteral '\n')
    <|> (take 1 >>| fun x -> CharLiteral (String.get x 0)))
    in

    let string =
        char '"' *> take_while1 (function '"' -> false | _ -> true) <* char '"' <?> "string literal"
        >>| fun x -> StringLiteral x in
    
    let boolean_true =
        Angstrom.string "#t" <?> "boolean literal"
        >>| fun _ -> BooleanLiteral true in

    let boolean_false =
        Angstrom.string "#f" <?> "boolean literal"
        >>| fun _ -> BooleanLiteral false in

    let atom = take_while1 (function
        | 'a' .. 'z' | '!' | '$' | '%' | '&'
        | '*' | '+' | '-' | '.' | '/' | ':' | '<'
        | '=' | '>' | '?' | '@' | '^' | '_' | '~'
    -> true | _ -> false) <?> "atom"
        >>| fun x -> Atom x in

    let comment = option () (char ';'
    >>= fun x-> 
        match x with
        | ';' -> skip_while (function '\n' -> false | _ -> true) <* char '\n'
        | _ -> return ()
    )
    in

    let ws = (skip_while (function
        | '\x20' | '\x0a' | '\x0d' | '\x09' -> true
      | _ -> false)) in

    let lisp = fix (fun lisp ->
        let ele = (choice [num; _char; string; boolean_true; boolean_false; atom]) <* ws <* comment in
        let list = ws *> lp *> many (ws *> lisp <* ws) <* rp <* ws >>| fun x -> List x in
        (both (option '\x00' quote) (list <* comment <|> ele)
        >>| fun res -> match res with
        | ('\'', x) -> Quote x
        | (_, x) -> x)
    ) in

    fun input -> (
        (* remove line comments *)
        let lines = Str.split (Str.regexp "\n") input in
        let filtered = List.filter lines
            ~f:(fun x ->
                (String.length x > 0) && not (Char.(=) ';' (String.get x 0))
            ) in
        (* recombine lines *)
        let str = (String.concat ~sep:"\n" filtered) ^ "\n" in

        (* call parser on filtered input *)
        parse_string ~consume:All (many lisp) str
    )

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

    | String of string

    (* a compound procedure, which holds both a closure and the procedure itself *)
    | Lambda of environment * lisp

    (* a builtin procedure, which is represented as an OCaml function that operates on ASTs *)
    | Builtin of (environment -> lisp -> lisp)

and pair = Nil | CC of lisp * lisp

and environment = {
    parent: environment ref option;
    table: (string, lisp) Hashtbl.t
}

exception SyntaxError of string

let _null = { is_mutable = false; value = Pair Nil }
let null = Object (ref _null)

(*
 * Converts a parse tree into a full AST
 * Is mostly trivial, except that certain literals must be turned into reference objects
 *)
let rec actualize (parse_tree: lisp_parse): lisp =
    match parse_tree with
    | Atom x -> Symbol x
    | IntegerLiteral x -> Integer x
    | FloatLiteral x -> Float x
    | BooleanLiteral x -> Boolean x
    | CharLiteral x -> Char x

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

(* for debugging *)
let rec show_lisp (ast: lisp) =
    match ast with
    | list when is_proper_list list -> "(" ^ String.concat ~sep:" " (List.map (to_list list) ~f:show_lisp) ^ ")"
    | Object { contents = {is_mutable = _; value = y}} -> show_reference_value y

    | Integer x -> Int.to_string x
    | Float x -> Float.to_string x
    | Boolean x -> if x then "#t" else "#f"
    | Symbol x -> x
    | Char x -> "#\\" ^ (
        match x with
        | '\n' -> "newline"
        | ' ' -> "space"
        | _ -> Char.to_string x)
    | Quote x -> "'" ^ (show_lisp x)

and show_reference_value rv =
    match rv with
    | Lambda (_, body) -> "Compound procedure: " ^ (show_lisp body)
    | Builtin _ -> "Builtin procedure"
    | Pair Nil -> "()"
    | Pair (CC (a, b)) -> "(" ^ (show_lisp a) ^ " . " ^ (show_lisp b) ^ ")"
    | String x -> "\"" ^ x ^ "\""

(* Eval / Apply *)
exception RuntimeError of string

let rec env_lookup (env: environment) = function
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

let is_undefined (env: environment) = function
    | Symbol name -> (
        try
            match env_lookup env (Symbol name) with
            | _ -> false
        with
        | RuntimeError _ -> true
    )
    | _ -> raise (RuntimeError "cannot lookup a non-symbol")

let car = function
    | (Object { contents = {is_mutable = _; value = Pair p} }) -> (
        match p with
        | Nil -> raise (RuntimeError "cannot take car of an empty list")
        | (CC (hd, _)) -> hd
    )
    | _ -> raise (RuntimeError "cannot take the car of this object")

let cdr = function
    | (Object { contents = {is_mutable = _; value = Pair p} }) -> (
        match p with
        | Nil -> raise (RuntimeError "cannot take cdr of an empty list")
        | (CC (_, tl)) -> tl
    )
    | _ -> raise (RuntimeError "cannot take the cdr of this object")

let cadr = Fn.compose car cdr
let cddr = Fn.compose cdr cdr

let is_null = function
    | Object { contents = {is_mutable = _; value = Pair Nil } } -> true
    | _ -> false

let is_symbol = function
    | Symbol _ -> true
    | _ -> false

let is_pair = function
    | Object { contents = { is_mutable = _; value = Pair _ } } -> true
    | _ -> false

let is_char = function
    | Char _ -> true
    | _ -> false

let is_string = function
    | Object { contents = { is_mutable = _; value = String _}} -> true
    | _ -> false

let is_procedure = function
    | Object { contents = { is_mutable = _; value = Lambda _}} -> true
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

let rec iter_list ~f list: unit =
    match list with
    | Object { contents = { is_mutable = _; value = Pair Nil } } -> ()
    | Object { contents = { is_mutable = _; value = Pair (CC (hd, tl)) } } -> (
        f hd;
        iter_list ~f:f tl;
    )
    | _ -> raise (RuntimeError "Cannot call iter on non-lists")

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

    | Object { contents = { is_mutable = _; value = Pair (CC (Symbol "set!", args)) } }
        when is_undefined env (Symbol "set!") -> 
            (
                if not (phys_equal 2 (length_list args)) then
                    raise (RuntimeError ("set! expects exactly two arguments"))
                else (
                    let var = car args in
                    let expr = cadr args in
                    let _ = match var with
                    | Symbol name -> (
                        if is_undefined env (Symbol name) then
                            raise (RuntimeError (name ^ " is unbound"))
                        else
                            env_set env ~key:name ~data:expr
                    )
                    | _ -> raise (RuntimeError ("Cannot assign to " ^ (show_lisp var)))
                    in null
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
                        let proc = Object (ref { is_mutable = false; value = Lambda (env, cons args (cdr rest)) }) in
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
    | Object { contents = { is_mutable = _; value = Builtin f} } -> f env args
    | Object { contents = { is_mutable = _; value = Lambda (closure, lambda)} } -> (
        let formals = car lambda in
        let body = cons (Symbol "begin") (cdr lambda) in
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
    | (_, _) -> print (show_lisp x); print (show_lisp y); raise (RuntimeError ("Incorrect type of arguments to " ^ f_name))

let _box_int x =
    Integer x
let _box_float x =
    Float x

let _add _ args = fold_list args ~init:(Integer 0) ~f:(_make_poly2 "+" (fun x -> fun y -> _box_int(x+y)) (fun x -> fun y -> _box_float(x +. y)))
let _mul _ args = fold_list args ~init:(Integer 1) ~f:(_make_poly2 "*" (fun x -> fun y -> _box_int(x*y)) (fun x -> fun y -> _box_float(x *. y)))

let _sub _ args = 
    if (is_null args) then
        raise (RuntimeError "- must receive at least 1 argument")
    else if (length_list args = 1) then
        (_make_poly "-" (fun x -> _box_int(-x)) (fun x -> _box_float (-. x)) (car args))
    else
        fold_list (cdr args) ~init:(car args) ~f:(_make_poly2 "-" (fun x -> fun y -> _box_int(x - y) ) (fun x -> fun y -> _box_float (x -. y) ))

let _div _ args = 
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

let _not _ args =
    if not (phys_equal 1 (length_list args)) then
        raise (RuntimeError "not expects exactly one argument")
    else
        match (car args) with
        | Boolean x -> Boolean (not x)
        | _ -> raise (RuntimeError "argument to 'not' is not the correct type")


let _lt _ args =
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

let _gt _ args =
    if (length_list args <= 1) then
        Boolean true
    else
        let to_bool a b =
            match (a, b) with
            | (Integer a, Integer b) -> Boolean (Poly.(>) a b)
            | (Float a, Integer b) -> Boolean (Poly.(>) a (Float.of_int b))
            | (Integer a, Float b) -> Boolean (Poly.(>) (Float.of_int a) b)
            | (Float a, Float b) -> Boolean (Poly.(>) a b)
            | (_, _) -> raise (RuntimeError ("Incorrect type of arguments to >"))
        in
        let bools = _map2 ~f:to_bool args in
        fold_list bools ~f:_and ~init:(Boolean true)

let _lte x args = _not x (cons (_gt x args) null)
let _gte x args = _not x (cons (_lt x args) null)

let is_eqv args: bool =
    if not (phys_equal (length_list args) 2) then
        raise (RuntimeError "eqv? requires exactly two arguments")
    else
        match (car args, car (cdr args)) with
        | (Boolean x, Boolean y) -> Bool.(=) x y
        | (Symbol x, Symbol y) -> String.(=) x y
        | (Integer x, Integer y) -> Int.(=) x y
        | (Float x, Float y) -> Float.(=) x y
        | (Char x, Char y) -> Char.(=) x y
        | (Object { contents = p }, Object { contents = q }) -> phys_equal p q
        | (_, _) -> false

(* for now, language makes no distinction between eqv? and eq? *)
let is_eq = is_eqv

let rec is_equal args: bool =
    if not (phys_equal (length_list args) 2) then
        raise (RuntimeError "equal? requires exactly two arguments")
    else
        match (car args, car (cdr args)) with
        | (Boolean x, Boolean y) -> Bool.(=) x y
        | (Symbol x, Symbol y) -> String.(=) x y
        | (Integer x, Integer y) -> Int.(=) x y
        | (Float x, Float y) -> Float.(=) x y
        | (Char x, Char y) -> Char.(=) x y
        | (Object { contents = p }, Object { contents = q }) -> (
            if phys_equal p q then
                true
            else
                (* check if objects are equal recursively *)
                match (p, q) with
                | (
                    {is_mutable = _; value = Pair (CC (hd, tl))},
                    {is_mutable = _; value = Pair ( CC (hd1, tl1))}
                    ) -> (
                        let eq1 = is_equal (cons hd (cons hd1 null)) in
                        let eq2 = is_equal (cons tl (cons tl1 null)) in
                        eq1 && eq2
                        )
                | (
                    {is_mutable = _; value = String x},
                    {is_mutable = _; value = String y}
                    ) -> String.(=) x y
                | ( (* lambda with the exact same formals and body are considered equal by value (as if they were lists) *)
                    {is_mutable = _; value = Lambda (_, body1)},
                    {is_mutable = _; value = Lambda (_, body2)}
                    ) -> is_equal (cons body1 (cons body2 null))
                | _ -> false
        )
        | (_, _) -> false

let _car _ args =
    if not (phys_equal 1 (length_list args)) then
        raise (RuntimeError "car expects exactly one argument")
    else
        car (car args)

let _cdr _ args =
    if not (phys_equal 1 (length_list args)) then
        raise (RuntimeError "cdr expects exactly one argument")
    else
        cdr (car args)

let _cons _ args = 
    if not (phys_equal 2 (length_list args)) then
        raise (RuntimeError "cons expects exactly two argument")
    else
        cons (car args) (cadr args)

let _predicate name f _ args =
    if not (phys_equal 1 (length_list args)) then
        raise (RuntimeError (name ^ " expects exactly one argument"))
    else
        Boolean (f (car args))

let _display _ args =
    let _ = if is_proper_list args then
        iter_list ~f:(Fn.compose print show_lisp) args
    else
        print (show_lisp args);
    in 
    null

(* (apply f a ... z) evaluates to (f args) where args = (append (a ... ) z)
 * a, ... are individual elements and z is a list
 *)
let _apply env args =
    if (length_list args) = 0 then
        raise (RuntimeError ("apply expects at least one argument"))
    else
        let rec collect list =
            if is_null list then
                null
            else if is_null (cdr list) then
                car list
            else
                cons (car list) (collect (cdr list))
        in
        apply env (car args) (collect (cdr args))

let _ =
    env_set global_env ~key:"+" ~data:(Object (ref {is_mutable = false; value = Builtin _add}));
    env_set global_env ~key:"-" ~data:(Object (ref {is_mutable = false; value = Builtin _sub}));
    env_set global_env ~key:"*" ~data:(Object (ref {is_mutable = false; value = Builtin _mul}));
    env_set global_env ~key:"/" ~data:(Object (ref {is_mutable = false; value = Builtin _div}));
    env_set global_env ~key:"<" ~data:(Object (ref {is_mutable = false; value = Builtin _lt}));
    env_set global_env ~key:">" ~data:(Object (ref {is_mutable = false; value = Builtin _gt}));
    env_set global_env ~key:"<=" ~data:(Object (ref {is_mutable = false; value = Builtin _lte}));
    env_set global_env ~key:">=" ~data:(Object (ref {is_mutable = false; value = Builtin _gte}));
    env_set global_env ~key:"eqv?" ~data:(Object (ref {is_mutable = false; value = Builtin (fun _ -> fun x -> Boolean (is_eqv x))}));
    env_set global_env ~key:"eq?" ~data:(Object (ref {is_mutable = false; value = Builtin (fun _ -> fun x -> Boolean (is_eq x))}));
    env_set global_env ~key:"equal?" ~data:(Object (ref {is_mutable = false; value = Builtin (fun _ -> fun x -> Boolean (is_equal x))}));
    env_set global_env ~key:"car" ~data:(Object (ref {is_mutable = false; value = Builtin _car}));
    env_set global_env ~key:"cdr" ~data:(Object (ref {is_mutable = false; value = Builtin _cdr}));
    env_set global_env ~key:"cons" ~data:(Object (ref {is_mutable = false; value = Builtin _cons}));
    env_set global_env ~key:"apply" ~data:(Object (ref {is_mutable = false; value = Builtin _apply}));
    env_set global_env ~key:"not" ~data:(Object (ref {is_mutable = false; value = Builtin _not}));
    env_set global_env ~key:"display" ~data:(Object (ref {is_mutable = false; value = Builtin _display}));
    env_set global_env ~key:"list?" ~data:(Object (ref {is_mutable = false; value = Builtin (_predicate "list?" is_proper_list)}));
    env_set global_env ~key:"string?" ~data:(Object (ref {is_mutable = false; value = Builtin (_predicate "string?" is_string)}));
    env_set global_env ~key:"pair?" ~data:(Object (ref {is_mutable = false; value = Builtin (_predicate "pair?" is_pair)}));
    env_set global_env ~key:"char?" ~data:(Object (ref {is_mutable = false; value = Builtin (_predicate "char?" is_char)}));
    env_set global_env ~key:"procedure?" ~data:(Object (ref {is_mutable = false; value = Builtin (_predicate "procedure?" is_procedure)}));

(* REPL *)
exception EndOfInput

let count_char c str =
    String.count str ~f:(fun x -> if phys_equal x c then true else false)

let repl () = 
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
                let asts = List.map ~f:actualize res in
                (* print (show_lisp ast); *)
                let interpret ast = 
                    try
                        let result = eval global_env ast in
                        print (show_lisp result)
                    with
                    | RuntimeError msg -> print ("RuntimeError: " ^ msg)
                    | SyntaxError msg -> print ("SyntaxError: " ^ msg)
                in
                List.iter ~f:interpret asts
            )
            | Error msg -> print msg;
            ;
        with
        | SyntaxError msg -> print msg
        | EndOfInput -> over := true
    done;
    ()

let runfile file =
    let ic = In_channel.create file in
    let str = In_channel.input_all ic in
    let _ = match parse str with
    | Ok res -> (
        (* List.iter ~f:(fun x -> print (show_lisp_parse x)) res; *)
        let asts = List.map ~f:actualize res in
        (* print (show_lisp ast); *)
        let interpret ast = 
            try
                let result = eval global_env ast in
                print (show_lisp result)
            with
            | RuntimeError msg -> print ("RuntimeError: " ^ msg)
            | SyntaxError msg -> print ("SyntaxError: " ^ msg)
        in
        List.iter ~f:interpret asts
    )
    | Error msg -> print msg;
    in
    ()

let _ =
    let usage_msg = "oscheme [-i] [file] [file2] ..." in
    let input_files = ref [] in
    let interactive = ref false in
    let anon_fun filename =
        input_files := filename :: !input_files in
    let speclist = [
        ("-i", Caml.Arg.Set interactive, "Run input files, then open into a repl")
    ] in
    let () = Caml.Arg.parse speclist anon_fun usage_msg;

    match !input_files with
    | [] -> repl ();
    | [filename] -> (
        runfile filename;
        if !interactive then
            repl ();
    )
    | list -> (
        List.iter ~f:runfile list;
        if !interactive then
            repl ();
    )
    in
    ()
