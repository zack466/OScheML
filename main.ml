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
        - Revised^7 Report on the Algorithmic Language Scheme
        - Structure and Interpretation of Computer Programs
        - Crafting Interpreters
        - random blog posts on the internet on the implementation of Lisps
*)

module Hashtbl_printable = struct
  type ('k,'s) t = ('k, 's) Hashtbl.t

  let pp pp_key pp_value ppf  values =
      (* get rid of 'unused values' warning *)
      let _ = pp_key in
      let _ = pp_value in
      let _ = ppf in
      let _ = values in
      () (* not actually printing anything bc might result in stack overflow *)
end

let print str =
    Out_channel.output_string stdout str;
    Out_channel.output_string stdout "\n";
    Out_channel.flush stdout;

(* Syntactic sugar is run on this parse tree *)
type lisp_parse =
    | Atom of string
    | IntegerLiteral of int
    | FloatLiteral of float
    | BooleanLiteral of bool
    | StringLiteral of string
    | Quote of lisp_parse
    | List of lisp_parse list
[@@deriving show]

(* The AST for this lisp *)
(* type lisp = 
    | Atom of string
    | Number of float
    | Boolean of bool
    | String of string
    | Quote of lisp
    | Symbol of string
    | List of lisp list
    | Pair of lisp list (* must have only 2 items, unfortunate schism bc list by itself cannot tell the difference between (cons 1 2) and (cons 1 '(2)) *)
    | Lambda of lisp * environment ref (* extra variant just to store closure environment *)
and environment = | Env of environment ref option * (string, lisp) Hashtbl_printable.t
[@@deriving show] *)

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
    | Object of {is_mutable: bool; value: reference_value ref}

    (* Primitives are immutable and reside on the stack (at least, behavior-wise) *)
    | Integer of int
    | Float of float
    | Boolean of bool
    | Symbol of string
    | Char of char
    | Variable of string
    | Quote of lisp

    (* builtin "functions" / special forms *)
    | Builtin of builtin
and builtin =
    (* conditional - (if <test> <consequent> [alternate] )*)
    | If of lisp * lisp * lisp option

    (* set! - (set! <variable> <expression> )*)
    | Set of lisp * lisp
    
    | And of lisp
    | Or of lisp
    | Begin of lisp list

and reference_value =
    (* Homebrewed linked list *)
    | Pair of pair

    (* | Vector of lisp Array.t *)

    (* a string *)
    | String of string

    (* a procedure, which holds both a closure and the procedure itself *)
    (* | Lambda of env * lisp *)

and pair = Nil | CC of lisp * lisp
(* and env = {
    parent: env ref option;
    hashtbl: (string, lisp) Hashtbl_printable.t
} *)

(* let is_exact = function
    | Int _ -> true
    | Float _ -> false
    | _ -> assert false *)

exception SyntaxError of string

let is_syntactic_keyword = function
    | "and" | "or" | "set!"
    | "if" | "lambda" | "begin" -> true
    | _ -> false

let rec actualize (parse_tree: lisp_parse): lisp =
    match parse_tree with
    | Atom x when is_syntactic_keyword x -> raise (SyntaxError ("Syntactic keyword '" ^ x ^ "' cannot be used as an expression"))
    | Atom x -> Variable x
    | IntegerLiteral x -> Integer x
    | FloatLiteral x -> Float x
    | BooleanLiteral x -> Boolean x
    | StringLiteral x -> Object { is_mutable = true; value = ref (String x) }

    (* quoting and symbols *)
    | Quote (StringLiteral x) -> Symbol x
    | Quote x -> Quote (actualize x)
    | List x -> (
        match x with
        (* Empty list *)
        | [] ->
                Object {
                    is_mutable = true;
                    value = ref (Pair Nil);
                }

        (* parsing pairs with dot notation *)
        | hd :: Atom "." :: tl :: [] ->
                Object {
                    is_mutable = true;
                    value = ref (Pair (CC ((actualize hd), (actualize tl))));
                }
        | _ :: Atom "." :: _ ->
                raise (SyntaxError "Incorrect usage of . notation")

        (* Otherwise, a standard list *)
        | hd :: tl ->
                Object {
                    is_mutable = true;
                    value = ref (Pair (CC ((actualize hd), (actualize (List tl)))));
                }

    )

let rec is_proper_list (ls: lisp) =
    match ls with
    | Object {is_mutable = _; value = { contents = (Pair Nil) } } -> true
    | Object {is_mutable = _; value = { contents = (Pair (CC (_, tl))) } } -> is_proper_list tl
    | _ -> false

let rec to_list (ls: lisp) =
    match ls with
    | Object {is_mutable = _; value = { contents = (Pair Nil) } } -> []
    | Object {is_mutable = _; value = { contents = (Pair (CC (hd, tl))) } } -> hd :: to_list tl
    | _ -> assert false

let rec show_lisp (ast: lisp) =
    match ast with
    | list when is_proper_list list -> "(" ^ String.concat ~sep:" " (List.map (to_list list) ~f:show_lisp) ^ ")"
    | Object {is_mutable = _; value = y} -> show_reference_value !y

    (* Primitives are immutable and reside on the stack (at least, behavior-wise) *)
    | Integer x -> Int.to_string x
    | Float x -> Float.to_string x
    | Boolean x -> Bool.to_string x
    | Symbol x -> "'" ^ x
    | Char x -> Char.to_string x
    | Variable x -> x
    | Quote x -> "'" ^ (show_lisp x)

    (* builtin "functions" / special forms *)
    | Builtin _ -> "Builtin function"
and show_reference_value rv =
    match rv with
    | Pair Nil -> "()"
    | Pair (CC (a, b)) -> "(" ^ (show_lisp a) ^ " . " ^ (show_lisp b) ^ ")"
    | String x -> "\"" ^ x ^ "\""

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
                print (show_lisp ast);
            )
            | Error msg -> print msg;
            ;
        with
        | SyntaxError msg -> print msg
        | EndOfInput -> over := true
    done;

(* exception UndefinedIdentifier of string


let env_new parent =
    match parent with
    | Some parent_env -> Env (Some parent_env,  Hashtbl.create(module String))
    | None -> Env (None, Hashtbl.create(module String))

let rec env_lookup env x =
    match env with
    | Env (Some parent, current) -> (
        match Hashtbl.find current x with
        | Some v -> v
        | None -> env_lookup !parent x
    )
    | Env (None, current) -> (
        match Hashtbl.find current x with
        | Some v -> v
        | None -> raise (UndefinedIdentifier ("identifier " ^ x ^ " not found"))
    )

let env_set env ~key ~data =
    match env with
    | Env (_, e) -> Hashtbl.set e ~key:key ~data:data

exception RuntimeError of string

let unbox_number x =
    match x with
    | Number y -> y
    | _ -> raise (RuntimeError ("cannot convert " ^ show_lisp x ^ " to float"))

let sum args =
    match args with
    | [] -> raise (RuntimeError "+ requires at least 1 argument")
    | _ -> List.sum (module Float) args ~f:unbox_number

let prod args =
    match args with
    | [] -> raise (RuntimeError "* requires at least 1 argument")
    | _ -> List.fold ~init:1.0 ~f:( *. ) (List.map args ~f:unbox_number)

let sub args =
    match args with
    | [] -> raise (RuntimeError "- requires at least 1 argument")
    | [hd] -> 0.0 -. unbox_number hd 
    | hd::tl -> unbox_number hd -. sum tl

let div args =
    match args with
    | [] -> raise (RuntimeError "/ requires at least 1 argument")
    | [hd] -> 1.0 /. unbox_number hd 
    | hd::tl -> unbox_number hd /. prod tl

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
