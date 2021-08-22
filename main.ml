open Base
open Stdio

module Hashtbl_printable = struct
  type ('k,'s) t = ('k, 's) Hashtbl.t

  let pp pp_key pp_value ppf  values =
      (* get rid of 'unused values' warning *)
      let _ = pp_key in
      let _ = pp_value in
      let _ = ppf in
      let _ = values in
      () (* not actually printing anything bc results in stack overflow *)
end

let print str =
    Out_channel.output_string stdout str;
    Out_channel.output_string stdout "\n";
    Out_channel.flush stdout;

type lisp = 
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
[@@deriving show]

let nil = List []

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
        try return (Number (Float.of_string s))
        with _ -> fail "invalid number literal" in

    let string =
        char '"' *> take_while1 (function '"' -> false | _ -> true) <* char '"' <?> "string literal"
        >>| fun x -> String x in
    
    let boolean_true =
        Angstrom.string "#t" <?> "boolean literal"
        >>| fun _ -> Boolean true in

    let boolean_false =
        Angstrom.string "#f" <?> "boolean literal"
        >>| fun _ -> Boolean false in

    let atom = take_while1 (function ' ' | '(' | ')' | '\'' | '"' -> false | _ -> true) <?> "atom"
        >>| fun x -> Atom x in

    let ws = skip_while (function
      | '\x20' | '\x0a' | '\x0d' | '\x09' -> true
      | _ -> false) in

    (* this function has broken my soul *)
    let lisp = fix (fun lisp ->
        let ele = choice [num; string; boolean_true; boolean_false; atom] in
        let list = lp *> many (ws *> lisp <* ws) <* rp >>| fun x -> List x in
        (both (option '\x00' quote) (list <|> ele)
        >>| fun res -> match res with
        | ('\'', x) -> Quote x
        | (_, x) -> x)
    ) in

    parse_string ~consume:All lisp

exception UndefinedIdentifier of string
exception SyntaxError of string

let count_char c str =
    String.count str ~f:(fun x -> if phys_equal x c then true else false)

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

exception EndOfInput

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
    print "Goodbye!"
