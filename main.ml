open Base
open Stdio

type lisp = 
    | Atom of string
    | Number of float
    | String of string
    | List of lisp list
[@@deriving show]

let nil = List []

let parse = 
    let open Angstrom in

    let lp = char '(' <?> "lparen" in
    let rp = char ')' <?> "rparen" in

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

    let atom = take_while1 (function ' ' | '(' | ')' -> false | _ -> true) <?> "atom"
        >>| fun x -> Atom x in

    let ws = skip_while (function
      | '\x20' | '\x0a' | '\x0d' | '\x09' -> true
      | _ -> false) in

    let lisp = fix (fun lisp ->
        let inside = many (ws *> choice [num; string; atom; lisp] <* ws) in
        lp *> inside <* rp
        >>| fun x -> List x) in
    
    parse_string ~consume:All lisp

let print str =
    Out_channel.output_string stdout str;
    Out_channel.output_string stdout "\n";
    Out_channel.flush stdout;

exception UndefinedIdentifier of string

let lookup env x =
    match Hashtbl.find env x with
    | Some v -> v
    | None -> raise (UndefinedIdentifier x)

exception RuntimeError of string

let unbox_number x =
    match x with
    | Number y -> y
    | _ -> raise (RuntimeError "cannot convert to float")

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

(* (define x <body>) binds the identifier x to <body> in the given environment env *)
let define env args =
    match args with
    | [] -> raise (RuntimeError "define requires at least 2 arguments")
    | [_] -> raise (RuntimeError "define requires at least 2 arguments")
    | hd::tl -> (
        
    )

let apply env fn args =
    match fn with
    | Atom "+" -> Number (sum args)
    | Atom "*" -> Number (prod args)
    | Atom "/" -> Number (div args)
    | Atom "-" -> Number (sub args)
    | Atom "define" -> define env args; nil
    | _ -> raise (RuntimeError (show_lisp fn ^ "cannot be applied to " ^ String.concat (List.map args ~f:show_lisp)))

let map l f =
    match l with
    | List x -> List (List.map x ~f:f)
    | _ -> raise (RuntimeError "Cannot map non-list types")

let rec eval (env: (string, lisp) Hashtbl.t) (ast: lisp) : lisp =
    match ast with
    | List [] -> List []
    | List (hd::tl) -> apply env (eval env hd) (List.map tl ~f:(eval env))
    | Atom x -> lookup env x
    | Number x -> Number x
    | String x -> String x

let count_char c str =
    String.count str ~f:(fun x -> if phys_equal x c then true else false)

let _ =
    let debug = false in
    let global = Hashtbl.create(module String) in
    let _ = Hashtbl.set global ~key:"+" ~data:(Atom "+") in
    let _ = Hashtbl.set global ~key:"-" ~data:(Atom "-") in
    let _ = Hashtbl.set global ~key:"*" ~data:(Atom "*") in
    let _ = Hashtbl.set global ~key:"/" ~data:(Atom "/") in
    while true do
        try
            let buf = Buffer.create 16 in
            let loop_over = ref false in
            let _ = while not !loop_over do
                match In_channel.input_line stdin with
                | Some input -> (
                    Buffer.add_string buf input;
                    if phys_equal (count_char '(' (Buffer.contents buf)) (count_char ')' (Buffer.contents buf))
                    then loop_over := true)
                | None -> loop_over := true
            done in
            if debug then Caml.print_string (Buffer.contents buf);
            let res = match parse (Buffer.contents buf) with
                | Ok x -> if debug then Caml.print_string (show_lisp x); eval global x
                | Error msg -> String msg
            in
            Out_channel.output_string stdout (show_lisp res ^ "\n");
            Out_channel.flush stdout
        with
        | RuntimeError msg -> print msg
    done
