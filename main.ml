open Base
open Angstrom

type lisp = 
    | Atom of string
    | Int of int
    | String of string
    | List of lisp list
[@@deriving show]

let parse = 
    let open Angstrom in

    let lp = char '(' in
    let rp = char ')' in

    let int = 
        take_while1 (function '0' .. '9' -> true | _ -> false)
        >>| Int.of_string
        >>| fun x -> Int x in

    let string =
        char '"' *> take_while1 (function '"' -> false | _ -> true) <* char '"'
        >>| fun x -> String x in

    let atom = take_while1 (function ' ' | '(' | ')' -> false | _ -> true)
        >>| fun x -> Atom x in

    let ws = skip_while (function
      | '\x20' | '\x0a' | '\x0d' | '\x09' -> true
      | _ -> false) in

    let lisp = fix (fun lisp ->
        let inside = many (ws *> choice [int; string; atom; lisp] <* ws) in
        lp *> inside <* rp
        >>| fun x -> List x) in
    
    parse_string ~consume:All lisp

let env = Hashtbl.create(module String)

let _ =
    let x = `Int 3 in
    Hashtbl.set env ~key:"asdf" ~data:x

let rec eval ast env =
    match ast with
        | List [] -> `Nil
        | List (hd::tl) -> apply (eval hd) tl env
        | Atom x -> lookup x env
        | Int x -> `Int x
        | String x -> `String x

let _ = Caml.print_endline "Hello, World!";
