(* parse tree *)
type t =
    | Atom of string
    | IntegerLiteral of int
    | FloatLiteral of float
    | BooleanLiteral of bool
    | StringLiteral of string
    | Quote of t
    | List of t list
[@@deriving show]

(* Returns a parse tree for a given input *)
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
