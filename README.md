# OScheML - a R5RS-inspired Scheme written in a single file of OCaml

## FEATURES:
- Datatypes:
    - Integer (fixed width)
    - Float (IEEE-754 double precision)
    - Boolean (#t and #f)
    - Character
    - String
    - Symbol
- Quoting
- Lambda

## BUILTINS:
- Arithmetic (auto-promoting): +, -, \*, /, <, <=, >, >=
- Logic: if, not, and & or (with short-circuiting)
- Lists: cons, car, cdr, list?, pair?
- Equality: eq?, eqv? equal?
- Predicates: pair?, list?, string?, char?, procedure?, number?, boolean?
- Other: lambda, begin, set!, define, apply, display

## USAGE:
- run `dune exec ./src/main.exe` to enter a REPL
- to run a script, add file path as an argument
   - ex: `dune exec ./src/main.exe examples/sqrt.scm`

## ARCHITECTURE:
- input -> parse -> actualize -> eval

A string input is parsed into a parse tree (a bit more useful than tokenization),
which is then converted to a full abstract syntax tree (AST),
which can then be interpreted with a recursive tree-walk (eval/apply).

## REFERENCES:
- Revised^5 Report on the Algorithmic Language Scheme
- Revised^7 Report on the Algorithmic Language Scheme
- Structure and Interpretation of Computer Programs
- Crafting Interpreters
- random blog posts on the internet about Lisp/Scheme
