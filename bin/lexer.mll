{
open Core

let symbol_table =
  Hashtbl.of_alist_exn
    (module String)
    [ ":", Parser.COLON
    ; ",", Parser.COMMA
    ; "decl", Parser.DECL
    ; "=", Parser.EQUAL
    ; "fun", Parser.FUN
    ; "in", Parser.IN
    ; "let", Parser.LET
    ; "(", Parser.LPAREN
    ; "->", Parser.MINUSGREATER
    ; ")", Parser.RPAREN
    ; ";", Parser.SEMICOLON
    ; "type", Parser.TYPE
    ]
;;

let update_loc lexbuf file line absolute chars =
  let pos = lexbuf.Lexing.lex_curr_p in
  let new_file =
    match file with
    | None -> pos.pos_fname
    | Some s -> s
  in
  lexbuf.lex_curr_p
    <- { pos with
         pos_fname = new_file
       ; pos_lnum = (if absolute then line else pos.pos_lnum + line)
       ; pos_bol = pos.pos_cnum - chars
       }
;;

exception Lex_error of string * Location.t

let error lexbuf msg = raise (Lex_error (msg, Location.curr lexbuf))

let () =
  Location.register_error_of_exn (function
      | Lex_error (msg, loc) -> Some (Location.errorf ~loc "%s" msg)
      | _ -> None)
;;
}

let newline = ('\013'* '\010')
let blank = [' ' '\009' '\012']
let digit = ['0'-'9']
let lower = ['a'-'z']
let upper = ['A'-'Z']

rule token_exn = parse
  | newline
    { update_loc lexbuf None 1 false 0; token_exn lexbuf }
  | blank+
    { token_exn lexbuf }
  | (lower | upper) (lower | upper | digit | '_' | '\'')* as name
    { match Hashtbl.find symbol_table name with
      | Some kwd ->
          kwd
      | None ->
          Parser.IDENT name }
  | '\'' ((lower | upper) (lower | upper | digit | '_' | '\'')* as name)
    { Parser.TYVAR name }
  | "->"
    { Hashtbl.find_exn symbol_table (Lexing.lexeme lexbuf) }
  | [':' ',' '=' '(' ')' ';']
    { Hashtbl.find_exn symbol_table (Lexing.lexeme lexbuf) }
  | eof
    { Parser.EOF }
  | _ as ch
    { error lexbuf ("illegal character (" ^ Char.escaped ch ^ ")") }
