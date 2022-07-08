{
open Core

let symbol_table =
  Hashtbl.of_alist_exn
    (module String)
    [ "&", Parser.AMPERSAND
    ; "*", Parser.ASTERISK
    ; "|", Parser.BAR
    ; "bool", Parser.BOOL
    ; "case", Parser.CASE
    ; ":", Parser.COLON
    ; ",", Parser.COMMA
    ; "cons", Parser.CONS
    ; ".l", Parser.DOTL
    ; ".r", Parser.DOTR
    ; "else", Parser.ELSE
    ; "=", Parser.EQUAL
    ; "false", Parser.FALSE
    ; "fun", Parser.FUN
    ; "if", Parser.IF
    ; "in", Parser.IN
    ; "inl", Parser.INL
    ; "inr", Parser.INR
    ; "let", Parser.LET
    ; "list", Parser.LIST
    ; "(", Parser.LPAREN
    ; "->", Parser.MINUSGREATER
    ; "-o", Parser.MINUSO
    ; "nil", Parser.NIL
    ; "+", Parser.PLUS
    ; ")", Parser.RPAREN
    ; ";", Parser.SEMICOLON
    ; "#type", Parser.SHOWTYPE
    ; "then", Parser.THEN
    ; "true", Parser.TRUE
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
  | lower (lower | upper | digit | '_' | '\'')* as name
    { match Hashtbl.find symbol_table name with
      | Some kwd ->
          kwd
      | None ->
          Parser.LIDENT name }
  | upper (lower | upper | digit | '_' | '\'')* as name
    { Parser.UIDENT name }
  | ".l" | ".r" | "->" | "-o" | "#type"
    { Hashtbl.find_exn symbol_table (Lexing.lexeme lexbuf) }
  | ['&' '*' '|' ':' ',' '=' '(' '+' ')' ';']
    { Hashtbl.find_exn symbol_table (Lexing.lexeme lexbuf) }
  | eof
    { Parser.EOF }
  | _ as ch
    { error lexbuf ("illegal character (" ^ Char.escaped ch ^ ")") }
