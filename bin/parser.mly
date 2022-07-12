%{
open Ast

let make_loc (start_pos, end_pos) =
  { Location.loc_start = start_pos
  ; Location.loc_end = end_pos
  ; Location.loc_ghost = false
  }
;;

let mk_ty ~loc ty_desc = { ty_desc; ty_loc = make_loc loc }
let mk_term ~loc term_desc = { term_desc; term_ty = (); term_loc = make_loc loc }
let mk_dec ~loc dec_desc = { dec_desc; dec_loc = make_loc loc }
%}

%token AMPERSAND                    "&"
%token ASTERISK                     "*"
%token BAR                          "|"
%token BOOL                         "bool"
%token CASE                         "case"
%token COLON                        ":"
%token COMMA                        ","
%token CONS                         "cons"
%token DECL                         "decl"
%token DOTL                         ".l"
%token DOTR                         ".r"
%token ELSE                         "else"
%token EOF                          ""
%token EQUAL                        "="
%token FALSE                        "false"
%token FUN                          "fun"
%token IF                           "if"
%token <string> IDENT               "ident" (* just an example *)
%token IN                           "in"
%token INL                          "inl"
%token INR                          "inr"
%token ITER                         "iter"
%token LET                          "let"
%token LIST                         "list"
%token LPAREN                       "("
%token MINUSGREATER                 "->"
%token MINUSO                       "-o"
%token NIL                          "nil"
%token PLUS                         "+"
%token RPAREN                       ")"
%token SEMICOLON                    ";"
%token THEN                         "then"
%token TRUE                         "true"
%token UNDERSCORE                   "_"
%token WITH                         "with"

%start <untyped_dec> dec_exn
%start <untyped_dec list> file_exn

%%

%inline mk_ty(symb): symb { mk_ty ~loc:$sloc $1 }
%inline mk_term(symb): symb { mk_term ~loc:$sloc $1 }
%inline mk_dec(symb): symb { mk_dec ~loc:$sloc $1 }

ty:
  | tensor_ty
    { $1 }
  | mk_ty(
      tensor_ty MINUSO ty
      { Ty_lolli ($1, $3) }
    )
    { $1 }

tensor_ty:
  | additive_ty
    { $1 }
  | mk_ty(
      additive_ty ASTERISK tensor_ty
      { Ty_tensor ($1, $3) }
    )
    { $1 }

additive_ty:
  | simple_ty
    { $1 }
  | mk_ty(
      simple_ty AMPERSAND additive_ty
      { Ty_with ($1, $3) }
    | simple_ty PLUS additive_ty
      { Ty_plus ($1, $3) }
    )
    { $1 }

simple_ty:
  | LPAREN ty RPAREN
    { $2 }
  | mk_ty(
      BOOL
      { Ty_bool }
    | LIST LPAREN ty RPAREN
      { Ty_list $3 }
    )
    { $1 }

term:
  | simple_term
    { $1 }
  | mk_term(
      IF term THEN term ELSE term
      { Tm_cond ($2, $4, $6) }
    | ITER simple_term LPAREN NIL MINUSGREATER term BAR CONS LPAREN IDENT COMMA UNDERSCORE RPAREN WITH IDENT MINUSGREATER term RPAREN
      { Tm_iter ($2, $6, ($10, $15, $17)) }
    | simple_term ASTERISK term
      { Tm_tensor ($1, $3) }
    | LET IDENT ASTERISK IDENT EQUAL term IN term
      { Tm_letp ($6, ($2, $4, $8)) }
    | FUN IDENT MINUSGREATER term
      { Tm_abs ($2, None, $4) }
    | FUN LPAREN IDENT COLON ty RPAREN MINUSGREATER term
      { Tm_abs ($3, Some $5, $8) }
    | simple_term AMPERSAND term
      { Tm_with ($1, $3) }
    | LET IDENT EQUAL term IN term
      { Tm_let ($4, ($2, $6)) }
    | INL simple_term
      { Tm_inl $2 }
    | INR simple_term
      { Tm_inr $2 }
    | CASE simple_term LPAREN INL IDENT MINUSGREATER term BAR INR IDENT MINUSGREATER term RPAREN
      { Tm_case ($2, ($5, $7), ($10, $12)) }
    )
    { $1 }

simple_term:
  | LPAREN term RPAREN
    { $2 }
  | mk_term(
      IDENT
      { Tm_var $1 }
    | TRUE
      { Tm_bool true }
    | FALSE
      { Tm_bool false }
    | NIL
      { Tm_nil }
    | CONS LPAREN term COMMA term RPAREN
      { Tm_cons ($3, $5) }
    | simple_term LPAREN term RPAREN
      { Tm_app ($1, $3) }
    | simple_term DOTL
      { Tm_first $1 }
    | simple_term DOTR
      { Tm_second $1 }
    )
    { $1 }

dec_exn:
  | dec
    { $1 }
  | EOF
    { raise End_of_file }

dec:
  | mk_dec(
      LET IDENT EQUAL term SEMICOLON
      { Dec_val (Some $2, $4) }
    | term SEMICOLON
      { Dec_val (None, $1) }
    | DECL IDENT COLON ty SEMICOLON
      { Dec_decl ($2, $4, ()) }
    )
    { $1 }

file_exn:
  | list(dec) EOF
    { $1 }
