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
%token DOTL                         ".l"
%token DOTR                         ".r"
%token ELSE                         "else"
%token EOF                          ""
%token EQUAL                        "="
%token FALSE                        "false"
%token FUN                          "fun"
%token IF                           "if"
%token <string> LIDENT              "ident" (* just an example *)
%token IN                           "in"
%token INL                          "inl"
%token INR                          "inr"
%token LET                          "let"
%token LIST                         "list"
%token LPAREN                       "("
%token MINUSGREATER                 "->"
%token MINUSO                       "-o"
%token NIL                          "nil"
%token PLUS                         "+"
%token RPAREN                       ")"
%token SEMICOLON                    ";"
%token SHOWTYPE                     "#type"
%token THEN                         "then"
%token TRUE                         "true"
%token <string> UIDENT              "Ident" (* just an example *)

%start <cmd> cmd_exn
%start <cmd list> file_exn

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
    | CASE simple_term LPAREN NIL MINUSGREATER term BAR CONS LPAREN LIDENT COMMA LIDENT RPAREN MINUSGREATER term RPAREN
      { Tm_matl ($2, $6, ($10, $12, $15)) }
    | simple_term ASTERISK term
      { Tm_tensor ($1, $3) }
    | LET LIDENT ASTERISK LIDENT EQUAL term IN term
      { Tm_letp ($6, ($2, $4, $8)) }
    | FUN LIDENT MINUSGREATER term
      { Tm_abs ($2, None, $4) }
    | FUN LPAREN LIDENT COLON ty RPAREN MINUSGREATER term
      { Tm_abs ($3, Some $5, $8) }
    | simple_term AMPERSAND term
      { Tm_with ($1, $3) }
    | LET LIDENT EQUAL term IN term
      { Tm_let ($4, ($2, $6)) }
    | INL simple_term
      { Tm_inl $2 }
    | INR simple_term
      { Tm_inr $2 }
    | CASE simple_term LPAREN INL LIDENT MINUSGREATER term BAR INR LIDENT MINUSGREATER term RPAREN
      { Tm_case ($2, ($5, $7), ($10, $12)) }
    )
    { $1 }

simple_term:
  | LPAREN term RPAREN
    { $2 }
  | mk_term(
      LIDENT
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
    | UIDENT LPAREN separated_list(COMMA, term) RPAREN
      { Tm_call ($1, $3) }
    )
    { $1 }

dec:
  | mk_dec(
      UIDENT LPAREN separated_list(COMMA, pair(LIDENT, option(preceded(COLON, ty)))) RPAREN option(preceded(COLON, ty)) EQUAL term
      { Dec_defn ($1, $3, $5, (), $7) }
    )
    { $1 }

cmd_exn:
  | cmd
    { $1 }
  | EOF
    { raise End_of_file }

cmd:
  | dec SEMICOLON
    { Cmd_dec $1 }
  | SHOWTYPE UIDENT SEMICOLON
    { Cmd_show_type $2 }

file_exn:
  | list(cmd) EOF
    { $1 }
