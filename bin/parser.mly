%{
open Ast

let make_loc (start_pos, end_pos) =
  { Location.loc_start = start_pos
  ; Location.loc_end = end_pos
  ; Location.loc_ghost = false
  }
;;

let mk_ty ~loc gen_ty_desc tbl = { ty_desc = gen_ty_desc tbl; ty_loc = make_loc loc }
let mk_term ~loc term_desc = { term_desc; term_ty = (); term_loc = make_loc loc }
let mk_dec ~loc dec_desc = { dec_desc; dec_loc = make_loc loc }
%}

%token COLON                        ":"
%token COMMA                        ","
%token DECL                         "decl"
%token EOF                          ""
%token EQUAL                        "="
%token FUN                          "fun"
%token <string> IDENT               "ident" (* just an example *)
%token IN                           "in"
%token LET                          "let"
%token LPAREN                       "("
%token MINUSGREATER                 "->"
%token RPAREN                       ")"
%token SEMICOLON                    ";"
%token TYPE                         "type"
%token <string> TYVAR               "'tyvar" (* just an example *)

%start <ty> ty_exn
%start <untyped_term> term_exn
%start <untyped_dec> dec_exn
%start <untyped_dec list> file_exn

%%

%inline mk_ty(symb): symb { mk_ty ~loc:$sloc $1 }
%inline mk_term(symb): symb { mk_term ~loc:$sloc $1 }
%inline mk_dec(symb): symb { mk_dec ~loc:$sloc $1 }

ty_exn:
  | ty EOF
    { $1 (Core.String.Table.create ()) }

ty:
  | simple_ty
    { $1 }
  | mk_ty(
      simple_ty MINUSGREATER ty
      { fun tbl -> Ty_arrow ($1 tbl, $3 tbl) }
    )
    { $1 }

simple_ty:
  | LPAREN ty RPAREN
    { $2 }
  | mk_ty(
      IDENT
      { fun _ -> Ty_const $1 }
    | simple_ty LPAREN separated_nonempty_list(COMMA, ty) RPAREN
      { fun tbl -> Ty_app ($1 tbl, Core.List.map $3 ~f:(fun g -> g tbl)) }
    | TYVAR
      { fun tbl ->
          match Core.Hashtbl.find tbl $1 with
          | Some v -> v
          | None ->
            let v = Ty_quan_var (fresh_ty_id ()) in
            Core.Hashtbl.add_exn tbl ~key:$1 ~data:v;
            v }
    )
    { $1 }

term_exn:
  | term EOF
    { $1 }

term:
  | simple_term
    { $1 }
  | mk_term(
      FUN IDENT MINUSGREATER term
      { Tm_abs ($2, $4) }
    | LET IDENT EQUAL term IN term
      { Tm_let ($4, ($2, $6)) }
    )
    { $1 }

simple_term:
  | LPAREN term RPAREN
    { $2 }
  | mk_term(
      IDENT
      { Tm_var $1 }
    | simple_term LPAREN term RPAREN
      { Tm_app ($1, $3) }
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
    | TYPE IDENT SEMICOLON
      { Dec_type $2 }
    | DECL IDENT COLON ty SEMICOLON
      { Dec_decl ($2, $4 (Core.String.Table.create ())) }
    )
    { $1 }

file_exn:
  | list(dec) EOF
    { $1 }
