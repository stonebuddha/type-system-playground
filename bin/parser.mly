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

%token BAR                          "|"
%token CASE                         "case"
%token COLON                        ":"
%token COMMA                        ","
%token DECL                         "decl"
%token DOT                          "."
%token DOTDOTDOT                    "..."
%token EOF                          ""
%token EQUAL                        "="
%token FUN                          "fun"
%token <string> IDENT               "ident" (* just an example *)
%token IN                           "in"
%token <string> LABEL               "`Label" (* just an example *)
%token LCURLY                       "{"
%token LET                          "let"
%token LPAREN                       "("
%token LSQUARE                      "["
%token MINUS                        "-"
%token MINUSGREATER                 "->"
%token RCURLY                       "}"
%token RPAREN                       ")"
%token RSQUARE                      "]"
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
    | LCURLY row RCURLY
      { fun tbl -> Ty_record ($2 tbl) }
    | LSQUARE row RSQUARE
      { fun tbl -> Ty_variant ($2 tbl) }
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

row:
  | mk_ty(

      { fun _ -> Ty_row_empty }
    )
    { $1 }
  | fixed_row
    { $1 }
  | extended_row
    { $1 }

fixed_row:
  | mk_ty(
      IDENT COLON ty
      { fun tbl ->
          let empty = { ty_desc = Ty_row_empty; ty_loc = Location.none } in
          Ty_row_extend ($1, $3 tbl, empty) }
    | IDENT COLON ty COMMA fixed_row
      { fun tbl -> Ty_row_extend ($1, $3 tbl, $5 tbl) }
    )
    { $1 }

extended_row:
  | DOTDOTDOT ty
    { $2 }
  | mk_ty(
      IDENT COLON ty COMMA extended_row
      { fun tbl -> Ty_row_extend ($1, $3 tbl, $5 tbl) }
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
    | LABEL simple_term
      { Tm_variant ($1, $2) }
    | CASE simple_term LPAREN cases RPAREN
      { let pat_cases, default_case_opt = $4 in
        Tm_case ($2, pat_cases, default_case_opt) }
    )
    { $1 }

simple_term:
  | LPAREN term RPAREN
    { $2 }
  | LCURLY record RCURLY
    { $2 }
  | mk_term(
      IDENT
      { Tm_var $1 }
    | simple_term LPAREN term RPAREN
      { Tm_app ($1, $3) }
    | simple_term DOT IDENT
      { Tm_record_select ($1, $3) }
    | LCURLY term MINUS IDENT RCURLY
      { Tm_record_restrict ($2, $4) }
    )
    { $1 }

record:
  | mk_term(

      { Tm_record_empty }
    )
    { $1 }
  | fixed_record
    { $1 }
  | extended_record
    { $1 }

fixed_record:
  | mk_term(
      IDENT EQUAL term
      { let empty = { term_desc = Tm_record_empty; term_ty = (); term_loc = Location.none } in
        Tm_record_extend ($1, $3, empty) }
    | IDENT EQUAL term COMMA fixed_record
      { Tm_record_extend ($1, $3, $5) }
    )
    { $1 }

extended_record:
  | DOTDOTDOT term
    { $2 }
  | mk_term(
      IDENT EQUAL term COMMA extended_record
      { Tm_record_extend ($1, $3, $5) }
    )
    { $1 }

cases:
  | pat_case
    { ([$1], None) }
  | default_case
    { ([], Some $1) }
  | pat_case BAR cases
    { let (pat_cases, default_case_opt) = $3 in ($1 :: pat_cases, default_case_opt) }

pat_case:
  | LABEL IDENT MINUSGREATER term
    { ($1, $2, $4) }

default_case:
  | IDENT MINUSGREATER term
    { ($1, $3) }

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
