open Core

exception Gra_error of string * Location.t

let () =
  Location.register_error_of_exn (function
      | Gra_error (msg, loc) -> Some (Location.errorf ~loc "%s" msg)
      | _ -> None)
;;

let last_token = ref Parser.EOF

let token lexbuf =
  let token = Lexer.token_exn lexbuf in
  last_token := token;
  token
;;

let rec skip_phrase lexbuf =
  match token lexbuf with
  | Parser.SEMICOLON | Parser.EOF -> ()
  | _ -> skip_phrase lexbuf
;;

let maybe_skip_phrase lexbuf =
  match !last_token with
  | Parser.SEMICOLON | Parser.EOF -> ()
  | _ -> skip_phrase lexbuf
;;

let rec loop lexbuf checkpoint =
  let module I = Parser.MenhirInterpreter in
  let string_of_terminal : type a. a I.terminal -> string option =
   fun terminal ->
    match terminal with
    | T_error -> None
    | T_WITH -> Some "keyword \"with\""
    | T_UNDERSCORE -> Some "underscore"
    | T_TRUE -> Some "keyword \"true\""
    | T_THEN -> Some "keyword \"then\""
    | T_SEMICOLON -> Some "semicolon"
    | T_RPAREN -> Some "right-parenthesis"
    | T_PLUS -> Some "plus symbol"
    | T_NIL -> Some "keyword \"nil\""
    | T_MINUSO -> Some "\"-o\""
    | T_MINUSGREATER -> Some "arrow"
    | T_LPAREN -> Some "left-parenthesis"
    | T_LIST -> Some "keyword \"list\""
    | T_LET -> Some "keyword \"let\""
    | T_LESSGREATER -> Some "diamond"
    | T_ITER -> Some "keyword \"iter\""
    | T_INR -> Some "keyword \"inr\""
    | T_INL -> Some "keyword \"inl\""
    | T_IN -> Some "keyword \"int\""
    | T_IF -> Some "keyword \"if\""
    | T_IDENT -> Some "identifier"
    | T_FUN -> Some "keyword \"fun\""
    | T_FALSE -> Some "keyword \"false\""
    | T_EQUAL -> Some "equal symbol"
    | T_EOF -> Some "EOF"
    | T_ELSE -> Some "keyword \"else\""
    | T_DOTR -> Some "\".r\""
    | T_DOTL -> Some "\".l\""
    | T_DECL -> Some "keyword \"decl\""
    | T_CONS -> Some "keyword \"cons\""
    | T_COMMA -> Some "comma"
    | T_COLON -> Some "colon"
    | T_CASE -> Some "keyword \"case\""
    | T_BOOL -> Some "keyword \"bool\""
    | T_BAR -> Some "bar symbol"
    | T_ASTERISK -> Some "asterisk"
    | T_AMPERSAND -> Some "ampersand"
  in
  let string_of_nonterminal : type a. a I.nonterminal -> string option = function
    | N_ty | N_tensor_ty | N_simple_ty | N_additive_ty -> Some "a type"
    | N_term | N_simple_term -> Some "a term"
    | N_list_dec_ | N_file_exn -> Some "a list of commands"
    | N_dec_exn | N_dec -> Some "a command"
  in
  let string_of_xsymbol (I.X symbol) =
    match symbol with
    | T terminal -> string_of_terminal terminal
    | N nonterminal -> string_of_nonterminal nonterminal
  in
  let generate_hint items =
    let aux (prod, idx) =
      if idx < List.length (I.rhs prod)
      then (
        let xsymbol = List.nth_exn (I.rhs prod) idx in
        string_of_xsymbol xsymbol)
      else (
        let xsymbol = I.lhs prod in
        Option.map (string_of_xsymbol xsymbol) ~f:(fun desc -> "something after " ^ desc))
    in
    let nexts = List.filter_map items ~f:aux in
    match nexts with
    | [] -> "syntax error"
    | [ next ] -> "expect " ^ next
    | [ next1; next2 ] -> "expect " ^ next1 ^ " or " ^ next2
    | _ ->
      let nexts_but_last, last = List.drop_last_exn nexts, List.last_exn nexts in
      "expect " ^ String.concat ~sep:", " nexts_but_last ^ ", or " ^ last
  in
  match checkpoint with
  | I.InputNeeded _ ->
    let token = token lexbuf in
    let triple = token, lexbuf.Lexing.lex_start_p, lexbuf.Lexing.lex_curr_p in
    let checkpoint = I.offer checkpoint triple in
    loop lexbuf checkpoint
  | Shifting _ | AboutToReduce _ -> loop lexbuf (I.resume checkpoint)
  | Accepted v -> v
  | Rejected ->
    let loc = Location.curr lexbuf in
    raise (Gra_error ("syntax error", loc))
  | HandlingError env ->
    let loc = Location.curr lexbuf in
    let msg =
      match I.stack env with
      | (lazy Nil) -> "expect a command"
      | (lazy (Cons (Element (state, _, _, _), _))) -> generate_hint (I.items state)
    in
    raise (Gra_error (msg, loc))
;;

let wrap_menhir entry_exn lexbuf =
  Result.try_with (fun () ->
      try
        let initial = entry_exn lexbuf.Lexing.lex_curr_p in
        let result = loop lexbuf initial in
        Parsing.clear_parser ();
        last_token := Parser.EOF;
        result
      with
      | Lexer.Lex_error _ as err when String.(!Location.input_name = "//toplevel//") ->
        skip_phrase lexbuf;
        raise err
      | Gra_error _ as err when String.(!Location.input_name = "//toplevel//") ->
        maybe_skip_phrase lexbuf;
        raise err
      | Parsing.Parse_error ->
        let loc = Location.curr lexbuf in
        if String.(!Location.input_name = "//toplevel//") then maybe_skip_phrase lexbuf;
        raise (Gra_error ("syntax error", loc)))
;;

let dec = wrap_menhir Parser.Incremental.dec_exn
let file = wrap_menhir Parser.Incremental.file_exn
