open Core
open OUnit2

let parse_ty str = Result.ok_exn (Parse.ty (Lexing.from_string str))
let parse_term str = Result.ok_exn (Parse.term (Lexing.from_string str))

let string_of_result res =
  Sexp.to_string_hum (Result.sexp_of_t String.sexp_of_t String.sexp_of_t res)
;;

let equal_result res1 res2 =
  Result.equal
    (fun ty_str1 ty_str2 ->
      let normalize s = Ast.string_of_ty (parse_ty s) in
      String.equal (normalize ty_str1) (normalize ty_str2))
    String.equal
    res1
    res2
;;

let prelude_env = Spec.Top.produce_prelude_environment ()

let make_single_test_case (code, expected_result) =
  String.escaped code
  >:: fun _ ->
  let result =
    try
      let tm = parse_term code in
      let dec = { Ast.dec_desc = Dec_val (None, tm); dec_loc = tm.term_loc } in
      let dec', _ = Infer.f_dec_exn ~verbose:false prelude_env dec in
      match dec'.dec_desc with
      | Dec_val (_, tm') -> Ok (Ast.string_of_ty tm'.term_ty)
      | _ -> assert false
    with
    | Lexer.Lex_error (msg, _) | Parse.Gra_error (msg, _) | Infer.Type_error (msg, _) ->
      Error msg
    | _ -> Error "<unknown error>"
  in
  assert_equal ~printer:string_of_result ~cmp:equal_result expected_result result
;;

let suite =
  Spec.Lang.name
  >::: List.map
         ~f:make_single_test_case
         [ "id", Ok "'a -> 'a"
         ; "one", Ok "int"
         ; "x", Error "variable x not found"
         ; "let x = x in x", Error "variable x not found"
         ; "let x = id in x", Ok "'a -> 'a"
         ; "let x = fun y -> y in x", Ok "'a -> 'a"
         ; "fun x -> x", Ok "'a -> 'a"
         ; "fun x -> x", Ok "'int -> 'int"
         ; "pair", Ok "'a -> 'b -> pair('a, 'b)"
         ; "pair", Ok "'x -> 'z -> pair('x, 'z)"
         ; "fun x -> let y = fun z -> z in y", Ok "'a -> 'b -> 'b"
         ; "let f = fun x -> x in let id = fun y -> y in eq(f)(id)", Ok "bool"
         ; "let f = fun x -> x in eq(f)(succ)", Ok "bool"
         ; "let f = fun x -> x in pair(f(one))(f(true))", Ok "pair(int, bool)"
         ; "fun f -> pair(f(one))(f(true))", Error "cannot unify types"
         ; ( "let f = fun x -> fun y -> let a = eq(x)(y) in eq(x)(y) in f"
           , Ok "'a -> 'a -> bool" )
         ; "id(id)", Ok "'a -> 'a"
         ; "choose(fun x -> fun y -> x)(fun x -> fun y -> y)", Ok "'a -> 'a -> 'a"
         ; "let x = id in let y = let z = x(id) in z in y", Ok "'a -> 'a"
         ; "cons(id)(nil)", Ok "list('a -> 'a)"
         ; ( "let lst1 = cons(id)(nil) in let lst2 = cons(succ)(lst1) in lst2"
           , Ok "list(int -> int)" )
         ; "cons(id)(cons(succ)(cons(id)(nil)))", Ok "list(int -> int)"
         ; "plus(one)(true)", Error "cannot unify types"
         ; "plus(one)", Ok "int -> int"
         ; "fun x -> let y = x in y", Ok "'a -> 'a"
         ; ( "fun x -> let y = let z = x(fun x -> x) in z in y"
           , Ok "(('a -> 'a) -> 'b) -> 'b" )
         ; "fun x -> fun y -> let x = x(y) in x(y)", Ok "('a -> 'a -> 'b) -> 'a -> 'b"
         ; "fun x -> let y = fun z -> x(z) in y", Ok "('a -> 'b) -> 'a -> 'b"
         ; "fun x -> let y = fun z -> x in y", Ok "'a -> 'b -> 'a"
         ; ( "fun x -> fun y -> let x = x(y) in fun x -> y(x)"
           , Ok "(('a -> 'b) -> 'c) -> ('a -> 'b) -> 'a -> 'b" )
         ; "fun x -> let y = x in y(y)", Error "cannot handle recursive types"
         ; "fun x -> let y = fun z -> z in y(y)", Ok "'a -> 'b -> 'b"
         ; "fun x -> x(x)", Error "cannot handle recursive types"
         ; "one(id)", Error "cannot unify types"
         ; ( "fun f -> let x = fun g -> fun y -> let z = g(y) in eq(f)(g) in x"
           , Ok "('a -> 'b) -> ('a -> 'b) -> 'a -> bool" )
         ; "let const = fun x -> fun y -> x in const", Ok "'a -> 'b -> 'a"
         ; "let apply = fun f -> fun x -> f(x) in apply", Ok "('a -> 'b) -> 'a -> 'b"
         ; ( "let fib1 = fun fib -> fun n -> \
              if(eq(n)(one))(one)(if(eq(n)(zero))(one)(plus(fib(minus(n)(one)))(fib(minus(n)(succ(one)))))) \
              in fix(fib1)"
           , Ok "int -> int" )
         ]
;;

let () = run_test_tt_main suite
