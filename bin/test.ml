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
         ; "{}", Ok "{}"
         ; "{}.x", Error "row does not contain label x"
         ; "{a= one}", Ok "{a: int}"
         ; "{a= one, b= true}", Ok "{a: int, b: bool}"
         ; "{b= true, a= one}", Ok "{b: bool, a: int}"
         ; "{a= one, b= true}.a", Ok "int"
         ; "{a= one, b= true}.b", Ok "bool"
         ; "{a= one, b= true}.c", Error "row does not contain label c"
         ; "{f= fun x -> x}", Ok "{f: 'a -> 'a}"
         ; "let r = {a= id, b= succ} in choose(r.a)(r.b)", Ok "int -> int"
         ; "let r = {a= id, b= fun x -> x} in choose(r.a)(r.b)", Ok "'a -> 'a"
         ; "choose({a= one})({})", Error "row does not contain label a"
         ; "{x= zero, ...{y= one, ...{}}}", Ok "{x: int, y: int}"
         ; ( "choose({x= zero, ...{y= one, ...{}}})({x= one, y= zero})"
           , Ok "{x: int, y: int}" )
         ; "{{} - x}", Error "row does not contain label x"
         ; "{{x= one, y= zero} - x}", Ok "{y: int}"
         ; "{x= true, ...{x= one}}", Ok "{x: bool, x: int}"
         ; "let a = {} in {b= one, ...a}", Ok "{b: int}"
         ; "let a = {x= one} in {x= true, ...a}.x", Ok "bool"
         ; "let a = {x= one} in a.y", Error "row does not contain label y"
         ; "let a = {x= one} in {a - x}", Ok "{}"
         ; "let a = {x= one} in let b = {x= true, ...a} in {b - x}.x", Ok "int"
         ; "fun r -> {x= one, ...r}", Ok "{...'r} -> {x: int, ...'r}"
         ; "fun r -> r.x", Ok "{x: 'a, ...'r} -> 'a"
         ; "let get_x = fun r -> r.x in get_x({y= one, x= zero})", Ok "int"
         ; ( "let get_x = fun r -> r.x in get_x({y= one, z= true})"
           , Error "row does not contain label x" )
         ; "fun r -> choose({x= zero, ...r})({x= one, ...{}})", Ok "{} -> {x: int}"
         ; "fun r -> choose({x= zero, ...r})({x= one})", Ok "{} -> {x: int}"
         ; ( "fun r -> choose({x= zero, ...r})({x= one, ...r})"
           , Ok "{...'r} -> {x: int, ...'r}" )
         ; ( "fun r -> choose({x= zero, ...r})({y= one, ...r})"
           , Error "cannot handle recursive types" )
         ; "let f = fun x -> x.t(one) in f({t= succ})", Ok "int"
         ; "let f = fun x -> x.t(one) in f({t= id})", Ok "int"
         ; "{x= one, x= true}", Ok "{x: int, x: bool}"
         ; ( "let f = fun r -> let y = r.y in choose(r)({x= one, x= true}) in f"
           , Error "row does not contain label y" )
         ; ( "fun r -> let y = choose(r.x)(one) in let z = choose({r - x}.x)(true) in r"
           , Ok "{x: int, x: bool, ...'r} -> {x: int, x: bool, ...'r}" )
         ; ( "fun r -> choose({x= zero, ...r})({x= one, x= true})"
           , Ok "{x: bool} -> {x: int, x: bool}" )
         ; ( "fun r -> choose(r)({x= one, x= true})"
           , Ok "{x: int, x: bool} -> {x: int, x: bool}" )
         ; "fun r -> choose({x= zero, ...r})({x= true, ...r})", Error "cannot unify types"
         ; ( "fun r -> fun s -> choose({b= true, a= one, c= zero, b= half, ...r})({b= \
              false, c= one, d= half, ...s})"
           , Ok
               "{d: float, ...'r} -> {a: int, b: float, ...'r} -> {b: bool, a: int, c: \
                int, b: float, d: float, ...'r}" )
         ; ( "fun r -> fun s -> choose({b= true, a= one, c= zero, b= half, ...r})({b= \
              false, c= one, ...s})"
           , Ok
               "{...'r} -> {a: int, b: float, ...'r} -> {b: bool, a: int, c: int, b: \
                float, ...'r}" )
         ; ( "fun r -> fun s -> choose({b= true, c= zero, ...r})({b= false, c= one, d= \
              half, ...s})"
           , Ok "{d: float, ...'r} -> {...'r} -> {b: bool, c: int, d: float, ...'r}" )
         ; ( "fun r -> fun s -> choose({b= true, a= one, c= one, b= half, ...r})({b= \
              false, c= one, a= one, b= half, ...s})"
           , Ok "{...'r} -> {...'r} -> {b: bool, a: int, c: int, b: float, ...'r}" )
         ; "fun r -> {x= r, ...r}", Ok "{...'r} -> {x: {...'r}, ...'r}"
         ; "`X one", Ok "[X: int, ...'r]"
         ; ( "choose(choose(`x one)(`Y true))(choose(`X half)(`y nil))"
           , Ok "[x: int, Y: bool, X: float, y: list('a), ...'r]" )
         ; "choose(`X one)(`X true)", Error "cannot unify types"
         ; ( "choose(`X {x= one, y= false})(`Y {w= half})"
           , Ok "[X: {x: int, y: bool}, Y: {w: float}, ...'r]" )
         ; ( "let e = choose(choose(`x one)(`Y true))(choose(`X half)(`y nil)) in case e \
              ( `x i -> i | `Y i -> zero )"
           , Error "row does not contain label X" )
         ; ( "fun x -> fun y -> case x ( `a i -> one | `b i -> zero | `c i -> y )"
           , Ok "[a: 'a, b: 'b, c: 'c] -> int -> int" )
         ; "fun a -> case a ( `X i -> i | r -> one )", Ok "[X: int, ...'r] -> int"
         ; ( "let f = fun m -> case m ( `y a -> one | `Y b -> zero | `z z -> zero ) in \
              fun e -> case e ( `x i -> i | `X f -> one | r -> f(r) )"
           , Ok "[x: int, X: 'a, y: 'b, Y: 'c, z: 'd] -> int" )
         ; ( "let e = choose(choose(`x one)(`Y true))(choose(`X half)(`y nil)) in let f \
              = fun m -> case m ( `y a -> one | `Y b -> zero | `z z -> zero ) in case e \
              ( `x i -> i | `X f -> one | r -> f(r) )"
           , Ok "int" )
         ; "fun e -> case e ( `X a -> one | `X i -> i )", Ok "[X: 'a, X: int] -> int"
         ; ( "let f = fun g -> fun e -> case e ( `x i -> i | `Y a -> one | r -> g(r) ) \
              in let g = fun s -> case s ( `x j -> head(j) | `X a -> zero ) in f(g)"
           , Ok "[x: int, Y: 'a, x: list(int), X: 'b] -> int" )
         ; "fun e -> case e ( `X a -> plus(a.x)(one) )", Ok "[X: {x: int, ...'r}] -> int"
         ; ( "let count1 = fun count -> fun x -> case x ( `Cons a -> \
              plus(one)(count(a.tail)) | `Nil u -> zero ) in fix(count1)"
           , Error "cannot handle recursive types" )
         ]
;;

let () = run_test_tt_main suite
