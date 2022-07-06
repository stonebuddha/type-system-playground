open Core

exception Type_error of string * Location.t

let () =
  Location.register_error_of_exn (function
      | Type_error (msg, loc) -> Some (Location.errorf ~loc "%s" msg)
      | _ -> None)
;;

module Level = struct
  type t = int

  let counter = ref 0
  let current () = !counter
  let reset () = counter := 0
  let enter () = Int.incr counter
  let leave () = Int.decr counter
end

type tyexp =
  | Tye_const of string
  | Tye_app of tyexp * tyexp list
  | Tye_arrow of tyexp * tyexp
  | Tye_record of tyexp
  | Tye_variant of tyexp
  | Tye_row_empty
  | Tye_row_extend of string * tyexp * tyexp
  | Tye_quan_var of Ast.ty_id
  | Tye_var of tyvar ref

and tyvar =
  | Tyv_link of tyexp
  | Tyv_unbound of Ast.ty_id * Level.t

module Env = struct
  type t = String.Set.t * tyexp String.Map.t

  let empty = String.Set.empty, String.Map.empty
  let add_type_const (tenv, venv) name = Set.add tenv name, venv
  let mem_type_const (tenv, _) name = Set.mem tenv name
  let add_var_type_bind (tenv, venv) x tye = tenv, Map.set venv ~key:x ~data:tye
  let find_var_type_bind (_, venv) x = Map.find venv x
end

let fresh_var () = Tye_var (ref (Tyv_unbound (Ast.fresh_ty_id (), Level.current ())))

let rec embed_ty_exn env ty =
  match ty.Ast.ty_desc with
  | Ty_const name ->
    if Env.mem_type_const env name
    then Tye_const name
    else raise @@ Type_error ("type constant " ^ name ^ " not found", ty.ty_loc)
  | Ty_app (ty1, ty2s) ->
    Tye_app (embed_ty_exn env ty1, List.map ty2s ~f:(embed_ty_exn env))
  | Ty_arrow (ty1, ty2) -> Tye_arrow (embed_ty_exn env ty1, embed_ty_exn env ty2)
  | Ty_record row -> Tye_record (embed_ty_exn env row)
  | Ty_variant row -> Tye_variant (embed_ty_exn env row)
  | Ty_row_empty -> Tye_row_empty
  | Ty_row_extend (l, ty, row0) ->
    Tye_row_extend (l, embed_ty_exn env ty, embed_ty_exn env row0)
  | Ty_quan_var id -> Tye_quan_var id
  | Ty_weak_var _ -> assert false
;;

let inst_tye tye =
  let tbl = Hashtbl.create (module Int) in
  let rec aux = function
    | Tye_const name -> Tye_const name
    | Tye_app (tye1, tye2s) -> Tye_app (aux tye1, List.map tye2s ~f:aux)
    | Tye_arrow (tye1, tye2) -> Tye_arrow (aux tye1, aux tye2)
    | Tye_record row -> Tye_record (aux row)
    | Tye_variant row -> Tye_variant (aux row)
    | Tye_row_empty -> Tye_row_empty
    | Tye_row_extend (l, ty, row0) -> Tye_row_extend (l, aux ty, aux row0)
    | Tye_quan_var id ->
      (match Hashtbl.find tbl id with
      | Some v -> v
      | None ->
        let v = fresh_var () in
        Hashtbl.add_exn tbl ~key:id ~data:v;
        v)
    | Tye_var { contents = Tyv_link tye0 } -> aux tye0
    | Tye_var r -> Tye_var r
  in
  aux tye
;;

let rec gen_tye = function
  | Tye_const name -> Tye_const name
  | Tye_app (tye1, tye2s) -> Tye_app (gen_tye tye1, List.map tye2s ~f:gen_tye)
  | Tye_arrow (tye1, tye2) -> Tye_arrow (gen_tye tye1, gen_tye tye2)
  | Tye_record row -> Tye_record (gen_tye row)
  | Tye_variant row -> Tye_variant (gen_tye row)
  | Tye_row_empty -> Tye_row_empty
  | Tye_row_extend (l, ty, row0) -> Tye_row_extend (l, gen_tye ty, gen_tye row0)
  | Tye_quan_var id -> Tye_quan_var id
  | Tye_var ({ contents = Tyv_link tye0 } as r) ->
    let tye0' = gen_tye tye0 in
    r := Tyv_link tye0';
    tye0'
  | Tye_var ({ contents = Tyv_unbound (id, level) } as r) ->
    if level > Level.current ()
    then (
      let v = Tye_quan_var id in
      r := Tyv_link v;
      v)
    else Tye_var r
;;

let rec deref_tye tye =
  let ty_desc =
    match tye with
    | Tye_const name -> Ast.Ty_const name
    | Tye_app (tye1, tye2s) -> Ty_app (deref_tye tye1, List.map tye2s ~f:deref_tye)
    | Tye_arrow (tye1, tye2) -> Ty_arrow (deref_tye tye1, deref_tye tye2)
    | Tye_record row -> Ty_record (deref_tye row)
    | Tye_variant row -> Ty_variant (deref_tye row)
    | Tye_row_empty -> Ty_row_empty
    | Tye_row_extend (l, ty, row0) -> Ty_row_extend (l, deref_tye ty, deref_tye row0)
    | Tye_quan_var id -> Ty_quan_var id
    | Tye_var { contents = Tyv_link tye0 } -> (deref_tye tye0).ty_desc
    | Tye_var { contents = Tyv_unbound (id, _) } -> Ty_weak_var id
  in
  { ty_desc; ty_loc = Location.none }
;;

let rec occur r1 = function
  | Tye_const _ -> false
  | Tye_app (tye21, tye22s) -> occur r1 tye21 || List.exists tye22s ~f:(occur r1)
  | Tye_arrow (tye21, tye22) -> occur r1 tye21 || occur r1 tye22
  | Tye_record row -> occur r1 row
  | Tye_variant row -> occur r1 row
  | Tye_row_empty -> false
  | Tye_row_extend (_, ty, row0) -> occur r1 ty || occur r1 row0
  | Tye_quan_var _ -> false
  | Tye_var r2 when phys_equal r1 r2 -> true
  | Tye_var { contents = Tyv_link tye20 } -> occur r1 tye20
  | Tye_var ({ contents = Tyv_unbound (id2, level2) } as r2) ->
    let min_level =
      match !r1 with
      | Tyv_unbound (_, level1) -> min level1 level2
      | _ -> level2
    in
    r2 := Tyv_unbound (id2, min_level);
    false
;;

let rec unify_exn ~loc tye1 tye2 =
  match tye1, tye2 with
  | Tye_const name1, Tye_const name2 when String.(name1 = name2) -> ()
  | Tye_app (tye11, tye12s), Tye_app (tye21, tye22s)
    when List.length tye12s = List.length tye22s ->
    unify_exn ~loc tye11 tye21;
    List.iter2_exn tye12s tye22s ~f:(unify_exn ~loc)
  | Tye_arrow (tye11, tye12), Tye_arrow (tye21, tye22) ->
    unify_exn ~loc tye11 tye21;
    unify_exn ~loc tye12 tye22
  | Tye_record row1, Tye_record row2 -> unify_exn ~loc row1 row2
  | Tye_variant row1, Tye_variant row2 -> unify_exn ~loc row1 row2
  | Tye_row_empty, Tye_row_empty -> ()
  | Tye_row_empty, Tye_row_extend (l2, _, _) ->
    raise @@ Type_error ("row does not contain label " ^ l2, loc)
  | Tye_row_extend (l1, _, _), Tye_row_empty ->
    raise @@ Type_error ("row does not contain label " ^ l1, loc)
  | Tye_row_extend (l1, ty1, row10), (Tye_row_extend _ as row2) ->
    let row10_r_opt =
      match row10 with
      | Tye_var ({ contents = Tyv_unbound _ } as r) -> Some r
      | _ -> None
    in
    let row20 = rewrite_row_exn ~loc row2 l1 ty1 in
    (match row10_r_opt with
    | Some { contents = Tyv_link _ } ->
      raise @@ Type_error ("cannot handle recursive types", loc)
    | _ -> ());
    unify_exn ~loc row10 row20
  | Tye_quan_var id1, Tye_quan_var id2 when id1 = id2 -> ()
  | Tye_var r1, Tye_var r2 when phys_equal r1 r2 -> ()
  | Tye_var { contents = Tyv_link tye10 }, _ -> unify_exn ~loc tye10 tye2
  | _, Tye_var { contents = Tyv_link tye20 } -> unify_exn ~loc tye1 tye20
  | Tye_var ({ contents = Tyv_unbound _ } as r1), _ ->
    if occur r1 tye2 then raise @@ Type_error ("cannot handle recursive types", loc);
    r1 := Tyv_link tye2
  | _, Tye_var ({ contents = Tyv_unbound _ } as r2) ->
    if occur r2 tye1 then raise @@ Type_error ("cannot handle recursive types", loc);
    r2 := Tyv_link tye1
  | _, _ -> raise @@ Type_error ("cannot unify types", loc)

and rewrite_row_exn ~loc row l ty =
  match row with
  | Tye_row_empty -> raise @@ Type_error ("row does not contain label " ^ l, loc)
  | Tye_row_extend (l', ty', row0) when String.(l = l') ->
    unify_exn ~loc ty ty';
    row0
  | Tye_row_extend (l', ty', row0) ->
    Tye_row_extend (l', ty', rewrite_row_exn ~loc row0 l ty)
  | Tye_var { contents = Tyv_link row0 } -> rewrite_row_exn ~loc row0 l ty
  | Tye_var ({ contents = Tyv_unbound (_, level) } as r) ->
    let row0 = Tye_var (ref (Tyv_unbound (Ast.fresh_ty_id (), level))) in
    r := Tyv_link (Tye_row_extend (l, ty, row0));
    row0
  | _ -> assert false
;;

let rec g_term_exn env tm =
  let term_desc', tye =
    match tm.Ast.term_desc with
    | Tm_var x ->
      (match Env.find_var_type_bind env x with
      | Some tye -> Ast.Tm_var x, inst_tye tye
      | None -> raise @@ Type_error ("variable " ^ x ^ " not found", tm.term_loc))
    | Tm_abs (x, tm0) ->
      let tye_x = fresh_var () in
      let tm0', tye0 = g_term_exn (Env.add_var_type_bind env x tye_x) tm0 in
      Tm_abs (x, tm0'), Tye_arrow (tye_x, tye0)
    | Tm_app (tm1, tm2) ->
      let tm1', tye1 = g_term_exn env tm1 in
      let tm2', tye2 = g_term_exn env tm2 in
      let tye_res = fresh_var () in
      unify_exn ~loc:tm1.term_loc (Tye_arrow (tye2, tye_res)) tye1;
      Tm_app (tm1', tm2'), tye_res
    | Tm_let (tm1, (x, tm2)) ->
      Level.enter ();
      let tm1', tye1 = g_term_exn env tm1 in
      Level.leave ();
      let gen_tye1 = gen_tye tye1 in
      unify_exn ~loc:tm1.term_loc gen_tye1 tye1;
      let tm2', tye2 = g_term_exn (Env.add_var_type_bind env x gen_tye1) tm2 in
      Tm_let (tm1', (x, tm2')), tye2
    | Tm_record_empty -> Tm_record_empty, Tye_record Tye_row_empty
    | Tm_record_extend (l, tm1, tm2) ->
      let tm1', tye1 = g_term_exn env tm1 in
      let tm2', tye2 = g_term_exn env tm2 in
      let row0 = fresh_var () in
      unify_exn ~loc:tm2.term_loc (Tye_record row0) tye2;
      Tm_record_extend (l, tm1', tm2'), Tye_record (Tye_row_extend (l, tye1, row0))
    | Tm_record_select (tm0, l) ->
      let tm0', tye0 = g_term_exn env tm0 in
      let row0 = fresh_var () in
      let tye_res = fresh_var () in
      unify_exn ~loc:tm0.term_loc (Tye_record (Tye_row_extend (l, tye_res, row0))) tye0;
      Tm_record_select (tm0', l), tye_res
    | Tm_record_restrict (tm0, l) ->
      let tm0', tye0 = g_term_exn env tm0 in
      let row0 = fresh_var () in
      let tye_rem = fresh_var () in
      unify_exn ~loc:tm0.term_loc (Tye_record (Tye_row_extend (l, tye_rem, row0))) tye0;
      Tm_record_restrict (tm0', l), Tye_record row0
    | Tm_variant (l, tm0) ->
      let tm0', tye0 = g_term_exn env tm0 in
      let row0 = fresh_var () in
      Ast.Tm_variant (l, tm0'), Tye_variant (Tye_row_extend (l, tye0, row0))
    | Tm_case (tm0, pat_cases, default_case_opt) ->
      let tm0', tye0 = g_term_exn env tm0 in
      let tye_res = fresh_var () in
      let row0, default_case_opt' =
        match default_case_opt with
        | None -> Tye_row_empty, None
        | Some (x, default_case_tm) ->
          let row0 = fresh_var () in
          let tm', tye =
            g_term_exn (Env.add_var_type_bind env x (Tye_variant row0)) default_case_tm
          in
          unify_exn ~loc:default_case_tm.term_loc tye_res tye;
          row0, Some (x, tm')
      in
      let row, pat_cases' =
        List.fold_right
          pat_cases
          ~init:(row0, [])
          ~f:(fun (l, x, pat_case_tm) (acc_row, acc_pat_cases) ->
            let tye_x = fresh_var () in
            let tm', tye = g_term_exn (Env.add_var_type_bind env x tye_x) pat_case_tm in
            unify_exn ~loc:pat_case_tm.term_loc tye_res tye;
            Tye_row_extend (l, tye_x, acc_row), (l, x, tm') :: acc_pat_cases)
      in
      unify_exn ~loc:tm0.term_loc (Tye_variant row) tye0;
      Tm_case (tm0', pat_cases', default_case_opt'), tye_res
  in
  { term_desc = term_desc'; term_ty = tye; term_loc = tm.term_loc }, tye
;;

let g_dec_exn ~verbose env dec =
  let dec_desc', env' =
    match dec.Ast.dec_desc with
    | Dec_val (x_opt, tm) ->
      Level.enter ();
      let tm', tye = g_term_exn env tm in
      Level.leave ();
      let gen_tye = gen_tye tye in
      unify_exn ~loc:tm.term_loc gen_tye tye;
      if verbose
      then
        Format.printf
          "val %s: %s@."
          (Option.value x_opt ~default:"_")
          (Ast.string_of_ty (deref_tye gen_tye));
      ( Ast.Dec_val (x_opt, Ast.map_ty_term ~f:deref_tye tm')
      , Option.value_map x_opt ~default:env ~f:(fun x ->
            Env.add_var_type_bind env x gen_tye) )
    | Dec_type name ->
      if verbose then Format.printf "type %s is registered@." name;
      Dec_type name, Env.add_type_const env name
    | Dec_decl (x, ty) ->
      let tye = embed_ty_exn env ty in
      if verbose then Format.printf "val %s: %s@." x (Ast.string_of_ty ty);
      Dec_decl (x, ty), Env.add_var_type_bind env x tye
  in
  { Ast.dec_desc = dec_desc'; dec_loc = dec.dec_loc }, env'
;;

let f_dec_exn ~verbose env dec =
  Level.reset ();
  g_dec_exn ~verbose env dec
;;
