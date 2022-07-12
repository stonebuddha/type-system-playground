open Core

let rec sym_of_tye tye =
  match tye with
  | Infer.Tye_bool -> "b"
  | Tye_list _ -> "l"
  | Tye_tensor _ -> "t"
  | Tye_lolli _ -> "f"
  | Tye_with _ -> "w"
  | Tye_plus _ -> "p"
  | Tye_var { contents = Tyv_link tye0 } -> sym_of_tye tye0
  | Tye_var { contents = Tyv_unbound _ } -> "c"
;;

let fresh_var =
  let counter = ref 0 in
  fun prefix ->
    let id = !counter in
    Int.incr counter;
    prefix ^ "." ^ Int.to_string id
;;

let insert_shares ~elim_reuse env mk_fv k =
  if not elim_reuse
  then k env env
  else (
    let fv = mk_fv () in
    let binds = Ast.Var_map.to_alist fv in
    let env1, env2, sharings_rev =
      List.fold binds ~init:(env, env, []) ~f:(fun (env1, env2, acc) (x, ty) ->
          let x' = Option.value ~default:x (Map.find env x) in
          let x1 = fresh_var x' in
          let x2 = fresh_var x' in
          ( Map.set env1 ~key:x ~data:x1
          , Map.set env2 ~key:x ~data:x2
          , ((x', ty), x1, x2) :: acc ))
    in
    let tm = k env1 env2 in
    List.fold sharings_rev ~init:tm ~f:(fun acc ((x', ty), x1, x2) ->
        let tm_x =
          { Ast.term_desc = Tm_var x'; term_ty = ty; term_loc = Location.none }
        in
        { Ast.term_desc = Tm_share (tm_x, (x1, x2, acc))
        ; term_ty = acc.term_ty
        ; term_loc = Location.none
        }))
;;

let insert_let tm k =
  match tm.Ast.term_desc with
  | Tm_var _ -> k tm
  | _ ->
    let ty = tm.term_ty in
    let x = fresh_var ("_T" ^ sym_of_tye ty) in
    let tm_x = { Ast.term_desc = Tm_var x; term_ty = ty; term_loc = Location.none } in
    let tm' = k tm_x in
    { Ast.term_desc = Tm_let (tm, (x, tm'))
    ; term_ty = tm'.term_ty
    ; term_loc = Location.none
    }
;;

let rec g_term ~elim_reuse =
  let rec aux env { Ast.term_desc; term_ty; term_loc } =
    let build term_desc = { Ast.term_desc; term_ty; term_loc } in
    match term_desc with
    | Tm_var x -> build (Tm_var (Option.value ~default:x (Map.find env x)))
    | Tm_bool b -> build (Tm_bool b)
    | Tm_cond (tm0, tm1, tm2) ->
      insert_shares
        ~elim_reuse
        env
        (fun () ->
          let fv0 = Ast.free_vars tm0 in
          let fv1 = Ast.free_vars tm1 in
          let fv2 = Ast.free_vars tm2 in
          Ast.Var_map.inter fv0 (Ast.Var_map.union fv1 fv2))
        (fun env1 env2 ->
          insert_let (aux env1 tm0) (fun x0 ->
              build (Tm_cond (x0, aux env2 tm1, aux env2 tm2))))
    | Tm_nil -> build Tm_nil
    | Tm_cons (tm1, tm2) ->
      insert_shares
        ~elim_reuse
        env
        (fun () ->
          let fv1 = Ast.free_vars tm1 in
          let fv2 = Ast.free_vars tm2 in
          Ast.Var_map.inter fv1 fv2)
        (fun env1 env2 ->
          insert_let (aux env1 tm1) (fun x1 ->
              insert_let (aux env2 tm2) (fun x2 -> build (Tm_cons (x1, x2)))))
    | Tm_matl (tm0, tm1, (x, y, tm2)) ->
      insert_shares
        ~elim_reuse
        env
        (fun () ->
          let fv0 = Ast.free_vars tm0 in
          let fv1 = Ast.free_vars tm1 in
          let fv2 = Ast.Var_map.remove_list (Ast.free_vars tm2) [ x; y ] in
          Ast.Var_map.inter fv0 (Ast.Var_map.union fv1 fv2))
        (fun env1 env2 ->
          insert_let (aux env1 tm0) (fun x0 ->
              let x' = fresh_var x in
              let y' = fresh_var y in
              build
                (Tm_matl
                   ( x0
                   , aux env2 tm1
                   , ( x'
                     , y'
                     , aux (Map.set (Map.set env2 ~key:x ~data:x') ~key:y ~data:y') tm2 )
                   ))))
    | Tm_tensor tm0s -> g_terms ~elim_reuse env tm0s (fun x0s -> build (Tm_tensor x0s))
    | Tm_letp (tm0, (xs, tm1)) ->
      insert_shares
        ~elim_reuse
        env
        (fun () ->
          let fv0 = Ast.free_vars tm0 in
          let fv1 = Ast.Var_map.remove_list (Ast.free_vars tm1) xs in
          Ast.Var_map.inter fv0 fv1)
        (fun env1 env2 ->
          insert_let (aux env1 tm0) (fun x0 ->
              let xs' = List.map xs ~f:fresh_var in
              build
                (Tm_letp
                   ( x0
                   , ( xs'
                     , aux
                         (List.fold2_exn xs xs' ~init:env2 ~f:(fun acc x x' ->
                              Map.set acc ~key:x ~data:x'))
                         tm1 ) ))))
    | Tm_abs (x, ty_opt, tm0) ->
      let x' = fresh_var x in
      build (Tm_abs (x', ty_opt, aux (Map.set env ~key:x ~data:x') tm0))
    | Tm_app (tm1, tm2) ->
      insert_shares
        ~elim_reuse
        env
        (fun () ->
          let fv1 = Ast.free_vars tm1 in
          let fv2 = Ast.free_vars tm2 in
          Ast.Var_map.inter fv1 fv2)
        (fun env1 env2 ->
          insert_let (aux env1 tm1) (fun x1 ->
              insert_let (aux env2 tm2) (fun x2 -> build (Tm_app (x1, x2)))))
    | Tm_with (tm1, tm2) -> build (Tm_with (aux env tm1, aux env tm2))
    | Tm_first tm0 -> insert_let (aux env tm0) (fun x0 -> build (Tm_first x0))
    | Tm_second tm0 -> insert_let (aux env tm0) (fun x0 -> build (Tm_second x0))
    | Tm_inl tm0 -> insert_let (aux env tm0) (fun x0 -> build (Tm_inl x0))
    | Tm_inr tm0 -> insert_let (aux env tm0) (fun x0 -> build (Tm_inr x0))
    | Tm_case (tm0, (x1, tm1), (x2, tm2)) ->
      insert_shares
        ~elim_reuse
        env
        (fun () ->
          let fv0 = Ast.free_vars tm0 in
          let fv1 = Ast.Var_map.remove (Ast.free_vars tm1) x1 in
          let fv2 = Ast.Var_map.remove (Ast.free_vars tm2) x2 in
          Ast.Var_map.inter fv0 (Ast.Var_map.union fv1 fv2))
        (fun env1 env2 ->
          insert_let (aux env1 tm0) (fun x0 ->
              let x1' = fresh_var x1 in
              let x2' = fresh_var x2 in
              build
                (Tm_case
                   ( x0
                   , (x1', aux (Map.set env2 ~key:x1 ~data:x1') tm1)
                   , (x2, aux (Map.set env2 ~key:x2 ~data:x2') tm2) ))))
    | Tm_let (tm1, (x, tm2)) ->
      insert_shares
        ~elim_reuse
        env
        (fun () ->
          let fv1 = Ast.free_vars tm1 in
          let fv2 = Ast.Var_map.remove (Ast.free_vars tm2) x in
          Ast.Var_map.inter fv1 fv2)
        (fun env1 env2 ->
          let x' = fresh_var x in
          build (Tm_let (aux env1 tm1, (x', aux (Map.set env2 ~key:x ~data:x') tm2))))
    | Tm_call (f, tm0s) ->
      g_terms ~elim_reuse env tm0s (fun x0s ->
          build (Tm_call (Ast.Call_site.fresh ~fname:f, x0s)))
    | Tm_tick (c, tm0) -> build (Tm_tick (c, aux env tm0))
    | Tm_share (tm0, (x1, x2, tm1)) ->
      insert_shares
        ~elim_reuse
        env
        (fun () ->
          let fv0 = Ast.free_vars tm0 in
          let fv1 = Ast.Var_map.remove_list (Ast.free_vars tm1) [ x1; x2 ] in
          Ast.Var_map.inter fv0 fv1)
        (fun env1 env2 ->
          insert_let (aux env1 tm0) (fun x0 ->
              let x1' = fresh_var x1 in
              let x2' = fresh_var x2 in
              build
                (Tm_share
                   ( x0
                   , ( x1'
                     , x2'
                     , aux
                         (Map.set (Map.set env2 ~key:x1 ~data:x1') ~key:x2 ~data:x2')
                         tm1 ) ))))
  in
  aux

and g_terms ~elim_reuse env tms k =
  let rec aux env xs_rev = function
    | [] -> k (List.rev xs_rev)
    | tms_hd :: tms_tl ->
      insert_shares
        ~elim_reuse
        env
        (fun () ->
          Ast.Var_map.inter
            (Ast.free_vars tms_hd)
            (Ast.Var_map.union_list (List.map tms_tl ~f:Ast.free_vars)))
        (fun env1 env2 ->
          insert_let (g_term ~elim_reuse env1 tms_hd) (fun x ->
              aux env2 (x :: xs_rev) tms_tl))
  in
  aux env [] tms
;;

let g_dec ~elim_reuse { Ast.dec_desc; dec_loc } =
  let build dec_desc = { Ast.dec_desc; dec_loc } in
  match dec_desc with
  | Dec_defn (f, binds, res_ty_opt, ftye, tm) ->
    let env, binds'_rev =
      List.fold binds ~init:(String.Map.empty, []) ~f:(fun (env, acc) (x, ty_opt) ->
          let x' = fresh_var x in
          Map.set env ~key:x ~data:x', (x', ty_opt) :: acc)
    in
    build (Dec_defn (f, List.rev binds'_rev, res_ty_opt, ftye, g_term ~elim_reuse env tm))
;;

let f_dec ~elim_reuse dec = g_dec ~elim_reuse dec
