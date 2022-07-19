open Core

exception Analysis_error of string * Location.t

let () =
  Location.register_error_of_exn (function
      | Analysis_error (msg, loc) -> Some (Location.errorf ~loc "%s" msg)
      | _ -> None)
;;

module Make (B : Potential.BACKEND) = struct
  module R = Rtype.Make (B)
  include R

  let iteratively_solve ~print_stats =
    let rec aux sol_opt = function
      | [] -> sol_opt
      | coefss_hd :: coefss_tl ->
        B.update_objective_coefficients lpman coefss_hd;
        if Option.is_none sol_opt
        then (
          B.set_log_level lpman 0;
          if print_stats then Format.printf "%a" B.pp_stats lpman;
          B.initial_solve lpman `Minimize)
        else B.solve_primal lpman `Minimize;
        (match B.status lpman with
        | `Solved ->
          let sol = B.primal_column_solution lpman in
          List.iter coefss_hd ~f:(fun (annot, _) ->
              assert_eq_annot_scalar annot (sol annot));
          aux (Some sol) coefss_tl
        | `Failed -> sol_opt)
    in
    aux None
  ;;

  let embed_memo_in_term =
    let rec aux { Ast.term_desc; term_ty; term_loc } =
      let build term_desc =
        { Ast.term_desc
        ; term_ty = term_ty, Hashtbl.create (module Ast.Call_stack)
        ; term_loc
        }
      in
      match term_desc with
      | Tm_var x -> build (Tm_var x)
      | Tm_bool b -> build (Tm_bool b)
      | Tm_cond (tm0, tm1, tm2) -> build (Tm_cond (aux tm0, aux tm1, aux tm2))
      | Tm_nil -> build Tm_nil
      | Tm_cons (tm1, tm2) -> build (Tm_cons (aux tm1, aux tm2))
      | Tm_matl (tm0, tm1, (x, y, tm2)) ->
        build (Tm_matl (aux tm0, aux tm1, (x, y, aux tm2)))
      | Tm_tensor tm0s -> build (Tm_tensor (List.map tm0s ~f:aux))
      | Tm_letp (tm0, (xs, tm1)) -> build (Tm_letp (aux tm0, (xs, aux tm1)))
      | Tm_abs (x, ty_opt, tm0) -> build (Tm_abs (x, ty_opt, aux tm0))
      | Tm_app (tm1, tm2) -> build (Tm_app (aux tm1, aux tm2))
      | Tm_with (tm1, tm2) -> build (Tm_with (aux tm1, aux tm2))
      | Tm_first tm0 -> build (Tm_first (aux tm0))
      | Tm_second tm0 -> build (Tm_second (aux tm0))
      | Tm_inl tm0 -> build (Tm_inl (aux tm0))
      | Tm_inr tm0 -> build (Tm_inr (aux tm0))
      | Tm_case (tm0, (x1, tm1), (x2, tm2)) ->
        build (Tm_case (aux tm0, (x1, aux tm1), (x2, aux tm2)))
      | Tm_let (tm1, (x, tm2)) -> build (Tm_let (aux tm1, (x, aux tm2)))
      | Tm_call (f, tm0s) -> build (Tm_call (f, List.map tm0s ~f:aux))
      | Tm_tick (c, tm0) -> build (Tm_tick (c, aux tm0))
      | Tm_share (tm0, (x1, x2, tm1)) -> build (Tm_share (aux tm0, (x1, x2, aux tm1)))
    in
    aux
  ;;

  let embed_memo_in_dec { Ast.dec_desc; dec_loc } =
    match dec_desc with
    | Dec_defn (f, binds, res_ty_opt, fty, tm) ->
      { Ast.dec_desc = Dec_defn (f, binds, res_ty_opt, fty, embed_memo_in_term tm)
      ; dec_loc
      }
  ;;

  let embed_memo_in_fundef fdef = Map.map fdef ~f:embed_memo_in_dec

  type higher_order_tyexp =
    | HO_const of string
    | HO_bool
    | HO_list of higher_order_tyexp
    | HO_tensor of higher_order_tyexp list
    | HO_lolli of higher_order_fun_tyexp
    | HO_with of higher_order_fun_tyexp * higher_order_fun_tyexp
    | HO_plus of higher_order_tyexp * higher_order_tyexp

  and higher_order_fun_tyexp =
    { fun_arg_ty : Infer.tyexp
    ; fun_res_ty : Infer.tyexp
    ; mutable fun_effect :
        higher_order_tyexp * Ast.Call_stack.t
        -> higher_order_tyexp * (analyzing_rich_tyexp -> analyzing_rich_tyexp)
    ; mutable fun_memo :
        (analyzing_rich_tyexp
        * higher_order_tyexp
        * analyzing_rich_tyexp
        * higher_order_tyexp)
        list
        ref
    }

  let rec embed_ty_as_htye ty =
    let make_fhtye fun_arg_ty fun_res_ty =
      let fun_memo = ref [] in
      let fun_effect (arg_htye, _) =
        let res_htye = embed_ty_as_htye fun_res_ty in
        let comp res_rtye =
          let arg_rtye = embed_ty fun_arg_ty, new_nonneg_annot () in
          fun_memo := (arg_rtye, arg_htye, res_rtye, res_htye) :: !fun_memo;
          arg_rtye
        in
        res_htye, comp
      in
      { fun_arg_ty; fun_res_ty; fun_effect; fun_memo }
    in
    match ty with
    | Infer.Tye_bool -> HO_bool
    | Tye_list ty0 -> HO_list (embed_ty_as_htye ty0)
    | Tye_tensor ty0s -> HO_tensor (List.map ty0s ~f:embed_ty_as_htye)
    | Tye_lolli (ty1, ty2) -> HO_lolli (make_fhtye ty1 ty2)
    | Tye_with (ty1, ty2) ->
      HO_with (make_fhtye (Tye_tensor []) ty1, make_fhtye (Tye_tensor []) ty2)
    | Tye_plus (ty1, ty2) -> HO_plus (embed_ty_as_htye ty1, embed_ty_as_htye ty2)
    | Tye_var { contents = Tyv_link ty0 } -> embed_ty_as_htye ty0
    | Tye_var { contents = Tyv_unbound id } -> HO_const ("_weak" ^ Int.to_string id)
  ;;

  let rec concretize_tye ~wrt:htye tye =
    match tye, htye with
    | Tye_const name1, HO_const name2 when String.(name1 = name2) -> Tye_const name1
    | Tye_bool, HO_bool -> Tye_bool
    | Tye_list (tye0, pot0), HO_list htye0 ->
      Tye_list (concretize_tye ~wrt:htye0 tye0, pot0)
    | Tye_tensor tye0s, HO_tensor htye0s ->
      Tye_tensor
        (List.map2_exn tye0s htye0s ~f:(fun tye0 htye0 -> concretize_tye ~wrt:htye0 tye0))
    | Tye_lolli ftye0, HO_lolli fhtye0 -> Tye_lolli (concretize_ftye ~wrt:fhtye0 ftye0)
    | Tye_with (ftye1, ftye2), HO_with (fhtye1, fhtye2) ->
      Tye_with (concretize_ftye ~wrt:fhtye1 ftye1, concretize_ftye ~wrt:fhtye2 ftye2)
    | Tye_plus ((tye1, pot1), (tye2, pot2)), HO_plus (htye1, htye2) ->
      Tye_plus
        ((concretize_tye ~wrt:htye1 tye1, pot1), (concretize_tye ~wrt:htye2 tye2, pot2))
    | _ -> assert false

  and concretize_ftye ~wrt:fhtye ftye =
    match ftye, fhtye with
    | Tye_fun _, { fun_arg_ty; fun_res_ty; fun_memo; _ } ->
      let memo =
        List.map
          !fun_memo
          ~f:(fun ((arg_tye, arg_pot), arg_htye, (res_tye, res_pot), res_htye) ->
            let arg_tye' = concretize_tye ~wrt:arg_htye arg_tye in
            let res_tye' = concretize_tye ~wrt:res_htye res_tye in
            Tye_fun_concrete ((arg_tye', arg_pot), (res_tye', res_pot)))
      in
      (match memo with
      | [] ->
        Tye_fun_concrete
          ((zero_embed_ty fun_arg_ty, zero_annot), (zero_embed_ty fun_res_ty, zero_annot))
      | memo_hd :: memo_tl ->
        List.iter memo_tl ~f:(assert_eq_ftye memo_hd);
        memo_hd)
    | _ -> assert false
  ;;

  let rec unify_htye htye1 htye2 =
    match htye1, htye2 with
    | HO_const name1, HO_const name2 when String.(name1 = name2) -> ()
    | HO_bool, HO_bool -> ()
    | HO_list htye10, HO_list htye20 -> unify_htye htye10 htye20
    | HO_tensor htye10s, HO_tensor htye20s -> List.iter2_exn htye10s htye20s ~f:unify_htye
    | HO_lolli fhtye10, HO_lolli fhtye20 -> unify_fun_htye fhtye10 fhtye20
    | HO_with (fhtye11, fhtye12), HO_with (fhtye21, fhtye22) ->
      unify_fun_htye fhtye11 fhtye21;
      unify_fun_htye fhtye12 fhtye22
    | HO_plus (htye11, htye12), HO_plus (htye21, htye22) ->
      unify_htye htye11 htye21;
      unify_htye htye12 htye22
    | _ -> assert false

  and unify_fun_htye
      ({ fun_effect = fun_effect1; fun_memo = fun_memo1; _ } as fhtye1)
      ({ fun_effect = fun_effect2; fun_memo = fun_memo2; _ } as fhtye2)
    =
    if phys_equal fun_effect1 fun_effect2
    then assert (phys_equal fun_memo1 fun_memo2)
    else (
      let fun_memo = ref (!fun_memo1 @ !fun_memo2) in
      let fun_effect (arg_htye, call_stack) =
        let res_htye1, comp1 = fun_effect1 (arg_htye, call_stack) in
        let res_htye2, comp2 = fun_effect2 (arg_htye, call_stack) in
        unify_htye res_htye1 res_htye2;
        let comp res_rtye =
          let arg_rtye1 = comp1 res_rtye in
          let arg_rtye2 = comp2 res_rtye in
          assert_eq_rtye arg_rtye1 arg_rtye2;
          fun_memo := (arg_rtye1, arg_htye, res_rtye, res_htye1) :: !fun_memo;
          arg_rtye1
        in
        res_htye1, comp
      in
      fhtye1.fun_effect <- fun_effect;
      fhtye1.fun_memo <- fun_memo;
      fhtye2.fun_effect <- fun_effect;
      fhtye2.fun_memo <- fun_memo)
  ;;

  let rec meet_htye htye1 htye2 =
    match htye1, htye2 with
    | HO_const name1, HO_const name2 when String.(name1 = name2) -> HO_const name1
    | HO_bool, HO_bool -> HO_bool
    | HO_list htye10, HO_list htye20 -> HO_list (meet_htye htye10 htye20)
    | HO_tensor htye10s, HO_tensor htye20s ->
      HO_tensor (List.map2_exn htye10s htye20s ~f:meet_htye)
    | HO_lolli fhtye10, HO_lolli fhtye20 -> HO_lolli (meet_fun_htye fhtye10 fhtye20)
    | HO_with (fhtye11, fhtye12), HO_with (fhtye21, fhtye22) ->
      HO_with (meet_fun_htye fhtye11 fhtye21, meet_fun_htye fhtye12 fhtye22)
    | HO_plus (htye11, htye12), HO_plus (htye21, htye22) ->
      HO_plus (meet_htye htye11 htye21, meet_htye htye12 htye22)
    | _ -> assert false

  and meet_fun_htye
      { fun_arg_ty; fun_res_ty; fun_effect = fun_effect1; _ }
      { fun_effect = fun_effect2; _ }
    =
    let fun_memo = ref [] in
    let fun_effect (arg_htye, call_stack) =
      let res_htye1, comp1 = fun_effect1 (arg_htye, call_stack) in
      let res_htye2, comp2 = fun_effect2 (arg_htye, call_stack) in
      let res_htye = meet_htye res_htye1 res_htye2 in
      let comp res_rtye =
        let arg_rtye1 = comp1 res_rtye in
        let arg_rtye2 = comp2 res_rtye in
        let arg_rtye = max_rtye arg_rtye1 arg_rtye2 in
        fun_memo := (arg_rtye, arg_htye, res_rtye, res_htye) :: !fun_memo;
        arg_rtye
      in
      res_htye, comp
    in
    { fun_arg_ty; fun_res_ty; fun_effect; fun_memo }
  ;;

  module Sigma = struct
    type t = higher_order_tyexp String.Map.t

    let empty = String.Map.empty
    let add_var_type_bind sigma x htye = Map.add_exn sigma ~key:x ~data:htye
    let find_var_type_bind sigma x = Map.find_exn sigma x
  end

  module Env = struct
    type t = analyzing_pure_tyexp String.Map.t

    let empty = String.Map.empty
    let add_var_type_bind env x tye = Map.add_exn env ~key:x ~data:tye
    let find_var_type_bind env x = Map.find env x
    let remove_var_type_bind env x = Map.remove env x
    let assert_potential_free env = Map.iter env ~f:assert_potential_free_tye

    let add env1 env2 =
      Map.merge env1 env2 ~f:(fun ~key:_ -> function
        | `Both _ -> assert false
        | `Left tye1 -> Some tye1
        | `Right tye2 -> Some tye2)
    ;;

    let join env1 env2 =
      Map.merge env1 env2 ~f:(fun ~key:_ -> function
        | `Both (tye1, tye2) -> Some (max_tye tye1 tye2)
        | `Left tye1 -> Some tye1
        | `Right tye2 -> Some tye2)
    ;;
  end

  let get_var tm =
    match tm.Ast.term_desc with
    | Tm_var x -> x
    | _ -> assert false
  ;;

  let find_var_or_embed env x ~ty =
    match Env.find_var_type_bind env x with
    | Some tye -> tye
    | None -> embed_ty ty
  ;;

  let rec g_forward_term fdef ctx call_stack =
    let rec aux sigma tm =
      match Hashtbl.find (snd tm.Ast.term_ty) call_stack with
      | Some htye -> htye
      | None ->
        let htye =
          match tm.term_desc with
          | Tm_var x -> Sigma.find_var_type_bind sigma x
          | Tm_bool _ -> HO_bool
          | Tm_cond (_, tm1, tm2) ->
            let htye1 = aux sigma tm1 in
            let htye2 = aux sigma tm2 in
            meet_htye htye1 htye2
          | Tm_nil -> embed_ty_as_htye (fst tm.term_ty)
          | Tm_cons (tm1, tm2) ->
            let x1 = get_var tm1 in
            let x2 = get_var tm2 in
            let htye1 = Sigma.find_var_type_bind sigma x1 in
            let htye2 = Sigma.find_var_type_bind sigma x2 in
            meet_htye (HO_list htye1) htye2
          | Tm_matl (tm0, tm1, (x, y, tm2)) ->
            let x0 = get_var tm0 in
            let htye0 = Sigma.find_var_type_bind sigma x0 in
            (match htye0 with
            | HO_list htye00 ->
              let htye1 = aux sigma tm1 in
              let htye2 =
                aux
                  (Sigma.add_var_type_bind
                     (Sigma.add_var_type_bind sigma x htye00)
                     y
                     (HO_list htye00))
                  tm2
              in
              meet_htye htye1 htye2
            | _ -> assert false)
          | Tm_tensor tm0s ->
            let x0s = List.map tm0s ~f:get_var in
            HO_tensor (List.map x0s ~f:(Sigma.find_var_type_bind sigma))
          | Tm_letp (tm0, (xs, tm1)) ->
            let x0 = get_var tm0 in
            let htye0 = Sigma.find_var_type_bind sigma x0 in
            (match htye0 with
            | HO_tensor htye00s ->
              aux (List.fold2_exn xs htye00s ~init:sigma ~f:Sigma.add_var_type_bind) tm1
            | _ -> assert false)
          | Tm_abs (x, _, tm0) ->
            (match fst tm.term_ty with
            | Tye_lolli (ty1, ty2) ->
              let fun_memo = ref [] in
              let fun_effect (arg_htye, call_stack) =
                let sigma' = Sigma.add_var_type_bind sigma x arg_htye in
                let res_htye = g_forward_term fdef ctx call_stack sigma' tm0 in
                let comp res_rtye =
                  let env0, pre_pot0 = g_term fdef ctx call_stack sigma' res_rtye tm0 in
                  let tye_x = find_var_or_embed env0 x ~ty:ty1 in
                  let env0_del_x = Env.remove_var_type_bind env0 x in
                  Env.assert_potential_free env0_del_x;
                  let arg_rtye = tye_x, pre_pot0 in
                  fun_memo := (arg_rtye, arg_htye, res_rtye, res_htye) :: !fun_memo;
                  arg_rtye
                in
                res_htye, comp
              in
              HO_lolli { fun_arg_ty = ty1; fun_res_ty = ty2; fun_effect; fun_memo }
            | _ -> assert false)
          | Tm_app (tm1, tm2) ->
            let x1 = get_var tm1 in
            let x2 = get_var tm2 in
            let htye1 = Sigma.find_var_type_bind sigma x1 in
            let htye2 = Sigma.find_var_type_bind sigma x2 in
            (match htye1 with
            | HO_lolli fhtye10 ->
              fst (fhtye10.fun_effect (htye2, Ast.Call_stack.extend x1 call_stack))
            | _ -> assert false)
          | Tm_with (tm1, tm2) ->
            let ty1 = fst tm1.term_ty in
            let fun_memo1 = ref [] in
            let fun_effect1 (arg_htye, call_stack) =
              let res_htye = g_forward_term fdef ctx call_stack sigma tm1 in
              let comp res_rtye =
                let env1, pre_pot1 = g_term fdef ctx call_stack sigma res_rtye tm1 in
                Env.assert_potential_free env1;
                let arg_rtye = Tye_tensor [], pre_pot1 in
                fun_memo1 := (arg_rtye, arg_htye, res_rtye, res_htye) :: !fun_memo1;
                arg_rtye
              in
              res_htye, comp
            in
            let fhtye1 =
              { fun_arg_ty = Tye_tensor []
              ; fun_res_ty = ty1
              ; fun_effect = fun_effect1
              ; fun_memo = fun_memo1
              }
            in
            let ty2 = fst tm2.term_ty in
            let fun_memo2 = ref [] in
            let fun_effect2 (arg_htye, call_stack) =
              let res_htye = g_forward_term fdef ctx call_stack sigma tm2 in
              let comp res_rtye =
                let env2, pre_pot2 = g_term fdef ctx call_stack sigma res_rtye tm2 in
                Env.assert_potential_free env2;
                let arg_rtye = Tye_tensor [], pre_pot2 in
                fun_memo2 := (arg_rtye, arg_htye, res_rtye, res_htye) :: !fun_memo2;
                arg_rtye
              in
              res_htye, comp
            in
            let fhtye2 =
              { fun_arg_ty = Tye_tensor []
              ; fun_res_ty = ty2
              ; fun_effect = fun_effect2
              ; fun_memo = fun_memo2
              }
            in
            HO_with (fhtye1, fhtye2)
          | Tm_first tm0 ->
            let x0 = get_var tm0 in
            let htye0 = Sigma.find_var_type_bind sigma x0 in
            (match htye0 with
            | HO_with (fhtye01, _) ->
              fst (fhtye01.fun_effect (HO_tensor [], Ast.Call_stack.extend x0 call_stack))
            | _ -> assert false)
          | Tm_second tm0 ->
            let x0 = get_var tm0 in
            let htye0 = Sigma.find_var_type_bind sigma x0 in
            (match htye0 with
            | HO_with (_, fhtye02) ->
              fst (fhtye02.fun_effect (HO_tensor [], Ast.Call_stack.extend x0 call_stack))
            | _ -> assert false)
          | Tm_inl tm0 ->
            let x0 = get_var tm0 in
            let htye0 = Sigma.find_var_type_bind sigma x0 in
            (match fst tm.term_ty with
            | Tye_plus (_, ty2) -> HO_plus (htye0, embed_ty_as_htye ty2)
            | _ -> assert false)
          | Tm_inr tm0 ->
            let x0 = get_var tm0 in
            let htye0 = Sigma.find_var_type_bind sigma x0 in
            (match fst tm.term_ty with
            | Tye_plus (ty1, _) -> HO_plus (embed_ty_as_htye ty1, htye0)
            | _ -> assert false)
          | Tm_case (tm0, (x1, tm1), (x2, tm2)) ->
            let x0 = get_var tm0 in
            let htye0 = Sigma.find_var_type_bind sigma x0 in
            (match htye0 with
            | HO_plus (htye01, htye02) ->
              let htye1 = aux (Sigma.add_var_type_bind sigma x1 htye01) tm1 in
              let htye2 = aux (Sigma.add_var_type_bind sigma x2 htye02) tm2 in
              meet_htye htye1 htye2
            | _ -> assert false)
          | Tm_let (tm1, (x, tm2)) ->
            let htye1 = aux sigma tm1 in
            aux (Sigma.add_var_type_bind sigma x htye1) tm2
          | Tm_call (f, tm0s) ->
            let x0s = List.map tm0s ~f:get_var in
            let htye0s = List.map x0s ~f:(Sigma.find_var_type_bind sigma) in
            let fname = Ast.Call_site.fname_of_t f in
            let dec = Option.value_exn (Infer.Fundef.find_fun_definition fdef fname) in
            let call_stack' = Ast.Call_stack.extend f call_stack in
            g_forward_dec fdef ctx call_stack' dec htye0s
          | Tm_tick (_, tm0) -> aux sigma tm0
          | Tm_share (tm0, (x1, x2, tm1)) ->
            let x0 = get_var tm0 in
            let htye0 = Sigma.find_var_type_bind sigma x0 in
            aux
              (Sigma.add_var_type_bind (Sigma.add_var_type_bind sigma x1 htye0) x2 htye0)
              tm1
        in
        Hashtbl.add_exn (snd tm.term_ty) ~key:call_stack ~data:htye;
        htye
    in
    aux

  and g_forward_dec fdef ctx call_stack dec arg_htyes =
    match Hashtbl.find ctx call_stack with
    | Some (_, Some rec_arg_htye, _, Some rec_res_htye) ->
      unify_htye rec_arg_htye (HO_tensor arg_htyes);
      rec_res_htye
    | _ ->
      (match dec.Ast.dec_desc with
      | Dec_defn (_, binds, _, fty, tm) ->
        let (Infer.Tye_fun (_, res_ty)) = fty in
        let rec_res_htye = embed_ty_as_htye res_ty in
        Hashtbl.add_exn
          ctx
          ~key:call_stack
          ~data:(None, Some (HO_tensor arg_htyes), None, Some rec_res_htye);
        let sigma =
          List.fold2_exn binds arg_htyes ~init:Sigma.empty ~f:(fun acc (x, _) arg_htye ->
              Sigma.add_var_type_bind acc x arg_htye)
        in
        let res_htye = g_forward_term fdef ctx call_stack sigma tm in
        unify_htye rec_res_htye res_htye;
        res_htye)

  and g_term fdef ctx call_stack =
    let rec aux sigma ((post_tye, post_pot) as post_rtye) tm =
      match tm.Ast.term_desc with
      | Tm_var x -> Env.add_var_type_bind Env.empty x post_tye, post_pot
      | Tm_bool _ -> Env.empty, post_pot
      | Tm_cond (tm0, tm1, tm2) ->
        let x0 = get_var tm0 in
        let env1, pre_pot1 = aux sigma (post_tye, weaken_annot post_pot) tm1 in
        let env2, pre_pot2 = aux sigma (post_tye, weaken_annot post_pot) tm2 in
        ( Env.add_var_type_bind (Env.join env1 env2) x0 Tye_bool
        , max_annot pre_pot1 pre_pot2 )
      | Tm_nil -> Env.empty, post_pot
      | Tm_cons (tm1, tm2) ->
        let x1 = get_var tm1 in
        let x2 = get_var tm2 in
        (match post_tye with
        | Tye_list ((tye0, pot0) as rtye0) ->
          ( Env.add_var_type_bind
              (Env.add_var_type_bind Env.empty x1 tye0)
              x2
              (Tye_list rtye0)
          , add_annot post_pot pot0 )
        | _ -> assert false)
      | Tm_matl (tm0, tm1, (x, y, tm2)) ->
        let x0 = get_var tm0 in
        let htye0 = Sigma.find_var_type_bind sigma x0 in
        (match fst tm0.term_ty, htye0 with
        | Infer.Tye_list ty00, HO_list htye00 ->
          let env1, pre_pot1 = aux sigma (post_tye, weaken_annot post_pot) tm1 in
          let env2, pre_pot2 =
            aux
              (Sigma.add_var_type_bind
                 (Sigma.add_var_type_bind sigma x htye00)
                 y
                 (HO_list htye00))
              (post_tye, weaken_annot post_pot)
              tm2
          in
          let tye_x = find_var_or_embed env2 x ~ty:ty00 in
          let tye_y = find_var_or_embed env2 y ~ty:(Tye_list ty00) in
          (match tye_y with
          | Tye_list (tye_y0, pot_y0) ->
            assert_eq_tye tye_x tye_y0;
            let pot_x = weaken_annot pot_y0 in
            ( Env.add_var_type_bind
                (Env.join
                   env1
                   (Env.remove_var_type_bind (Env.remove_var_type_bind env2 x) y))
                x0
                (Tye_list (tye_x, pot_x))
            , max_annot pre_pot1 (sub_annot pre_pot2 pot_x) )
          | _ -> assert false)
        | _ -> assert false)
      | Tm_tensor tm0s ->
        let x0s = List.map tm0s ~f:get_var in
        (match post_tye with
        | Tye_tensor tye0s ->
          List.fold2_exn x0s tye0s ~init:Env.empty ~f:Env.add_var_type_bind, post_pot
        | _ -> assert false)
      | Tm_letp (tm0, (xs, tm1)) ->
        let x0 = get_var tm0 in
        let htye0 = Sigma.find_var_type_bind sigma x0 in
        (match fst tm0.term_ty, htye0 with
        | Infer.Tye_tensor ty00s, HO_tensor htye00s ->
          let env1, pre_pot1 =
            aux
              (List.fold2_exn xs htye00s ~init:sigma ~f:Sigma.add_var_type_bind)
              post_rtye
              tm1
          in
          let tye00s =
            List.map2_exn xs ty00s ~f:(fun x ty00 -> find_var_or_embed env1 x ~ty:ty00)
          in
          ( Env.add_var_type_bind
              (List.fold xs ~init:env1 ~f:Env.remove_var_type_bind)
              x0
              (Tye_tensor tye00s)
          , pre_pot1 )
        | _ -> assert false)
      | Tm_abs _ ->
        let fv = Ast.free_vars tm in
        let env =
          Ast.Var_map.fold fv ~init:Env.empty ~f:(fun ~key:x ~data:ty acc ->
              Env.add_var_type_bind acc x (embed_ty (fst ty)))
        in
        env, post_pot
      | Tm_app (tm1, tm2) ->
        let x1 = get_var tm1 in
        let x2 = get_var tm2 in
        let htye1 = Sigma.find_var_type_bind sigma x1 in
        let htye2 = Sigma.find_var_type_bind sigma x2 in
        (match htye1 with
        | HO_lolli fhtye10 ->
          let _, comp = fhtye10.fun_effect (htye2, Ast.Call_stack.extend x1 call_stack) in
          let frame = new_nonneg_annot () in
          let arg_tye, arg_pot = comp (post_tye, sub_annot post_pot frame) in
          ( Env.add_var_type_bind
              (Env.add_var_type_bind
                 Env.empty
                 x1
                 (Tye_lolli (Tye_fun (fst tm2.term_ty, fst tm.term_ty))))
              x2
              arg_tye
          , add_annot arg_pot frame )
        | _ -> assert false)
      | Tm_with (tm1, tm2) ->
        let fv1 = Ast.free_vars tm1 in
        let env1 =
          Ast.Var_map.fold fv1 ~init:Env.empty ~f:(fun ~key:x ~data:ty acc ->
              Env.add_var_type_bind acc x (embed_ty (fst ty)))
        in
        let fv2 = Ast.free_vars tm2 in
        let env2 =
          Ast.Var_map.fold fv2 ~init:Env.empty ~f:(fun ~key:x ~data:ty acc ->
              Env.add_var_type_bind acc x (embed_ty (fst ty)))
        in
        Env.join env1 env2, post_pot
      | Tm_first tm0 ->
        let x0 = get_var tm0 in
        let htye0 = Sigma.find_var_type_bind sigma x0 in
        (match fst tm0.term_ty, htye0 with
        | Tye_with (_, ty02), HO_with (fhtye01, _) ->
          let _, comp =
            fhtye01.fun_effect (HO_tensor [], Ast.Call_stack.extend x0 call_stack)
          in
          let frame = new_nonneg_annot () in
          let _, arg_pot = comp (post_tye, sub_annot post_pot frame) in
          ( Env.add_var_type_bind
              Env.empty
              x0
              (Tye_with
                 (Tye_fun (Tye_tensor [], fst tm.term_ty), Tye_fun (Tye_tensor [], ty02)))
          , add_annot arg_pot frame )
        | _ -> assert false)
      | Tm_second tm0 ->
        let x0 = get_var tm0 in
        let htye0 = Sigma.find_var_type_bind sigma x0 in
        (match fst tm0.term_ty, htye0 with
        | Tye_with (ty01, _), HO_with (_, fhtye02) ->
          let _, comp =
            fhtye02.fun_effect (HO_tensor [], Ast.Call_stack.extend x0 call_stack)
          in
          let frame = new_nonneg_annot () in
          let _, arg_pot = comp (post_tye, sub_annot post_pot frame) in
          ( Env.add_var_type_bind
              Env.empty
              x0
              (Tye_with
                 (Tye_fun (Tye_tensor [], ty01), Tye_fun (Tye_tensor [], fst tm.term_ty)))
          , add_annot arg_pot frame )
        | _ -> assert false)
      | Tm_inl tm0 ->
        let x0 = get_var tm0 in
        (match post_tye with
        | Tye_plus ((tye1, pot1), _) ->
          Env.add_var_type_bind Env.empty x0 tye1, add_annot post_pot pot1
        | _ -> assert false)
      | Tm_inr tm0 ->
        let x0 = get_var tm0 in
        (match post_tye with
        | Tye_plus (_, (tye2, pot2)) ->
          Env.add_var_type_bind Env.empty x0 tye2, add_annot post_pot pot2
        | _ -> assert false)
      | Tm_case (tm0, (x1, tm1), (x2, tm2)) ->
        let x0 = get_var tm0 in
        let htye0 = Sigma.find_var_type_bind sigma x0 in
        (match fst tm0.term_ty, htye0 with
        | Tye_plus (ty01, ty02), HO_plus (htye01, htye02) ->
          let env1, pre_pot1 =
            aux
              (Sigma.add_var_type_bind sigma x1 htye01)
              (post_tye, weaken_annot post_pot)
              tm1
          in
          let env2, pre_pot2 =
            aux
              (Sigma.add_var_type_bind sigma x2 htye02)
              (post_tye, weaken_annot post_pot)
              tm2
          in
          let tye1 = find_var_or_embed env1 x1 ~ty:ty01 in
          let tye2 = find_var_or_embed env2 x2 ~ty:ty02 in
          let pot1 = new_nonneg_annot () in
          let pot2 = new_nonneg_annot () in
          ( Env.add_var_type_bind
              (Env.join
                 (Env.remove_var_type_bind env1 x1)
                 (Env.remove_var_type_bind env2 x2))
              x0
              (Tye_plus ((tye1, pot1), (tye2, pot2)))
          , max_annot (sub_annot pre_pot1 pot1) (sub_annot pre_pot2 pot2) )
        | _ -> assert false)
      | Tm_let (tm1, (x, tm2)) ->
        let htye1 = g_forward_term fdef ctx call_stack sigma tm1 in
        let env2, pre_pot2 = aux (Sigma.add_var_type_bind sigma x htye1) post_rtye tm2 in
        let tye_x = find_var_or_embed env2 x ~ty:(fst tm1.term_ty) in
        let env1, pre_pot1 = aux sigma (tye_x, pre_pot2) tm1 in
        Env.add env1 (Env.remove_var_type_bind env2 x), pre_pot1
      | Tm_call (f, tm0s) ->
        let x0s = List.map tm0s ~f:get_var in
        let htye0s = List.map x0s ~f:(Sigma.find_var_type_bind sigma) in
        let fname = Ast.Call_site.fname_of_t f in
        let dec = Option.value_exn (Infer.Fundef.find_fun_definition fdef fname) in
        let call_stack' = Ast.Call_stack.extend f call_stack in
        let frame = new_nonneg_annot () in
        let (arg_tye, arg_pot), _ =
          g_dec fdef ctx call_stack' dec htye0s (post_tye, sub_annot post_pot frame)
        in
        (match arg_tye with
        | Tye_tensor arg_tye0s ->
          ( List.fold2_exn x0s arg_tye0s ~init:Env.empty ~f:Env.add_var_type_bind
          , add_annot arg_pot frame )
        | _ -> assert false)
      | Tm_tick (c, tm0) ->
        let env0, pre_pot0 = aux sigma post_rtye tm0 in
        env0, add_annot_scalar pre_pot0 (F.of_float c)
      | Tm_share (tm0, (x1, x2, tm1)) ->
        let x0 = get_var tm0 in
        let htye0 = Sigma.find_var_type_bind sigma x0 in
        let env1, pre_pot1 =
          aux
            (Sigma.add_var_type_bind (Sigma.add_var_type_bind sigma x1 htye0) x2 htye0)
            post_rtye
            tm1
        in
        let tye1 = find_var_or_embed env1 x1 ~ty:(fst tm0.term_ty) in
        let tye2 = find_var_or_embed env1 x2 ~ty:(fst tm0.term_ty) in
        ( Env.add_var_type_bind
            (Env.remove_var_type_bind (Env.remove_var_type_bind env1 x1) x2)
            x0
            (add_tye tye1 tye2)
        , pre_pot1 )
    in
    aux

  and g_dec fdef ctx call_stack dec arg_htyes res_rtye =
    let record = Hashtbl.find ctx call_stack in
    match record with
    | Some (Some rec_arg_rtye, Some rec_arg_htye, Some rec_res_rtye, Some rec_res_htye) ->
      unify_htye rec_arg_htye (HO_tensor arg_htyes);
      assert_eq_rtye rec_res_rtye res_rtye;
      rec_arg_rtye, rec_res_htye
    | _ ->
      (match dec.Ast.dec_desc with
      | Dec_defn (_, binds, _, fty, tm) ->
        let (Infer.Tye_fun (arg_tys, res_ty)) = fty in
        let rec_arg_rtye =
          Tye_tensor (List.map arg_tys ~f:embed_ty), new_nonneg_annot ()
        in
        let rec_res_htye =
          match record with
          | Some (_, Some rec_arg_htye, _, Some rec_res_htye) ->
            unify_htye rec_arg_htye (HO_tensor arg_htyes);
            rec_res_htye
          | _ -> embed_ty_as_htye res_ty
        in
        Hashtbl.set
          ctx
          ~key:call_stack
          ~data:
            ( Some rec_arg_rtye
            , Some (HO_tensor arg_htyes)
            , Some res_rtye
            , Some rec_res_htye );
        let sigma =
          List.fold2_exn binds arg_htyes ~init:Sigma.empty ~f:(fun acc (x, _) arg_htye ->
              Sigma.add_var_type_bind acc x arg_htye)
        in
        let res_htye = g_forward_term fdef ctx call_stack sigma tm in
        unify_htye rec_res_htye res_htye;
        let env, pre_pot = g_term fdef ctx call_stack sigma res_rtye tm in
        let tye0s =
          List.map2_exn binds arg_tys ~f:(fun (x, _) arg_ty ->
              find_var_or_embed env x ~ty:arg_ty)
        in
        let tye = Tye_tensor tye0s in
        assert_eq_rtye rec_arg_rtye (tye, pre_pot);
        (tye, pre_pot), res_htye)
  ;;
end

let f_dec (solver : (module Potential.BACKEND)) ~verbose ~degree:_ ~print_stats fdef dec =
  let module B = (val solver : Potential.BACKEND) in
  let module M = Make (B) in
  let open M in
  match dec.Ast.dec_desc with
  | Dec_defn (f, _, _, fty, _) ->
    let fdef = embed_memo_in_fundef fdef in
    let dec = Option.value_exn (Infer.Fundef.find_fun_definition fdef f) in
    if verbose
    then Format.printf "defn %s: %s@." f (Ast.string_of_fun_ty (Infer.deref_fun_tye fty));
    let (Infer.Tye_fun (arg_tys, res_ty)) = fty in
    let arg_htyes = List.map arg_tys ~f:embed_ty_as_htye in
    let res_tye, res_pot = embed_ty res_ty, new_nonneg_annot () in
    let (arg_tye, arg_pot), res_htye =
      g_dec
        fdef
        (Hashtbl.create (module Ast.Call_stack))
        (Ast.Call_stack.empty ~fname:f)
        dec
        arg_htyes
        (res_tye, res_pot)
    in
    let arg_htye = HO_tensor arg_htyes in
    let ftye =
      Tye_fun_concrete
        ( (concretize_tye ~wrt:arg_htye arg_tye, arg_pot)
        , (concretize_tye ~wrt:res_htye res_tye, res_pot) )
    in
    (match
       iteratively_solve
         ~print_stats:(verbose && print_stats)
         (get_coefs_list_for_optimizing_ftye ftye)
     with
    | Some sol ->
      let analyzed_ftye = map_annot_ftye ~f:sol ftye in
      if verbose
      then
        Format.printf
          "aara %s: %s@."
          f
          (string_of_ftye
             ~f:(fun f -> if F.is_zero f then None else Some (F.string_of_t f))
             analyzed_ftye)
    | None ->
      if verbose then Format.eprintf "@{<warning>Error@}: linear programming failed@.")
;;
