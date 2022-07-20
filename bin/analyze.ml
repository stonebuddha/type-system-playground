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
      | coefs :: rest ->
        B.update_objective_coefficients lpman coefs;
        if Option.is_none sol_opt
        then (
          B.set_log_level lpman 0;
          if print_stats then Format.printf "%a" B.pp_stats lpman;
          B.initial_solve lpman `Minimize)
        else B.solve_primal lpman `Minimize;
        (match B.status lpman with
        | `Solved ->
          let sol = B.primal_column_solution lpman in
          List.iter coefs ~f:(fun (v, _) -> assert_eq_annot_scalar v (sol v));
          aux (Some sol) rest
        | `Failed -> sol_opt)
    in
    aux None
  ;;

  module Analyzing_context = struct
    type t = Ast.Call_stack.t * int [@@deriving sexp, compare, hash, equal]
  end

  module Env = struct
    type t =
      { binds : analyzing_pure_tyexp String.Map.t
      ; cpot : B.lp_var CI.Map.t
      ; degree : int
      }

    let empty ~degree annot =
      let binds = String.Map.empty in
      let cpot =
        CI.make_cpot ~degree binds ~f:(fun cind ->
            assert (CI.degree cind = 0);
            annot)
      in
      { binds; cpot; degree }
    ;;

    let singleton ~degree x (tye, pot) =
      let binds = String.Map.singleton x tye in
      let cpot =
        CI.make_cpot ~degree binds ~f:(fun cind ->
            let ind_x, cind' = CI.split cind ~on_var:x in
            assert (CI.degree cind' = 0);
            I.Map.find_exn pot ind_x)
      in
      { binds; cpot; degree }
    ;;

    let add_var_type_bind { binds; cpot; degree } x (tye, pot) =
      let binds' = Map.add_exn binds ~key:x ~data:tye in
      let cpot' =
        CI.make_cpot ~degree binds' ~f:(fun cind ->
            let ind_x, cind' = CI.split cind ~on_var:x in
            if CI.degree cind = 0
            then add_annot (I.Map.find_exn pot ind_x) (CI.Map.find_exn cpot cind')
            else if I.degree ind_x = 0
            then CI.Map.find_exn cpot cind'
            else if CI.degree cind' = 0
            then I.Map.find_exn pot ind_x
            else zero_annot)
      in
      { binds = binds'; cpot = cpot'; degree }
    ;;

    let add_var_type_bind_free { binds; cpot; degree } x tye =
      let binds' = Map.add_exn binds ~key:x ~data:tye in
      let cpot' =
        CI.make_cpot ~degree binds' ~f:(fun cind ->
            let ind_x, cind' = CI.split cind ~on_var:x in
            if I.degree ind_x = 0 then CI.Map.find_exn cpot cind' else zero_annot)
      in
      { binds = binds'; cpot = cpot'; degree }
    ;;

    let add_pot_annot_on_star { binds; cpot; degree } annot =
      let cind = CI.star_of binds in
      { binds
      ; cpot =
          CI.Map.set cpot ~key:cind ~data:(add_annot (CI.Map.find_exn cpot cind) annot)
      ; degree
      }
    ;;

    let add_pot_scalar_on_star { binds; cpot; degree } k =
      let cind = CI.star_of binds in
      { binds
      ; cpot =
          CI.Map.set cpot ~key:cind ~data:(add_annot_scalar (CI.Map.find_exn cpot cind) k)
      ; degree
      }
    ;;

    let find_var_type_bind { binds; _ } x = Map.find binds x

    let assert_potential_free { cpot; _ } =
      CI.Map.iter cpot ~f:(fun annot -> assert_eq_annot_scalar annot F.zero)
    ;;

    let join
        { binds = binds1; cpot = cpot1; degree = degree1 }
        { binds = binds2; cpot = cpot2; degree = degree2 }
      =
      assert (degree1 = degree2);
      let binds' =
        Map.merge binds1 binds2 ~f:(fun ~key:_ -> function
          | `Both (tye1, tye2) -> Some (max_tye tye1 tye2)
          | `Left tye1 -> Some tye1
          | `Right tye2 -> Some tye2)
      in
      let xs1 = Map.key_set binds1 in
      let xs2 = Map.key_set binds2 in
      let cpot' =
        CI.make_cpot ~degree:degree1 binds' ~f:(fun cind ->
            let cind1, cind'1 = CI.split_multi cind ~on_vars:xs1 in
            let cind2, cind'2 = CI.split_multi cind ~on_vars:xs2 in
            let annot1 =
              if CI.degree cind'1 = 0 then CI.Map.find_exn cpot1 cind1 else zero_annot
            in
            let annot2 =
              if CI.degree cind'2 = 0 then CI.Map.find_exn cpot2 cind2 else zero_annot
            in
            max_annot annot1 annot2)
      in
      { binds = binds'; cpot = cpot'; degree = degree1 }
    ;;

    let sum_up_inds_on_pot ~degree pot inds =
      List.fold inds ~init:zero_annot ~f:(fun acc ind ->
          if I.degree ind > degree then acc else add_annot acc (I.Map.find_exn pot ind))
    ;;

    let sum_up_inds_on_cpot ~degree ~on cpot cind inds =
      List.fold inds ~init:zero_annot ~f:(fun acc ind ->
          if I.degree ind + CI.degree cind > degree
          then acc
          else add_annot acc (CI.Map.find_exn cpot (CI.extend cind on ind)))
    ;;

    let cons ~degree (tye, pot) ~xh ~xt =
      match tye with
      | Tye_list tye0 ->
        let binds = String.Map.of_alist_exn [ xh, tye0; xt, Tye_list tye0 ] in
        let cpot =
          CI.make_cpot ~degree binds ~f:(fun cind ->
              let ind_xh, cind' = CI.split cind ~on_var:xh in
              let ind_xt, cind'' = CI.split cind' ~on_var:xt in
              assert (CI.degree cind'' = 0);
              sum_up_inds_on_pot ~degree pot (I.shift_cons ind_xh ind_xt))
        in
        { binds; cpot; degree }
      | _ -> assert false
    ;;

    let de_cons { binds; cpot; degree } ~on ~xh ~xt =
      let tye_xh = Map.find_exn binds xh in
      let tye_xt = Map.find_exn binds xt in
      match tye_xt with
      | Tye_list tye_xt0 ->
        assert_eq_tye tye_xh tye_xt0;
        let binds' =
          Map.add_exn
            (Map.remove (Map.remove binds xh) xt)
            ~key:on
            ~data:(Tye_list tye_xh)
        in
        let cpot' = CI.make_cpot ~degree binds' ~f:(fun _ -> new_nonneg_annot ()) in
        CI.Map.iteri cpot ~f:(fun ~key:cind ~data:annot ->
            let ind_xh, cind' = CI.split cind ~on_var:xh in
            let ind_xt, cind'' = CI.split cind' ~on_var:xt in
            assert_ge_annot
              (sum_up_inds_on_cpot ~degree ~on cpot' cind'' (I.shift_cons ind_xh ind_xt))
              annot);
        { binds = binds'; cpot = cpot'; degree }
      | _ -> assert false
    ;;

    let tensor ~degree (tye, pot) ~x0s =
      match tye with
      | Tye_tensor tye0s ->
        let binds =
          String.Map.of_alist_exn
            (List.map2_exn x0s tye0s ~f:(fun x0 (_, tye0) -> x0, tye0))
        in
        let cpot =
          CI.make_cpot ~degree binds ~f:(fun cind ->
              let named_inds_rev, cind' =
                List.fold2_exn
                  x0s
                  tye0s
                  ~init:([], cind)
                  ~f:(fun (acc, cind) x0 (name0, _) ->
                    let ind_x0, cind' = CI.split cind ~on_var:x0 in
                    (name0, ind_x0) :: acc, cind')
              in
              let named_inds = List.rev named_inds_rev in
              assert (CI.degree cind' = 0);
              I.Map.find_exn pot (I.tensor_named named_inds))
        in
        { binds; cpot; degree }
      | _ -> assert false
    ;;

    let de_tensor { binds; cpot; degree } ~on ~xs ~name0s =
      let tye0s = List.zip_exn name0s (List.map xs ~f:(Map.find_exn binds)) in
      let binds' =
        Map.add_exn
          (List.fold xs ~init:binds ~f:Map.remove)
          ~key:on
          ~data:(Tye_tensor tye0s)
      in
      let cpot' = CI.make_cpot ~degree binds' ~f:(fun _ -> new_nonneg_annot ()) in
      CI.Map.iteri cpot ~f:(fun ~key:cind ~data:annot ->
          let named_inds_rev, cind' =
            List.fold2_exn xs tye0s ~init:([], cind) ~f:(fun (acc, cind) x (name0, _) ->
                let ind_x, cind' = CI.split cind ~on_var:x in
                (name0, ind_x) :: acc, cind')
          in
          let named_inds = List.rev named_inds_rev in
          assert_ge_annot
            (CI.Map.find_exn cpot' (CI.extend cind' on (I.tensor_named named_inds)))
            annot);
      { binds = binds'; cpot = cpot'; degree }
    ;;

    let inl ~degree (tye, pot) ~x =
      match tye with
      | Tye_plus (tye1, _) ->
        let binds = String.Map.singleton x tye1 in
        let cpot =
          CI.make_cpot ~degree binds ~f:(fun cind ->
              let ind_x, cind' = CI.split cind ~on_var:x in
              assert (CI.degree cind' = 0);
              sum_up_inds_on_pot ~degree pot (I.shift_inl ind_x))
        in
        { binds; cpot; degree }
      | _ -> assert false
    ;;

    let de_inl { binds; cpot; degree } ~on ~x ~tye_other =
      let tye_x = Map.find_exn binds x in
      let binds' =
        Map.add_exn (Map.remove binds x) ~key:on ~data:(Tye_plus (tye_x, tye_other))
      in
      let cpot' = CI.make_cpot ~degree binds' ~f:(fun _ -> new_nonneg_annot ()) in
      CI.Map.iteri cpot ~f:(fun ~key:cind ~data:annot ->
          let ind_x, cind' = CI.split cind ~on_var:x in
          assert_ge_annot
            (sum_up_inds_on_cpot ~degree ~on cpot' cind' (I.shift_inl ind_x))
            annot);
      { binds = binds'; cpot = cpot'; degree }
    ;;

    let inr ~degree (tye, pot) ~x =
      match tye with
      | Tye_plus (_, tye2) ->
        let binds = String.Map.singleton x tye2 in
        let cpot =
          CI.make_cpot ~degree binds ~f:(fun cind ->
              let ind_x, cind' = CI.split cind ~on_var:x in
              assert (CI.degree cind' = 0);
              sum_up_inds_on_pot ~degree pot (I.shift_inr ind_x))
        in
        { binds; cpot; degree }
      | _ -> assert false
    ;;

    let de_inr { binds; cpot; degree } ~on ~x ~tye_other =
      let tye_x = Map.find_exn binds x in
      let binds' =
        Map.add_exn (Map.remove binds x) ~key:on ~data:(Tye_plus (tye_other, tye_x))
      in
      let cpot' = CI.make_cpot ~degree binds' ~f:(fun _ -> new_nonneg_annot ()) in
      CI.Map.iteri cpot ~f:(fun ~key:cind ~data:annot ->
          let ind_x, cind' = CI.split cind ~on_var:x in
          assert_ge_annot
            (sum_up_inds_on_cpot ~degree ~on cpot' cind' (I.shift_inr ind_x))
            annot);
      { binds = binds'; cpot = cpot'; degree }
    ;;

    let decompose_frames { binds; cpot; degree } ~on:x =
      let pot = ref I.Map.empty in
      let frames = ref CI.Map.empty in
      List.iter (CI.all_cinds_up_to ~degree binds) ~f:(fun cind ->
          let ind_x, cind' = CI.split cind ~on_var:x in
          if CI.degree cind' = 0
          then pot := I.Map.add_exn !pot ~key:ind_x ~data:(CI.Map.find_exn cpot cind)
          else (
            match CI.Map.find !frames cind' with
            | None ->
              frames
                := CI.Map.add_exn
                     !frames
                     ~key:cind'
                     ~data:(I.Map.singleton ind_x (CI.Map.find_exn cpot cind))
            | Some old_pot ->
              frames
                := CI.Map.set
                     !frames
                     ~key:cind'
                     ~data:
                       (I.Map.add_exn
                          old_pot
                          ~key:ind_x
                          ~data:(CI.Map.find_exn cpot cind))));
      !pot, !frames
    ;;

    let combine_frames
        { binds = binds1; cpot = cpot1; degree = degree1 }
        framed_envs
        ~on:x
        { binds = binds2; degree = degree2; _ }
      =
      assert (degree1 = degree2);
      CI.Map.iter framed_envs ~f:(fun framed_env ->
          Map.iter2 binds1 framed_env.binds ~f:(fun ~key:_ ~data ->
              match data with
              | `Both (tye, cf_tye) -> ignore (add_tye_cf tye cf_tye : _)
              | _ -> assert false));
      let binds' =
        Map.merge binds1 (Map.remove binds2 x) ~f:(fun ~key:_ -> function
          | `Both _ -> assert false
          | `Left tye1 -> Some tye1
          | `Right tye2 -> Some tye2)
      in
      let xs1 = Map.key_set binds1 in
      let cpot' =
        CI.make_cpot ~degree:degree1 binds' ~f:(fun cind ->
            let cind1, cind2 = CI.split_multi cind ~on_vars:xs1 in
            if CI.degree cind2 = 0
            then CI.Map.find_exn cpot1 cind1
            else (
              let framed_env = CI.Map.find_exn framed_envs cind2 in
              CI.Map.find_exn framed_env.cpot cind1))
      in
      { binds = binds'; cpot = cpot'; degree = degree1 }
    ;;

    let share { binds; cpot; degree } ~on ~x1 ~x2 =
      let tye1 = Map.find_exn binds x1 in
      let tye2 = Map.find_exn binds x2 in
      assert_eq_tye tye1 tye2;
      let binds' = Map.add_exn (Map.remove (Map.remove binds x1) x2) ~key:on ~data:tye1 in
      let cpot' =
        CI.Map.of_alist_fold
          (List.concat_map (CI.Map.to_alist cpot) ~f:(fun (cind, annot) ->
               let ind1, cind' = CI.split cind ~on_var:x1 in
               let ind2, cind'' = CI.split cind' ~on_var:x2 in
               List.map (I.share ind1 ind2) ~f:(fun (ind, coef) ->
                   CI.extend cind'' on ind, scale_annot (F.of_int coef) annot)))
          ~init:zero_annot
          ~f:add_annot
      in
      { binds = binds'; cpot = cpot'; degree }
    ;;

    let project { binds; cpot; degree } x =
      let binds' = Map.remove binds x in
      let tye = Map.find_exn binds x in
      I.make_pot ~degree tye ~f:(fun ind ->
          let cind = CI.extend (CI.star_of binds') x ind in
          CI.Map.find_exn cpot cind)
    ;;

    let remove_projected_var { binds; cpot; degree } x =
      assert (Map.mem binds x);
      let binds' = Map.remove binds x in
      let cpot' = CI.make_cpot ~degree binds' ~f:(fun _ -> new_nonneg_annot ()) in
      CI.Map.iteri cpot ~f:(fun ~key:cind ~data:annot ->
          let ind_x, cind' = CI.split cind ~on_var:x in
          if I.degree ind_x < CI.degree cind
          then
            if I.degree ind_x > 0
            then assert_eq_annot_scalar annot F.zero
            else assert_eq_annot annot (CI.Map.find_exn cpot' cind')
          else assert_eq_annot_scalar (CI.Map.find_exn cpot' cind') F.zero);
      { binds = binds'; cpot = cpot'; degree }
    ;;

    let project_star { binds; cpot; _ } = CI.Map.find_exn cpot (CI.star_of binds)

    let remove_projected_star { binds; cpot; degree } =
      { binds; cpot = CI.Map.set cpot ~key:(CI.star_of binds) ~data:zero_annot; degree }
    ;;
  end

  let get_var tm =
    match tm.Ast.term_desc with
    | Tm_var x -> x
    | _ -> assert false
  ;;

  let find_var_or_embed env x ~ty ~degree =
    match Env.find_var_type_bind env x with
    | Some tye -> tye, env
    | None ->
      let tye = embed_ty ~degree ty in
      tye, Env.add_var_type_bind_free env x tye
  ;;

  let rec g_term ~degree ~cost_free fdef ctx call_stack =
    let rec aux ((post_tye, post_pot) as post_rtye) tm =
      match tm.Ast.term_desc with
      | Tm_var x -> Env.singleton ~degree x post_rtye
      | Tm_bool _ -> Env.empty ~degree (I.Map.find_exn post_pot (I.star_of post_tye))
      | Tm_cond (tm0, tm1, tm2) ->
        let x0 = get_var tm0 in
        let env1 = aux (post_tye, weaken_pot post_pot) tm1 in
        let env2 = aux (post_tye, weaken_pot post_pot) tm2 in
        Env.add_var_type_bind_free (Env.join env1 env2) x0 Tye_bool
      | Tm_nil -> Env.empty ~degree (I.Map.find_exn post_pot (I.star_of post_tye))
      | Tm_cons (tm1, tm2) ->
        let x1 = get_var tm1 in
        let x2 = get_var tm2 in
        Env.cons ~degree post_rtye ~xh:x1 ~xt:x2
      | Tm_matl (tm0, tm1, (x, y, tm2)) ->
        let x0 = get_var tm0 in
        let env1 = aux (post_tye, weaken_pot post_pot) tm1 in
        let env2 = aux (post_tye, weaken_pot post_pot) tm2 in
        (match tm0.term_ty with
        | Infer.Tye_list ty00 ->
          let tye_x, env2 = find_var_or_embed env2 x ~ty:ty00 ~degree in
          let _, env2 = find_var_or_embed env2 y ~ty:(Tye_list ty00) ~degree in
          Env.join
            (Env.add_var_type_bind_free env1 x0 (Tye_list tye_x))
            (Env.de_cons env2 ~on:x0 ~xh:x ~xt:y)
        | _ -> assert false)
      | Tm_tensor tm0s ->
        let x0s = List.map tm0s ~f:get_var in
        Env.tensor ~degree post_rtye ~x0s
      | Tm_letp (tm0, (xs, tm1)) ->
        let x0 = get_var tm0 in
        let env1 = aux post_rtye tm1 in
        (match tm0.term_ty with
        | Infer.Tye_tensor ty00s ->
          let env1 =
            List.fold2_exn xs ty00s ~init:env1 ~f:(fun acc x ty00 ->
                snd (find_var_or_embed acc x ~ty:ty00 ~degree))
          in
          Env.de_tensor
            env1
            ~on:x0
            ~xs
            ~name0s:(List.mapi ty00s ~f:(fun i _ -> Int.to_string i))
        | _ -> assert false)
      | Tm_abs (x, _, tm0) ->
        (match tm.term_ty, post_tye with
        | Infer.Tye_lolli (ty1, _), Tye_lolli (Tye_fun (rtye1, (tye2, pot2))) ->
          let borrowed_annot = new_nonneg_annot () in
          let env0 =
            aux (tye2, add_pot_annot ~on_ind:(I.star_of tye2) pot2 borrowed_annot) tm0
          in
          let tye_x, env0 = find_var_or_embed env0 x ~ty:ty1 ~degree in
          assert_eq_rtye
            rtye1
            ( tye_x
            , sub_pot_annot ~on_ind:(I.star_of tye_x) (Env.project env0 x) borrowed_annot
            );
          let env0_del_x = Env.remove_projected_var env0 x in
          Env.assert_potential_free env0_del_x;
          Env.add_pot_annot_on_star
            env0_del_x
            (add_annot (I.Map.find_exn post_pot (I.star_of post_tye)) borrowed_annot)
        | _ -> assert false)
      | Tm_app (tm1, tm2) ->
        let x1 = get_var tm1 in
        let x2 = get_var tm2 in
        let arg_tye = embed_ty ~degree tm2.term_ty in
        let arg_pot = new_nonneg_pot ~degree arg_tye in
        let frame = new_nonneg_annot () in
        Env.add_var_type_bind
          (Env.add_var_type_bind_free
             (Env.empty ~degree frame)
             x1
             (Tye_lolli
                (Tye_fun
                   ( (arg_tye, arg_pot)
                   , (post_tye, sub_pot_annot ~on_ind:(I.star_of post_tye) post_pot frame)
                   ))))
          x2
          (arg_tye, arg_pot)
      | Tm_with (tm1, tm2) ->
        (match post_tye with
        | Tye_with
            (Tye_fun ((_, pot11), (tye12, pot12)), Tye_fun ((_, pot21), (tye22, pot22)))
          ->
          let borrowed_annot1 = new_nonneg_annot () in
          let env1 =
            aux (tye12, add_pot_annot ~on_ind:(I.star_of tye12) pot12 borrowed_annot1) tm1
          in
          assert_eq_annot
            (I.Map.find_exn pot11 (I.star_of (Tye_tensor [])))
            (sub_annot (Env.project_star env1) borrowed_annot1);
          let env1 = Env.remove_projected_star env1 in
          Env.assert_potential_free env1;
          let borrowed_annot2 = new_nonneg_annot () in
          let env2 =
            aux (tye22, add_pot_annot ~on_ind:(I.star_of tye22) pot22 borrowed_annot2) tm2
          in
          assert_eq_annot
            (I.Map.find_exn pot21 (I.star_of (Tye_tensor [])))
            (sub_annot (Env.project_star env2) borrowed_annot2);
          let env2 = Env.remove_projected_star env2 in
          Env.assert_potential_free env2;
          Env.add_pot_annot_on_star
            (Env.join env1 env2)
            (add_annot
               (I.Map.find_exn post_pot (I.star_of post_tye))
               (max_annot borrowed_annot1 borrowed_annot2))
        | _ -> assert false)
      | Tm_first tm0 ->
        let x0 = get_var tm0 in
        (match tm0.term_ty with
        | Tye_with (_, ty02) ->
          let arg_pot = new_nonneg_pot ~degree (Tye_tensor []) in
          let frame = new_nonneg_annot () in
          let tye02 = embed_ty ~degree ty02 in
          Env.add_var_type_bind_free
            (Env.empty
               ~degree
               (add_annot (I.Map.find_exn arg_pot (I.star_of (Tye_tensor []))) frame))
            x0
            (Tye_with
               ( Tye_fun
                   ( (Tye_tensor [], arg_pot)
                   , (post_tye, sub_pot_annot ~on_ind:(I.star_of post_tye) post_pot frame)
                   )
               , Tye_fun
                   ( (Tye_tensor [], new_nonneg_pot ~degree (Tye_tensor []))
                   , (tye02, new_nonneg_pot ~degree tye02) ) ))
        | _ -> assert false)
      | Tm_second tm0 ->
        let x0 = get_var tm0 in
        (match tm0.term_ty with
        | Tye_with (ty01, _) ->
          let arg_pot = new_nonneg_pot ~degree (Tye_tensor []) in
          let frame = new_nonneg_annot () in
          let tye01 = embed_ty ~degree ty01 in
          Env.add_var_type_bind_free
            (Env.empty
               ~degree
               (add_annot (I.Map.find_exn arg_pot (I.star_of (Tye_tensor []))) frame))
            x0
            (Tye_with
               ( Tye_fun
                   ( (Tye_tensor [], new_nonneg_pot ~degree (Tye_tensor []))
                   , (tye01, new_nonneg_pot ~degree tye01) )
               , Tye_fun
                   ( (Tye_tensor [], arg_pot)
                   , (post_tye, sub_pot_annot ~on_ind:(I.star_of post_tye) post_pot frame)
                   ) ))
        | _ -> assert false)
      | Tm_inl tm0 ->
        let x0 = get_var tm0 in
        Env.inl ~degree post_rtye ~x:x0
      | Tm_inr tm0 ->
        let x0 = get_var tm0 in
        Env.inr ~degree post_rtye ~x:x0
      | Tm_case (tm0, (x1, tm1), (x2, tm2)) ->
        let x0 = get_var tm0 in
        let env1 = aux (post_tye, weaken_pot post_pot) tm1 in
        let env2 = aux (post_tye, weaken_pot post_pot) tm2 in
        (match tm0.term_ty with
        | Tye_plus (ty01, ty02) ->
          let tye1, env1 = find_var_or_embed env1 x1 ~ty:ty01 ~degree in
          let tye2, env2 = find_var_or_embed env2 x2 ~ty:ty02 ~degree in
          Env.join
            (Env.de_inl env1 ~on:x0 ~x:x1 ~tye_other:tye2)
            (Env.de_inr env2 ~on:x0 ~x:x2 ~tye_other:tye1)
        | _ -> assert false)
      | Tm_let (tm1, (x, tm2)) ->
        let env2 = aux post_rtye tm2 in
        let tye_x, env2 = find_var_or_embed env2 x ~ty:tm1.term_ty ~degree in
        let pot_x, frames = Env.decompose_frames env2 ~on:x in
        let env1 = aux (tye_x, pot_x) tm1 in
        let framed_envs =
          CI.Map.mapi frames ~f:(fun ~key:cind2 ~data:frame_pot_x ->
              let _, frame_tye_x =
                split_tye_cf ~degree:(degree - CI.degree cind2) tye_x
              in
              g_term
                ~degree:(degree - CI.degree cind2)
                ~cost_free:true
                fdef
                (if cost_free then ctx else Hashtbl.create (module Analyzing_context))
                (Ast.Call_stack.empty ~fname:"%anonymous")
                (frame_tye_x, frame_pot_x)
                tm1)
        in
        Env.combine_frames env1 framed_envs ~on:x env2
      | Tm_call (f, tm0s) ->
        let x0s = List.map tm0s ~f:get_var in
        let fname = Ast.Call_site.fname_of_t f in
        let dec = Option.value_exn (Infer.Fundef.find_fun_definition fdef fname) in
        let call_stack' =
          (if cost_free then Ast.Call_stack.extend_k ~k:0 else Ast.Call_stack.extend)
            f
            call_stack
        in
        if cost_free || degree = 1
        then (
          let frame = new_nonneg_annot () in
          let arg_rtye =
            g_dec
              ~degree
              ~cost_free
              fdef
              ctx
              call_stack'
              dec
              (post_tye, sub_pot_annot ~on_ind:(I.star_of post_tye) post_pot frame)
          in
          Env.add_pot_annot_on_star (Env.tensor ~degree arg_rtye ~x0s) frame)
        else (
          let non_cf_post_tye, cf_post_tye = split_tye_cf ~degree:(degree - 1) post_tye in
          let non_cf_post_pot, cf_post_pot = split_pot post_pot in
          let cf_post_pot =
            I.Map.filteri cf_post_pot ~f:(fun ~key:ind ~data:annot ->
                if I.degree ind = degree
                then (
                  assert_eq_annot_scalar annot F.zero;
                  false)
                else true)
          in
          let non_cf_arg_tye, non_cf_arg_pot =
            g_dec
              ~degree
              ~cost_free
              fdef
              ctx
              call_stack'
              dec
              (non_cf_post_tye, non_cf_post_pot)
          in
          let cf_arg_tye, cf_arg_pot =
            g_dec
              ~degree:(degree - 1)
              ~cost_free:true
              fdef
              (Hashtbl.create (module Analyzing_context))
              (Ast.Call_stack.empty ~fname)
              dec
              (cf_post_tye, cf_post_pot)
          in
          Env.tensor
            ~degree
            ( add_tye_cf non_cf_arg_tye cf_arg_tye
            , add_pot_unequal_inds non_cf_arg_pot cf_arg_pot )
            ~x0s)
      | Tm_tick (c, tm0) ->
        if cost_free
        then aux post_rtye tm0
        else Env.add_pot_scalar_on_star (aux post_rtye tm0) (F.of_float c)
      | Tm_share (tm0, (x1, x2, tm1)) ->
        let x0 = get_var tm0 in
        let env1 = aux post_rtye tm1 in
        let _, env1 = find_var_or_embed env1 x1 ~ty:tm0.term_ty ~degree in
        let _, env1 = find_var_or_embed env1 x2 ~ty:tm0.term_ty ~degree in
        Env.share env1 ~on:x0 ~x1 ~x2
    in
    aux

  and g_dec ~degree ~cost_free fdef ctx call_stack dec res_rtye =
    match Hashtbl.find ctx (call_stack, degree) with
    | Some (mk_arg_rtye, rec_res_rtye) ->
      assert_eq_rtye rec_res_rtye res_rtye;
      mk_arg_rtye ()
    | None ->
      (match dec.Ast.dec_desc with
      | Dec_defn (_, binds, _, fty, tm) ->
        let (Infer.Tye_fun (arg_tys, _)) = fty in
        let rec_arg_rtye = ref None in
        let mk_arg_rtye () =
          match !rec_arg_rtye with
          | Some arg_rtye -> arg_rtye
          | None ->
            let arg_tye =
              Tye_tensor
                (List.map2_exn binds arg_tys ~f:(fun (x, _) arg_ty ->
                     x, embed_ty ~degree arg_ty))
            in
            let arg_pot = new_nonneg_pot ~degree arg_tye in
            rec_arg_rtye := Some (arg_tye, arg_pot);
            arg_tye, arg_pot
        in
        Hashtbl.add_exn ctx ~key:(call_stack, degree) ~data:(mk_arg_rtye, res_rtye);
        let env = g_term ~degree ~cost_free fdef ctx call_stack res_rtye tm in
        let env =
          Env.de_tensor
            env
            ~on:"%parameters"
            ~xs:(List.map binds ~f:fst)
            ~name0s:(List.map binds ~f:fst)
        in
        let tye = Option.value_exn (Env.find_var_type_bind env "%parameters") in
        let pot = Env.project env "%parameters" in
        (match !rec_arg_rtye with
        | Some arg_rtye -> assert_eq_rtye arg_rtye (tye, pot)
        | None -> rec_arg_rtye := Some (tye, pot));
        tye, pot)
  ;;
end

let f_dec (solver : (module Potential.BACKEND)) ~verbose ~degree ~print_stats fdef dec =
  let module B = (val solver : Potential.BACKEND) in
  let module M = Make (B) in
  let open M in
  match dec.Ast.dec_desc with
  | Dec_defn (f, _, _, fty, _) ->
    if verbose
    then Format.printf "defn %s: %s@." f (Ast.string_of_fun_ty (Infer.deref_fun_tye fty));
    let (Infer.Tye_fun (_, res_ty)) = fty in
    let res_tye = embed_ty ~degree res_ty in
    let res_pot = new_nonneg_pot ~degree res_tye in
    let arg_rtye =
      g_dec
        ~degree
        ~cost_free:false
        fdef
        (Hashtbl.create (module Analyzing_context))
        (Ast.Call_stack.empty ~fname:f)
        dec
        (res_tye, res_pot)
    in
    let ftye = Tye_fun (arg_rtye, (res_tye, res_pot)) in
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
