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

  let find_var_or_embed env x ~ty ~degree =
    match Env.find_var_type_bind env x with
    | Some tye -> tye
    | None -> embed_ty ~degree ty
  ;;

  let rec g_term ~degree ~cost_free fdef ctx call_stack =
    let rec aux ((post_tye, post_pot) as post_rtye) tm =
      match tm.Ast.term_desc with
      | Tm_var x -> Env.add_var_type_bind Env.empty x post_tye, post_pot
      | Tm_bool _ -> Env.empty, post_pot
      | Tm_cond (tm0, tm1, tm2) ->
        let x0 = get_var tm0 in
        let env1, pre_pot1 = aux (post_tye, weaken_annot post_pot) tm1 in
        let env2, pre_pot2 = aux (post_tye, weaken_annot post_pot) tm2 in
        ( Env.add_var_type_bind (Env.join env1 env2) x0 Tye_bool
        , max_annot pre_pot1 pre_pot2 )
      | Tm_nil -> Env.empty, post_pot
      | Tm_cons (tm1, tm2) ->
        let x1 = get_var tm1 in
        let x2 = get_var tm2 in
        (match post_tye with
        | Tye_list (qs, tye0) ->
          ( Env.add_var_type_bind
              (Env.add_var_type_bind Env.empty x1 tye0)
              x2
              (Tye_list (shift_annots qs, tye0))
          , add_annot post_pot (List.hd_exn qs) )
        | _ -> assert false)
      | Tm_matl (tm0, tm1, (x, y, tm2)) ->
        let x0 = get_var tm0 in
        let env1, pre_pot1 = aux (post_tye, weaken_annot post_pot) tm1 in
        let env2, pre_pot2 = aux (post_tye, weaken_annot post_pot) tm2 in
        (match tm0.term_ty with
        | Infer.Tye_list ty00 ->
          let tye_x = find_var_or_embed env2 x ~ty:ty00 ~degree in
          let tye_y = find_var_or_embed env2 y ~ty:(Tye_list ty00) ~degree in
          (match tye_y with
          | Tye_list (qs_y0, tye_y0) ->
            assert_eq_tye tye_x tye_y0;
            let qs = new_nonneg_annots ~degree in
            assert_ge_annots (shift_annots qs) qs_y0;
            ( Env.add_var_type_bind
                (Env.join
                   env1
                   (Env.remove_var_type_bind (Env.remove_var_type_bind env2 x) y))
                x0
                (Tye_list (qs, tye_x))
            , max_annot pre_pot1 (sub_annot pre_pot2 (List.hd_exn qs)) )
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
        let env1, pre_pot1 = aux post_rtye tm1 in
        (match tm0.term_ty with
        | Infer.Tye_tensor ty00s ->
          let tye00s =
            List.map2_exn xs ty00s ~f:(fun x ty00 ->
                find_var_or_embed env1 x ~ty:ty00 ~degree)
          in
          ( Env.add_var_type_bind
              (List.fold xs ~init:env1 ~f:Env.remove_var_type_bind)
              x0
              (Tye_tensor tye00s)
          , pre_pot1 )
        | _ -> assert false)
      | Tm_abs (x, _, tm0) ->
        (match tm.term_ty, post_tye with
        | Infer.Tye_lolli (ty1, _), Tye_lolli (Tye_fun (rtye1, (tye2, pot2))) ->
          let borrowed_pot = new_nonneg_annot () in
          let env0, pre_pot0 = aux (tye2, add_annot pot2 borrowed_pot) tm0 in
          let tye_x = find_var_or_embed env0 x ~ty:ty1 ~degree in
          assert_eq_rtye rtye1 (tye_x, sub_annot pre_pot0 borrowed_pot);
          let env0_del_x = Env.remove_var_type_bind env0 x in
          Env.assert_potential_free env0_del_x;
          env0_del_x, add_annot post_pot borrowed_pot
        | _ -> assert false)
      | Tm_app (tm1, tm2) ->
        let x1 = get_var tm1 in
        let x2 = get_var tm2 in
        let arg_tye = embed_ty ~degree tm2.term_ty in
        let arg_pot = new_nonneg_annot () in
        let frame = new_nonneg_annot () in
        ( Env.add_var_type_bind
            (Env.add_var_type_bind
               Env.empty
               x1
               (Tye_lolli
                  (Tye_fun ((arg_tye, arg_pot), (post_tye, sub_annot post_pot frame)))))
            x2
            arg_tye
        , add_annot arg_pot frame )
      | Tm_with (tm1, tm2) ->
        (match post_tye with
        | Tye_with
            (Tye_fun ((_, pot11), (tye12, pot12)), Tye_fun ((_, pot21), (tye22, pot22)))
          ->
          let borrowed_pot1 = new_nonneg_annot () in
          let env1, pre_pot1 = aux (tye12, add_annot pot12 borrowed_pot1) tm1 in
          assert_eq_annot pot11 (sub_annot pre_pot1 borrowed_pot1);
          Env.assert_potential_free env1;
          let borrowed_pot2 = new_nonneg_annot () in
          let env2, pre_pot2 = aux (tye22, add_annot pot22 borrowed_pot2) tm2 in
          assert_eq_annot pot21 (sub_annot pre_pot2 borrowed_pot2);
          Env.assert_potential_free env2;
          Env.join env1 env2, add_annot post_pot (max_annot borrowed_pot1 borrowed_pot2)
        | _ -> assert false)
      | Tm_first tm0 ->
        let x0 = get_var tm0 in
        (match tm0.term_ty with
        | Tye_with (_, ty02) ->
          let arg_pot = new_nonneg_annot () in
          let frame = new_nonneg_annot () in
          ( Env.add_var_type_bind
              Env.empty
              x0
              (Tye_with
                 ( Tye_fun ((Tye_tensor [], arg_pot), (post_tye, sub_annot post_pot frame))
                 , Tye_fun
                     ( (Tye_tensor [], new_nonneg_annot ())
                     , (embed_ty ~degree ty02, new_nonneg_annot ()) ) ))
          , add_annot arg_pot frame )
        | _ -> assert false)
      | Tm_second tm0 ->
        let x0 = get_var tm0 in
        (match tm0.term_ty with
        | Tye_with (ty01, _) ->
          let arg_pot = new_nonneg_annot () in
          let frame = new_nonneg_annot () in
          ( Env.add_var_type_bind
              Env.empty
              x0
              (Tye_with
                 ( Tye_fun
                     ( (Tye_tensor [], new_nonneg_annot ())
                     , (embed_ty ~degree ty01, new_nonneg_annot ()) )
                 , Tye_fun ((Tye_tensor [], arg_pot), (post_tye, sub_annot post_pot frame))
                 ))
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
        let env1, pre_pot1 = aux (post_tye, weaken_annot post_pot) tm1 in
        let env2, pre_pot2 = aux (post_tye, weaken_annot post_pot) tm2 in
        (match tm0.term_ty with
        | Tye_plus (ty01, ty02) ->
          let tye1 = find_var_or_embed env1 x1 ~ty:ty01 ~degree in
          let tye2 = find_var_or_embed env2 x2 ~ty:ty02 ~degree in
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
        let env2, pre_pot2 = aux post_rtye tm2 in
        let tye_x = find_var_or_embed env2 x ~ty:tm1.term_ty ~degree in
        let env1, pre_pot1 = aux (tye_x, pre_pot2) tm1 in
        Env.add env1 (Env.remove_var_type_bind env2 x), pre_pot1
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
          let arg_tye, arg_pot =
            g_dec
              ~degree
              ~cost_free
              fdef
              ctx
              call_stack'
              dec
              (post_tye, sub_annot post_pot frame)
          in
          match arg_tye with
          | Tye_tensor arg_tye0s ->
            ( List.fold2_exn x0s arg_tye0s ~init:Env.empty ~f:Env.add_var_type_bind
            , add_annot arg_pot frame )
          | _ -> assert false)
        else (
          let non_cf_post_tye, cf_post_tye = split_tye_cf post_tye in
          let non_cf_post_pot, cf_post_pot = split_annot post_pot in
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
              (Hashtbl.create (module Ast.Call_stack))
              (Ast.Call_stack.empty ~fname)
              dec
              (cf_post_tye, cf_post_pot)
          in
          match add_tye_cf non_cf_arg_tye cf_arg_tye with
          | Tye_tensor arg_tye0s ->
            ( List.fold2_exn x0s arg_tye0s ~init:Env.empty ~f:Env.add_var_type_bind
            , add_annot non_cf_arg_pot cf_arg_pot )
          | _ -> assert false)
      | Tm_tick (c, tm0) ->
        if cost_free
        then aux post_rtye tm0
        else (
          let env0, pre_pot0 = aux post_rtye tm0 in
          env0, add_annot_scalar pre_pot0 (F.of_float c))
      | Tm_share (tm0, (x1, x2, tm1)) ->
        let x0 = get_var tm0 in
        let env1, pre_pot1 = aux post_rtye tm1 in
        let tye1 = find_var_or_embed env1 x1 ~ty:tm0.term_ty ~degree in
        let tye2 = find_var_or_embed env1 x2 ~ty:tm0.term_ty ~degree in
        ( Env.add_var_type_bind
            (Env.remove_var_type_bind (Env.remove_var_type_bind env1 x1) x2)
            x0
            (add_tye tye1 tye2)
        , pre_pot1 )
    in
    aux

  and g_dec ~degree ~cost_free fdef ctx call_stack dec res_rtye =
    match Hashtbl.find ctx call_stack with
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
            let arg_rtye =
              Tye_tensor (List.map arg_tys ~f:(embed_ty ~degree)), new_nonneg_annot ()
            in
            rec_arg_rtye := Some arg_rtye;
            arg_rtye
        in
        Hashtbl.add_exn ctx ~key:call_stack ~data:(mk_arg_rtye, res_rtye);
        let env, pre_pot = g_term ~degree ~cost_free fdef ctx call_stack res_rtye tm in
        let tye0s =
          List.map2_exn binds arg_tys ~f:(fun (x, _) arg_ty ->
              find_var_or_embed env x ~ty:arg_ty ~degree)
        in
        let tye = Tye_tensor tye0s in
        (match !rec_arg_rtye with
        | Some arg_rtye -> assert_eq_rtye arg_rtye (tye, pre_pot)
        | None -> rec_arg_rtye := Some (tye, pre_pot));
        tye, pre_pot)
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
    let res_rtye = embed_ty ~degree res_ty, new_nonneg_annot () in
    let arg_rtye =
      g_dec
        ~degree
        ~cost_free:false
        fdef
        (Hashtbl.create (module Ast.Call_stack))
        (Ast.Call_stack.empty ~fname:f)
        dec
        res_rtye
    in
    let ftye = Tye_fun (arg_rtye, res_rtye) in
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
