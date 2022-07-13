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
    let find_var_type_bind env x = Map.find_exn env x
    let set_var_type_bind env x tye = Map.set env ~key:x ~data:tye
    let remove_var_type_bind env x = Map.remove env x

    let assert_eq env1 env2 =
      Map.iter2 env1 env2 ~f:(fun ~key:_ ~data ->
          match data with
          | `Both (tye1, tye2) -> assert_eq_tye tye1 tye2
          | _ -> assert false)
    ;;

    let meet env1 env2 =
      Map.merge env1 env2 ~f:(fun ~key:_ -> function
        | `Both (tye1, tye2) -> Some (min_tye tye1 tye2)
        | _ -> assert false)
    ;;

    let split env =
      Map.fold
        (Map.map env ~f:split_tye)
        ~init:(empty, empty)
        ~f:(fun ~key:x ~data:(tye1, tye2) (env1, env2) ->
          add_var_type_bind env1 x tye1, add_var_type_bind env2 x tye2)
    ;;
  end

  let get_var tm =
    match tm.Ast.term_desc with
    | Tm_var x -> x
    | _ -> assert false
  ;;

  let find_and_use_var env x =
    let tye = Env.find_var_type_bind env x in
    let tye1, tye2 = split_tye tye in
    tye1, Env.set_var_type_bind env x tye2
  ;;

  let add_back_var env x tye =
    let old_tye = Env.find_var_type_bind env x in
    Env.set_var_type_bind env x (add_tye old_tye tye)
  ;;

  let rec g_term fdef ctx call_stack =
    let rec aux env pre_pot tm =
      match tm.Ast.term_desc with
      | Tm_var x ->
        let tye, env' = find_and_use_var env x in
        (tye, pre_pot), env'
      | Tm_bool _ -> (Tye_bool, pre_pot), env
      | Tm_cond (_, tm1, tm2) ->
        let rtye1, env'1 = aux env pre_pot tm1 in
        let rtye2, env'2 = aux env pre_pot tm2 in
        min_rtye rtye1 rtye2, Env.meet env'1 env'2
      | Tm_nil ->
        let tye = embed_ty tm.term_ty in
        (tye, pre_pot), env
      | Tm_cons (tm1, tm2) ->
        let x1 = get_var tm1 in
        let x2 = get_var tm2 in
        let tye1, env'1 = find_and_use_var env x1 in
        let tye2, env'2 = find_and_use_var env'1 x2 in
        (match tye2 with
        | Tye_list (tye20, pot20) ->
          assert_eq_tye tye1 tye20;
          (Tye_list (tye20, pot20), sub_annot pre_pot pot20), env'2
        | _ -> assert false)
      | Tm_matl (tm0, tm1, (x, y, tm2)) ->
        let x0 = get_var tm0 in
        let tye0, env'0 = find_and_use_var env x0 in
        (match tye0 with
        | Tye_list (tye00, pot00) ->
          let rtye1, env'1 = aux env'0 pre_pot tm1 in
          let env'1 = add_back_var env'1 x0 (Tye_list (tye00, pot00)) in
          let (tye2, pot2), env'2 =
            aux
              (Env.add_var_type_bind
                 (Env.add_var_type_bind env'0 x tye00)
                 y
                 (Tye_list (tye00, pot00)))
              (add_annot pre_pot pot00)
              tm2
          in
          let tye_x_rem = Env.find_var_type_bind env'2 x in
          let tye_y_rem = Env.find_var_type_bind env'2 y in
          let pot_x_rem = new_nonneg_annot () in
          let tye0_back = min_tye tye_y_rem (Tye_list (tye_x_rem, pot_x_rem)) in
          ( min_rtye rtye1 (tye2, sub_annot pot2 pot_x_rem)
          , Env.meet
              env'1
              (add_back_var
                 (Env.remove_var_type_bind (Env.remove_var_type_bind env'2 x) y)
                 x0
                 tye0_back) )
        | _ -> assert false)
      | Tm_tensor tm0s ->
        let x0s = List.map tm0s ~f:get_var in
        let tye0s_rev, env' =
          List.fold x0s ~init:([], env) ~f:(fun (acc, env) x0 ->
              let tye0, env'0 = find_and_use_var env x0 in
              tye0 :: acc, env'0)
        in
        (Tye_tensor (List.rev tye0s_rev), pre_pot), env'
      | Tm_letp (tm0, (xs, tm1)) ->
        let x0 = get_var tm0 in
        let tye0, env'0 = find_and_use_var env x0 in
        (match tye0 with
        | Tye_tensor tye00s ->
          let rtye1, env'1 =
            aux
              (List.fold2_exn xs tye00s ~init:env'0 ~f:Env.add_var_type_bind)
              pre_pot
              tm1
          in
          let tye0_rems = List.map xs ~f:(Env.find_var_type_bind env'1) in
          ( rtye1
          , add_back_var
              (List.fold xs ~init:env'1 ~f:Env.remove_var_type_bind)
              x0
              (Tye_tensor tye0_rems) )
        | _ -> assert false)
      | Tm_abs (x, _, tm0) ->
        (match tm.term_ty with
        | Infer.Tye_lolli (ty1, _) ->
          let tye_x = embed_ty ty1 in
          let pot_x = new_nonneg_annot () in
          let rem_env, borrowed_env = Env.split env in
          let rem_pot, borrowed_pot = split_annot pre_pot in
          let (tye0, pot0), env'0 =
            aux
              (Env.add_var_type_bind borrowed_env x tye_x)
              (add_annot pot_x borrowed_pot)
              tm0
          in
          Env.assert_eq borrowed_env (Env.remove_var_type_bind env'0 x);
          ( ( Tye_lolli
                (Tye_fun
                   ( (tye_x, pot_x)
                   , (tye0, sub_annot pot0 borrowed_pot)
                   , Env.find_var_type_bind env'0 x ))
            , rem_pot )
          , rem_env )
        | _ -> assert false)
      | Tm_app (tm1, tm2) ->
        let x1 = get_var tm1 in
        let x2 = get_var tm2 in
        let tye1, env'1 = find_and_use_var env x1 in
        let tye2, env'2 = find_and_use_var env'1 x2 in
        (match tye1 with
        | Tye_lolli (Tye_fun ((tye11, pot11), (tye12, pot12), tye11_rem)) ->
          assert_eq_tye tye11 tye2;
          let frame = sub_annot pre_pot pot11 in
          (tye12, add_annot pot12 frame), add_back_var env'2 x2 tye11_rem
        | _ -> assert false)
      | Tm_with (tm1, tm2) ->
        let rem_env1, borrowed_env1 = Env.split env in
        let rem_pot1, borrowed_pot1 = split_annot pre_pot in
        let pot11 = new_nonneg_annot () in
        let (tye12, pot12), env'1 =
          aux borrowed_env1 (add_annot pot11 borrowed_pot1) tm1
        in
        Env.assert_eq borrowed_env1 env'1;
        let rem_env2, borrowed_env2 = Env.split env in
        let rem_pot2, borrowed_pot2 = split_annot pre_pot in
        let pot21 = new_nonneg_annot () in
        let (tye22, pot22), env'2 =
          aux borrowed_env2 (add_annot pot21 borrowed_pot2) tm2
        in
        Env.assert_eq borrowed_env2 env'2;
        ( ( Tye_with
              ( Tye_fun
                  ( (Tye_tensor [], pot11)
                  , (tye12, sub_annot pot12 borrowed_pot1)
                  , Tye_tensor [] )
              , Tye_fun
                  ( (Tye_tensor [], pot21)
                  , (tye22, sub_annot pot22 borrowed_pot2)
                  , Tye_tensor [] ) )
          , min_annot rem_pot1 rem_pot2 )
        , Env.meet rem_env1 rem_env2 )
      | Tm_first tm0 ->
        let x0 = get_var tm0 in
        let tye0, env'0 = find_and_use_var env x0 in
        (match tye0 with
        | Tye_with (Tye_fun ((_, pot11), (tye12, pot12), _), _) ->
          let frame = sub_annot pre_pot pot11 in
          (tye12, add_annot pot12 frame), env'0
        | _ -> assert false)
      | Tm_second tm0 ->
        let x0 = get_var tm0 in
        let tye0, env'0 = find_and_use_var env x0 in
        (match tye0 with
        | Tye_with (_, Tye_fun ((_, pot21), (tye22, pot22), _)) ->
          let frame = sub_annot pre_pot pot21 in
          (tye22, add_annot pot22 frame), env'0
        | _ -> assert false)
      | Tm_inl tm0 ->
        let x0 = get_var tm0 in
        let tye0, env'0 = find_and_use_var env x0 in
        (match tm.term_ty with
        | Tye_plus (_, ty2) ->
          let rem_pot, pot1 = split_annot pre_pot in
          (Tye_plus ((tye0, pot1), (embed_ty ty2, new_nonneg_annot ())), rem_pot), env'0
        | _ -> assert false)
      | Tm_inr tm0 ->
        let x0 = get_var tm0 in
        let tye0, env'0 = find_and_use_var env x0 in
        (match tm.term_ty with
        | Tye_plus (ty1, _) ->
          let rem_pot, pot2 = split_annot pre_pot in
          (Tye_plus ((embed_ty ty1, new_nonneg_annot ()), (tye0, pot2)), rem_pot), env'0
        | _ -> assert false)
      | Tm_case (tm0, (x1, tm1), (x2, tm2)) ->
        let x0 = get_var tm0 in
        let tye0, env'0 = find_and_use_var env x0 in
        (match tye0 with
        | Tye_plus ((tye01, pot01), (tye02, pot02)) ->
          let (tye1, pot1), env'1 =
            aux (Env.add_var_type_bind env'0 x1 tye01) (add_annot pre_pot pot01) tm1
          in
          let tye1_rem = Env.find_var_type_bind env'1 x1 in
          let pot1_rem = new_nonneg_annot () in
          let (tye2, pot2), env'2 =
            aux (Env.add_var_type_bind env'0 x2 tye02) (add_annot pre_pot pot02) tm2
          in
          let tye2_rem = Env.find_var_type_bind env'2 x2 in
          let pot2_rem = new_nonneg_annot () in
          ( min_rtye (tye1, sub_annot pot1 pot1_rem) (tye2, sub_annot pot2 pot2_rem)
          , add_back_var
              (Env.meet
                 (Env.remove_var_type_bind env'1 x1)
                 (Env.remove_var_type_bind env'2 x2))
              x0
              (Tye_plus ((tye1_rem, pot1_rem), (tye2_rem, pot2_rem))) )
        | _ -> assert false)
      | Tm_let (tm1, (x, tm2)) ->
        let (tye1, pot1), env'1 = aux env pre_pot tm1 in
        let rtye2, env'2 = aux (Env.add_var_type_bind env'1 x tye1) pot1 tm2 in
        rtye2, Env.remove_var_type_bind env'2 x
      | Tm_call (f, tm0s) ->
        let x0s = List.map tm0s ~f:get_var in
        let fname = Ast.Call_site.fname_of_t f in
        let dec = Option.value_exn (Infer.Fundef.find_fun_definition fdef fname) in
        let call_stack' = Ast.Call_stack.extend f call_stack in
        let tye0s_rev, env' =
          List.fold x0s ~init:([], env) ~f:(fun (acc, env) x0 ->
              let tye0, env'0 = find_and_use_var env x0 in
              tye0 :: acc, env'0)
        in
        let arg_pot, frame = split_annot pre_pot in
        let (res_tye, res_pot), arg_tye_rem =
          g_dec fdef ctx call_stack' dec (List.rev tye0s_rev) arg_pot
        in
        let env' =
          match arg_tye_rem with
          | Tye_tensor arg_tye0_rems ->
            List.fold2_exn x0s arg_tye0_rems ~init:env' ~f:add_back_var
          | _ -> assert false
        in
        (res_tye, add_annot res_pot frame), env'
      | Tm_tick (c, tm0) -> aux env (sub_annot_scalar pre_pot (F.of_float c)) tm0
      | Tm_share _ -> assert false
    in
    aux

  and g_dec fdef ctx call_stack dec arg_tyes arg_pot =
    match Hashtbl.find ctx call_stack with
    | Some (mk_res_rtye_and_arg_tye_rem, rec_arg_rtye) ->
      assert_eq_rtye rec_arg_rtye (Tye_tensor arg_tyes, arg_pot);
      mk_res_rtye_and_arg_tye_rem ()
    | None ->
      (match dec.Ast.dec_desc with
      | Dec_defn (_, binds, _, fty, tm) ->
        let (Infer.Tye_fun (arg_tys, res_ty)) = fty in
        let rec_res_rtye_and_arg_tye_rem = ref None in
        let mk_res_rtye_and_arg_tye_rem () =
          match !rec_res_rtye_and_arg_tye_rem with
          | Some (res_rtye, arg_tye_rem) -> res_rtye, arg_tye_rem
          | None ->
            let res_rtye = embed_ty res_ty, new_nonneg_annot () in
            let arg_tye_rem = Tye_tensor (List.map arg_tys ~f:embed_ty) in
            rec_res_rtye_and_arg_tye_rem := Some (res_rtye, arg_tye_rem);
            res_rtye, arg_tye_rem
        in
        Hashtbl.add_exn
          ctx
          ~key:call_stack
          ~data:(mk_res_rtye_and_arg_tye_rem, (Tye_tensor arg_tyes, arg_pot));
        let env =
          List.fold2_exn binds arg_tyes ~init:Env.empty ~f:(fun env (x, _) arg_tye ->
              Env.add_var_type_bind env x arg_tye)
        in
        let rtye, env' = g_term fdef ctx call_stack env arg_pot tm in
        let tye_rem =
          Tye_tensor (List.map binds ~f:(fun (x, _) -> Env.find_var_type_bind env' x))
        in
        (match !rec_res_rtye_and_arg_tye_rem with
        | Some (res_rtye, arg_tye_rem) ->
          assert_eq_rtye res_rtye rtye;
          assert_eq_tye arg_tye_rem tye_rem
        | None -> rec_res_rtye_and_arg_tye_rem := Some (rtye, tye_rem));
        rtye, tye_rem)
  ;;
end

let f_dec (solver : (module Potential.BACKEND)) ~verbose ~degree:_ ~print_stats fdef dec =
  let module B = (val solver : Potential.BACKEND) in
  let module M = Make (B) in
  let open M in
  match dec.Ast.dec_desc with
  | Dec_defn (f, _, _, fty, _) ->
    if verbose
    then Format.printf "defn %s: %s@." f (Ast.string_of_fun_ty (Infer.deref_fun_tye fty));
    let (Infer.Tye_fun (arg_tys, _)) = fty in
    let arg_tyes = List.map arg_tys ~f:embed_ty in
    let arg_pot = new_nonneg_annot () in
    let res_rtye, arg_tye_rem =
      g_dec
        fdef
        (Hashtbl.create (module Ast.Call_stack))
        (Ast.Call_stack.empty ~fname:f)
        dec
        arg_tyes
        arg_pot
    in
    let ftye = Tye_fun ((Tye_tensor arg_tyes, arg_pot), res_rtye, arg_tye_rem) in
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
