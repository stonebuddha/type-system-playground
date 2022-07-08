open Core

exception Analysis_error of string * Location.t

let () =
  Location.register_error_of_exn (function
      | Analysis_error (msg, loc) -> Some (Location.errorf ~loc "%s" msg)
      | _ -> None)
;;

type tyexp = Infer.tyexp

module Env = struct
  type t = tyexp option list String.Map.t

  let empty = String.Map.empty
  let add_var_type_bind venv x tye = Map.add_multi venv ~key:x ~data:(Some tye)
  let find_var_type_bind venv x = List.hd_exn (Map.find_multi venv x)
  let use_var_type_bind venv x = Map.add_multi (Map.remove_multi venv x) ~key:x ~data:None
  let remove_var_type_bind venv x = Map.remove_multi venv x

  let meet_var_type_binds venv1 venv2 =
    Map.merge venv1 venv2 ~f:(fun ~key:_ -> function
      | `Both (tye_opts1, tye_opts2) ->
        Some
          (List.map2_exn tye_opts1 tye_opts2 ~f:(fun tye_opt1 tye_opt2 ->
               match tye_opt1, tye_opt2 with
               | Some tye1, Some _ -> Some tye1
               | _ -> None))
      | _ -> assert false)
  ;;
end

let heap_free tye =
  let rec aux = function
    | Infer.Tye_bool -> true
    | Tye_list _ -> false
    | Tye_tensor (tye1, tye2) -> aux tye1 && aux tye2
    | Tye_lolli (_, _) -> false
    | Tye_with _ -> false
    | Tye_plus (tye1, tye2) -> aux tye1 && aux tye2
    | Tye_var { contents = Tyv_link tye0 } -> aux tye0
    | Tye_var { contents = Tyv_unbound _ } -> false
  in
  aux tye
;;

let rec g_term_exn env tm =
  match tm.Ast.term_desc with
  | Tm_var x ->
    (match Env.find_var_type_bind env x with
    | Some tye -> if heap_free tye then env else Env.use_var_type_bind env x
    | None -> raise @@ Analysis_error ("variable " ^ x ^ " has been used", tm.term_loc))
  | Tm_bool _ -> env
  | Tm_cond (tm0, tm1, tm2) ->
    let env'0 = g_term_exn env tm0 in
    let env'1 = g_term_exn env'0 tm1 in
    let env'2 = g_term_exn env'0 tm2 in
    Env.meet_var_type_binds env'1 env'2
  | Tm_nil -> env
  | Tm_cons (tm1, tm2) ->
    let env'1 = g_term_exn env tm1 in
    let env'2 = g_term_exn env'1 tm2 in
    env'2
  | Tm_matl (tm0, tm1, (x, y, tm2)) ->
    let env'0 = g_term_exn env tm0 in
    let env'1 = g_term_exn env'0 tm1 in
    (match tm0.term_ty with
    | Infer.Tye_list tye ->
      let env'2 =
        g_term_exn
          (Env.add_var_type_bind (Env.add_var_type_bind env'0 x tye) y (Tye_list tye))
          tm2
      in
      Env.meet_var_type_binds
        env'1
        (Env.remove_var_type_bind (Env.remove_var_type_bind env'2 y) x)
    | _ -> assert false)
  | Tm_tensor (tm1, tm2) ->
    let env'1 = g_term_exn env tm1 in
    let env'2 = g_term_exn env'1 tm2 in
    env'2
  | Tm_letp (tm0, (x1, x2, tm1)) ->
    let env'0 = g_term_exn env tm0 in
    (match tm0.term_ty with
    | Tye_tensor (tye1, tye2) ->
      let env'1 =
        g_term_exn
          (Env.add_var_type_bind (Env.add_var_type_bind env'0 x1 tye1) x2 tye2)
          tm1
      in
      Env.remove_var_type_bind (Env.remove_var_type_bind env'1 x2) x1
    | _ -> assert false)
  | Tm_abs (x, _, tm0) ->
    (match tm.term_ty with
    | Tye_lolli (tye, _) ->
      let env' = g_term_exn (Env.add_var_type_bind env x tye) tm0 in
      let env'' = Env.remove_var_type_bind env' x in
      env''
    | _ -> assert false)
  | Tm_app (tm1, tm2) ->
    let env'1 = g_term_exn env tm1 in
    let env'2 = g_term_exn env'1 tm2 in
    env'2
  | Tm_with (tm1, tm2) ->
    let env'1 = g_term_exn env tm1 in
    let env'2 = g_term_exn env tm2 in
    Env.meet_var_type_binds env'1 env'2
  | Tm_first tm0 ->
    let env' = g_term_exn env tm0 in
    env'
  | Tm_second tm0 ->
    let env' = g_term_exn env tm0 in
    env'
  | Tm_inl tm0 ->
    let env' = g_term_exn env tm0 in
    env'
  | Tm_inr tm0 ->
    let env' = g_term_exn env tm0 in
    env'
  | Tm_case (tm0, (x1, tm1), (x2, tm2)) ->
    let env'0 = g_term_exn env tm0 in
    (match tm0.term_ty with
    | Tye_plus (tye1, tye2) ->
      let env'1 = g_term_exn (Env.add_var_type_bind env'0 x1 tye1) tm1 in
      let env'2 = g_term_exn (Env.add_var_type_bind env'0 x2 tye2) tm2 in
      Env.meet_var_type_binds
        (Env.remove_var_type_bind env'1 x1)
        (Env.remove_var_type_bind env'2 x2)
    | _ -> assert false)
  | Tm_let (tm1, (x, tm2)) ->
    let env'1 = g_term_exn env tm1 in
    let env'2 = g_term_exn (Env.add_var_type_bind env'1 x tm1.term_ty) tm2 in
    Env.remove_var_type_bind env'2 x
  | Tm_call (_, tm0s) -> List.fold tm0s ~init:env ~f:g_term_exn
;;

let g_dec_exn ~verbose dec =
  match dec.Ast.dec_desc with
  | Dec_defn (f, binds, _, ftye, tm) ->
    let params = List.map binds ~f:fst in
    let (Infer.Tye_fun (arg_tyes, _)) = ftye in
    let env = List.fold2_exn params arg_tyes ~init:Env.empty ~f:Env.add_var_type_bind in
    let (_ : _) = g_term_exn env tm in
    if verbose
    then Format.printf "defn %s: %s@." f (Ast.string_of_fun_ty (Infer.deref_fun_tye ftye))
;;

let f_dec_exn ~verbose dec = g_dec_exn ~verbose dec
