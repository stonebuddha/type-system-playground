open Core

exception Type_error of string * Location.t

let () =
  Location.register_error_of_exn (function
      | Type_error (msg, loc) -> Some (Location.errorf ~loc "%s" msg)
      | _ -> None)
;;

module Type_id = struct
  type t = int

  let counter = ref 0

  let fresh () =
    let id = !counter in
    Int.incr counter;
    id
  ;;
end

type tyexp =
  | Tye_bool
  | Tye_list of tyexp
  | Tye_tensor of tyexp list
  | Tye_lolli of tyexp * tyexp
  | Tye_with of tyexp * tyexp
  | Tye_plus of tyexp * tyexp
  | Tye_var of tyvar ref

and tyvar =
  | Tyv_link of tyexp
  | Tyv_unbound of Type_id.t

type fun_tyexp = Tye_fun of tyexp list * tyexp

module Env = struct
  type t = fun_tyexp String.Map.t * tyexp String.Map.t

  let empty = String.Map.empty, String.Map.empty
  let add_fun_type_bind (fenv, venv) f ftye = Map.set fenv ~key:f ~data:ftye, venv
  let find_fun_type_bind (fenv, _) f = Map.find fenv f
  let add_var_type_bind (fenv, venv) x tye = fenv, Map.set venv ~key:x ~data:tye
  let find_var_type_bind (_, venv) x = Map.find venv x
end

module Fundef = struct
  type t = (fun_tyexp, tyexp) Ast.dec String.Map.t

  let empty = String.Map.empty
  let add_fun_definition fdef f dec = Map.set fdef ~key:f ~data:dec
  let find_fun_definition fdef f = Map.find fdef f
end

let fresh_var () = Tye_var (ref (Tyv_unbound (Type_id.fresh ())))

let rec embed_ty ty =
  match ty.Ast.ty_desc with
  | Ty_const _ -> assert false
  | Ty_bool -> Tye_bool
  | Ty_list ty0 -> Tye_list (embed_ty ty0)
  | Ty_tensor tys -> Tye_tensor (List.map tys ~f:embed_ty)
  | Ty_lolli (ty1, ty2) -> Tye_lolli (embed_ty ty1, embed_ty ty2)
  | Ty_with (ty1, ty2) -> Tye_with (embed_ty ty1, embed_ty ty2)
  | Ty_plus (ty1, ty2) -> Tye_plus (embed_ty ty1, embed_ty ty2)
;;

let rec deref_tye tye =
  let ty_desc =
    match tye with
    | Tye_bool -> Ast.Ty_bool
    | Tye_list tye0 -> Ty_list (deref_tye tye0)
    | Tye_tensor tyes -> Ty_tensor (List.map tyes ~f:deref_tye)
    | Tye_lolli (tye1, tye2) -> Ty_lolli (deref_tye tye1, deref_tye tye2)
    | Tye_with (tye1, tye2) -> Ty_with (deref_tye tye1, deref_tye tye2)
    | Tye_plus (tye1, tye2) -> Ty_plus (deref_tye tye1, deref_tye tye2)
    | Tye_var { contents = Tyv_link tye0 } -> (deref_tye tye0).ty_desc
    | Tye_var { contents = Tyv_unbound id } -> Ty_const ("_weak" ^ Int.to_string id)
  in
  { ty_desc; ty_loc = Location.none }
;;

let deref_fun_tye (Tye_fun (arg_tyes, res_tye)) =
  { Ast.fun_ty_desc = List.map arg_tyes ~f:deref_tye, deref_tye res_tye
  ; fun_ty_loc = Location.none
  }
;;

let rec delink_tye tye =
  match tye with
  | Tye_bool -> Tye_bool
  | Tye_list tye0 -> Tye_list (delink_tye tye0)
  | Tye_tensor tyes -> Tye_tensor (List.map tyes ~f:delink_tye)
  | Tye_lolli (tye1, tye2) -> Tye_lolli (delink_tye tye1, delink_tye tye2)
  | Tye_with (tye1, tye2) -> Tye_with (delink_tye tye1, delink_tye tye2)
  | Tye_plus (tye1, tye2) -> Tye_plus (delink_tye tye1, delink_tye tye2)
  | Tye_var { contents = Tyv_link tye0 } -> delink_tye tye0
  | Tye_var ({ contents = Tyv_unbound _ } as r) -> Tye_var r
;;

let delink_fun_tye (Tye_fun (arg_tyes, res_tye)) =
  Tye_fun (List.map arg_tyes ~f:delink_tye, delink_tye res_tye)
;;

let rec occur r1 = function
  | Tye_bool -> false
  | Tye_list tye20 -> occur r1 tye20
  | Tye_tensor tyes2 -> List.exists tyes2 ~f:(occur r1)
  | Tye_lolli (tye21, tye22) | Tye_with (tye21, tye22) | Tye_plus (tye21, tye22) ->
    occur r1 tye21 || occur r1 tye22
  | Tye_var r2 when phys_equal r1 r2 -> true
  | Tye_var { contents = Tyv_link tye20 } -> occur r1 tye20
  | Tye_var { contents = Tyv_unbound _ } -> false
;;

let rec unify_exn ~loc tye1 tye2 =
  match tye1, tye2 with
  | Tye_bool, Tye_bool -> ()
  | Tye_list tye10, Tye_list tye20 -> unify_exn ~loc tye10 tye20
  | Tye_tensor tyes1, Tye_tensor tyes2 ->
    if List.length tyes1 <> List.length tyes2
    then raise @@ Type_error ("tuple length mismatch", loc)
    else List.iter2_exn tyes1 tyes2 ~f:(unify_exn ~loc)
  | Tye_lolli (tye11, tye12), Tye_lolli (tye21, tye22)
  | Tye_with (tye11, tye12), Tye_with (tye21, tye22)
  | Tye_plus (tye11, tye12), Tye_plus (tye21, tye22) ->
    unify_exn ~loc tye11 tye21;
    unify_exn ~loc tye12 tye22
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
;;

let rec g_term_exn env tm =
  let term_desc', tye =
    match tm.Ast.term_desc with
    | Tm_var x ->
      (match Env.find_var_type_bind env x with
      | Some tye -> Ast.Tm_var x, tye
      | None -> raise @@ Type_error ("variable " ^ x ^ " not found", tm.term_loc))
    | Tm_bool b -> Tm_bool b, Tye_bool
    | Tm_cond (tm0, tm1, tm2) ->
      let tm0', tye0 = g_term_exn env tm0 in
      unify_exn ~loc:tm0.term_loc Tye_bool tye0;
      let tm1', tye1 = g_term_exn env tm1 in
      let tm2', tye2 = g_term_exn env tm2 in
      unify_exn ~loc:tm2.term_loc tye1 tye2;
      Tm_cond (tm0', tm1', tm2'), tye1
    | Tm_nil ->
      let tye0 = fresh_var () in
      Tm_nil, Tye_list tye0
    | Tm_cons (tm1, tm2) ->
      let tm1', tye1 = g_term_exn env tm1 in
      let tm2', tye2 = g_term_exn env tm2 in
      unify_exn ~loc:tm2.term_loc (Tye_list tye1) tye2;
      Tm_cons (tm1', tm2'), Tye_list tye1
    | Tm_matl (tm0, tm1, (x, y, tm2)) ->
      let tm0', tye0 = g_term_exn env tm0 in
      let tye = fresh_var () in
      unify_exn ~loc:tm0.term_loc (Tye_list tye) tye0;
      let tm1', tye1 = g_term_exn env tm1 in
      let tm2', tye2 =
        g_term_exn
          (Env.add_var_type_bind (Env.add_var_type_bind env x tye) y (Tye_list tye))
          tm2
      in
      unify_exn ~loc:tm2.term_loc tye1 tye2;
      Tm_matl (tm0', tm1', (x, y, tm2')), tye1
    | Tm_tensor tm0s ->
      let tm'0s, tye0s = List.unzip (List.map tm0s ~f:(g_term_exn env)) in
      Tm_tensor tm'0s, Tye_tensor tye0s
    | Tm_letp (tm0, (xs, tm1)) ->
      let tm0', tye0 = g_term_exn env tm0 in
      let tyes = List.map xs ~f:(fun _ -> fresh_var ()) in
      unify_exn ~loc:tm0.term_loc (Tye_tensor tyes) tye0;
      let tm1', tye1 =
        g_term_exn (List.fold2_exn xs tyes ~init:env ~f:Env.add_var_type_bind) tm1
      in
      Tm_letp (tm0', (xs, tm1')), tye1
    | Tm_abs (x, ty_opt, tm0) ->
      let tye_x =
        match ty_opt with
        | None -> fresh_var ()
        | Some ty -> embed_ty ty
      in
      let tm0', tye0 = g_term_exn (Env.add_var_type_bind env x tye_x) tm0 in
      Tm_abs (x, ty_opt, tm0'), Tye_lolli (tye_x, tye0)
    | Tm_app (tm1, tm2) ->
      let tm1', tye1 = g_term_exn env tm1 in
      let tm2', tye2 = g_term_exn env tm2 in
      let tye_res = fresh_var () in
      unify_exn ~loc:tm1.term_loc (Tye_lolli (tye2, tye_res)) tye1;
      Tm_app (tm1', tm2'), tye_res
    | Tm_with (tm1, tm2) ->
      let tm1', tye1 = g_term_exn env tm1 in
      let tm2', tye2 = g_term_exn env tm2 in
      Tm_with (tm1', tm2'), Tye_with (tye1, tye2)
    | Tm_first tm0 ->
      let tm0', tye0 = g_term_exn env tm0 in
      let tye1 = fresh_var () in
      let tye2 = fresh_var () in
      unify_exn ~loc:tm0.term_loc (Tye_with (tye1, tye2)) tye0;
      Tm_first tm0', tye1
    | Tm_second tm0 ->
      let tm0', tye0 = g_term_exn env tm0 in
      let tye1 = fresh_var () in
      let tye2 = fresh_var () in
      unify_exn ~loc:tm0.term_loc (Tye_with (tye1, tye2)) tye0;
      Tm_second tm0', tye2
    | Tm_inl tm0 ->
      let tm0', tye0 = g_term_exn env tm0 in
      let tye_other = fresh_var () in
      Tm_inl tm0', Tye_plus (tye0, tye_other)
    | Tm_inr tm0 ->
      let tm0', tye0 = g_term_exn env tm0 in
      let tye_other = fresh_var () in
      Tm_inr tm0', Tye_plus (tye_other, tye0)
    | Tm_case (tm0, (x1, tm1), (x2, tm2)) ->
      let tm0', tye0 = g_term_exn env tm0 in
      let tyel = fresh_var () in
      let tyer = fresh_var () in
      unify_exn ~loc:tm0.term_loc (Tye_plus (tyel, tyer)) tye0;
      let tm1', tye1 = g_term_exn (Env.add_var_type_bind env x1 tyel) tm1 in
      let tm2', tye2 = g_term_exn (Env.add_var_type_bind env x2 tyer) tm2 in
      unify_exn ~loc:tm2.term_loc tye1 tye2;
      Tm_case (tm0', (x1, tm1'), (x2, tm2')), tye1
    | Tm_let (tm1, (x, tm2)) ->
      let tm1', tye1 = g_term_exn env tm1 in
      let tm2', tye2 = g_term_exn (Env.add_var_type_bind env x tye1) tm2 in
      Tm_let (tm1', (x, tm2')), tye2
    | Tm_call (f, tm0s) ->
      (match Env.find_fun_type_bind env f with
      | None -> raise @@ Type_error ("function " ^ f ^ " not found", tm.term_loc)
      | Some (Tye_fun (arg_tyes, res_tye)) ->
        if List.length tm0s <> List.length arg_tyes
        then raise @@ Type_error ("arity mismatch", tm.term_loc);
        let tm'0s_rev =
          List.fold (List.zip_exn tm0s arg_tyes) ~init:[] ~f:(fun acc (tm0, arg_tye) ->
              let tm0', tye = g_term_exn env tm0 in
              unify_exn ~loc:tm0.term_loc arg_tye tye;
              tm0' :: acc)
        in
        Tm_call (f, List.rev tm'0s_rev), res_tye)
    | Tm_tick (c, tm0) ->
      let tm0', tye0 = g_term_exn env tm0 in
      Tm_tick (c, tm0'), tye0
    | Tm_share (tm0, (x1, x2, tm1)) ->
      let tm0', tye0 = g_term_exn env tm0 in
      let tm1', tye1 =
        g_term_exn (Env.add_var_type_bind (Env.add_var_type_bind env x1 tye0) x2 tye0) tm1
      in
      Tm_share (tm0', (x1, x2, tm1')), tye1
  in
  { term_desc = term_desc'; term_ty = tye; term_loc = tm.term_loc }, tye
;;

let g_dec_exn env dec =
  let dec_desc', env' =
    match dec.Ast.dec_desc with
    | Dec_defn (f, binds, res_ty_opt, (), tm) ->
      let params, arg_tyes =
        List.unzip
          (List.map binds ~f:(fun (param, arg_ty_opt) ->
               ( param
               , match arg_ty_opt with
                 | None -> fresh_var ()
                 | Some arg_ty -> embed_ty arg_ty )))
      in
      let res_tye =
        match res_ty_opt with
        | None -> fresh_var ()
        | Some res_ty -> embed_ty res_ty
      in
      let ftye = Tye_fun (arg_tyes, res_tye) in
      let env' = Env.add_fun_type_bind env f ftye in
      let env'' = List.fold2_exn params arg_tyes ~init:env' ~f:Env.add_var_type_bind in
      let tm', tye = g_term_exn env'' tm in
      unify_exn ~loc:dec.dec_loc res_tye tye;
      ( Ast.Dec_defn
          (f, binds, res_ty_opt, delink_fun_tye ftye, Ast.map_ty_term ~f:delink_tye tm')
      , env' )
  in
  { Ast.dec_desc = dec_desc'; dec_loc = dec.dec_loc }, env'
;;

let f_dec_exn env dec = g_dec_exn env dec
