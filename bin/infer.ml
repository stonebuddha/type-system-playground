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
  | Tye_tensor of tyexp * tyexp
  | Tye_lolli of tyexp * tyexp
  | Tye_with of tyexp * tyexp
  | Tye_plus of tyexp * tyexp
  | Tye_diamond
  | Tye_var of tyvar ref

and tyvar =
  | Tyv_link of tyexp
  | Tyv_unbound of Type_id.t

module Env = struct
  type t = tyexp String.Map.t

  let empty = String.Map.empty
  let add_var_type_bind venv x tye = Map.set venv ~key:x ~data:tye
  let find_var_type_bind venv x = Map.find venv x
end

let fresh_var () = Tye_var (ref (Tyv_unbound (Type_id.fresh ())))

let rec embed_ty ty =
  match ty.Ast.ty_desc with
  | Ty_const _ -> assert false
  | Ty_bool -> Tye_bool
  | Ty_list ty0 -> Tye_list (embed_ty ty0)
  | Ty_tensor (ty1, ty2) -> Tye_tensor (embed_ty ty1, embed_ty ty2)
  | Ty_lolli (ty1, ty2) -> Tye_lolli (embed_ty ty1, embed_ty ty2)
  | Ty_with (ty1, ty2) -> Tye_with (embed_ty ty1, embed_ty ty2)
  | Ty_plus (ty1, ty2) -> Tye_plus (embed_ty ty1, embed_ty ty2)
  | Ty_diamond -> Tye_diamond
;;

let rec deref_tye tye =
  let ty_desc =
    match tye with
    | Tye_bool -> Ast.Ty_bool
    | Tye_list tye0 -> Ty_list (deref_tye tye0)
    | Tye_tensor (tye1, tye2) -> Ty_tensor (deref_tye tye1, deref_tye tye2)
    | Tye_lolli (tye1, tye2) -> Ty_lolli (deref_tye tye1, deref_tye tye2)
    | Tye_with (tye1, tye2) -> Ty_with (deref_tye tye1, deref_tye tye2)
    | Tye_plus (tye1, tye2) -> Ty_plus (deref_tye tye1, deref_tye tye2)
    | Tye_diamond -> Ty_diamond
    | Tye_var { contents = Tyv_link tye0 } -> (deref_tye tye0).ty_desc
    | Tye_var { contents = Tyv_unbound id } -> Ty_const ("_weak" ^ Int.to_string id)
  in
  { ty_desc; ty_loc = Location.none }
;;

let rec delink_tye tye =
  match tye with
  | Tye_bool -> Tye_bool
  | Tye_list tye0 -> Tye_list (delink_tye tye0)
  | Tye_tensor (tye1, tye2) -> Tye_tensor (delink_tye tye1, delink_tye tye2)
  | Tye_lolli (tye1, tye2) -> Tye_lolli (delink_tye tye1, delink_tye tye2)
  | Tye_with (tye1, tye2) -> Tye_with (delink_tye tye1, delink_tye tye2)
  | Tye_plus (tye1, tye2) -> Tye_plus (delink_tye tye1, delink_tye tye2)
  | Tye_diamond -> Tye_diamond
  | Tye_var { contents = Tyv_link tye0 } -> delink_tye tye0
  | Tye_var ({ contents = Tyv_unbound _ } as r) -> Tye_var r
;;

let rec occur r1 = function
  | Tye_bool -> false
  | Tye_list tye20 -> occur r1 tye20
  | Tye_tensor (tye21, tye22)
  | Tye_lolli (tye21, tye22)
  | Tye_with (tye21, tye22)
  | Tye_plus (tye21, tye22) -> occur r1 tye21 || occur r1 tye22
  | Tye_diamond -> false
  | Tye_var r2 when phys_equal r1 r2 -> true
  | Tye_var { contents = Tyv_link tye20 } -> occur r1 tye20
  | Tye_var { contents = Tyv_unbound _ } -> false
;;

let rec unify_exn ~loc tye1 tye2 =
  match tye1, tye2 with
  | Tye_bool, Tye_bool -> ()
  | Tye_list tye10, Tye_list tye20 -> unify_exn ~loc tye10 tye20
  | Tye_tensor (tye11, tye12), Tye_tensor (tye21, tye22)
  | Tye_lolli (tye11, tye12), Tye_lolli (tye21, tye22)
  | Tye_with (tye11, tye12), Tye_with (tye21, tye22)
  | Tye_plus (tye11, tye12), Tye_plus (tye21, tye22) ->
    unify_exn ~loc tye11 tye21;
    unify_exn ~loc tye12 tye22
  | Tye_diamond, Tye_diamond -> ()
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
    | Tm_cons (tm0, tm1, tm2) ->
      let tm0', tye0 = g_term_exn env tm0 in
      unify_exn ~loc:tm0.term_loc Tye_diamond tye0;
      let tm1', tye1 = g_term_exn env tm1 in
      let tm2', tye2 = g_term_exn env tm2 in
      unify_exn ~loc:tm2.term_loc (Tye_list tye1) tye2;
      Tm_cons (tm0', tm1', tm2'), Tye_list tye1
    | Tm_iter (tm0, tm1, (d, x, y, tm2)) ->
      let tm0', tye0 = g_term_exn env tm0 in
      let tye = fresh_var () in
      unify_exn ~loc:tm0.term_loc (Tye_list tye) tye0;
      let tm1', tye1 = g_term_exn env tm1 in
      let tm2', tye2 =
        g_term_exn
          (Env.add_var_type_bind
             (Env.add_var_type_bind (Env.add_var_type_bind env d Tye_diamond) x tye)
             y
             tye1)
          tm2
      in
      unify_exn ~loc:tm2.term_loc tye1 tye2;
      Tm_iter (tm0', tm1', (d, x, y, tm2')), tye1
    | Tm_tensor (tm1, tm2) ->
      let tm1', tye1 = g_term_exn env tm1 in
      let tm2', tye2 = g_term_exn env tm2 in
      Tm_tensor (tm1', tm2'), Tye_tensor (tye1, tye2)
    | Tm_letp (tm0, (x1, x2, tm1)) ->
      let tm0', tye0 = g_term_exn env tm0 in
      let tye1 = fresh_var () in
      let tye2 = fresh_var () in
      unify_exn ~loc:tm0.term_loc (Tye_tensor (tye1, tye2)) tye0;
      let tm1', tye1 =
        g_term_exn (Env.add_var_type_bind (Env.add_var_type_bind env x1 tye1) x2 tye2) tm1
      in
      Tm_letp (tm0', (x1, x2, tm1')), tye1
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
  in
  { term_desc = term_desc'; term_ty = tye; term_loc = tm.term_loc }, tye
;;

let g_dec_exn env dec =
  let dec_desc', env' =
    match dec.Ast.dec_desc with
    | Dec_val (x_opt, tm) ->
      let tm', tye = g_term_exn env tm in
      ( Ast.Dec_val (x_opt, Ast.map_ty_term ~f:delink_tye tm')
      , Option.value_map x_opt ~default:env ~f:(fun x -> Env.add_var_type_bind env x tye)
      )
    | Dec_decl (x, ty, _) ->
      let tye = embed_ty ty in
      Dec_decl (x, ty, tye), Env.add_var_type_bind env x tye
  in
  { Ast.dec_desc = dec_desc'; dec_loc = dec.dec_loc }, env'
;;

let f_dec_exn env dec = g_dec_exn env dec
