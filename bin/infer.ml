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
  | Tye_const of string
  | Tye_app of tyexp * tyexp list
  | Tye_arrow of tyexp * tyexp
  | Tye_var of tyvar ref

and tyvar =
  | Tyv_link of tyexp
  | Tyv_unbound of Type_id.t

module Env = struct
  type t = String.Set.t * tyexp String.Map.t

  let empty = String.Set.empty, String.Map.empty
  let add_type_const (tenv, venv) name = Set.add tenv name, venv
  let mem_type_const (tenv, _) name = Set.mem tenv name
  let add_var_type_bind (tenv, venv) x tye = tenv, Map.set venv ~key:x ~data:tye
  let find_var_type_bind (_, venv) x = Map.find venv x
end

let fresh_var () = Tye_var (ref (Tyv_unbound (Type_id.fresh ())))

let rec embed_ty_exn env ty =
  match ty.Ast.ty_desc with
  | Ty_const name ->
    if Env.mem_type_const env name
    then Tye_const name
    else raise @@ Type_error ("type constant " ^ name ^ " not found", ty.ty_loc)
  | Ty_app (ty1, ty2s) ->
    Tye_app (embed_ty_exn env ty1, List.map ty2s ~f:(embed_ty_exn env))
  | Ty_arrow (ty1, ty2) -> Tye_arrow (embed_ty_exn env ty1, embed_ty_exn env ty2)
;;

let rec deref_tye tye =
  let ty_desc =
    match tye with
    | Tye_const name -> Ast.Ty_const name
    | Tye_app (tye1, tye2s) -> Ty_app (deref_tye tye1, List.map tye2s ~f:deref_tye)
    | Tye_arrow (tye1, tye2) -> Ty_arrow (deref_tye tye1, deref_tye tye2)
    | Tye_var { contents = Tyv_link tye0 } -> (deref_tye tye0).ty_desc
    | Tye_var { contents = Tyv_unbound id } -> Ty_const ("_weak" ^ Int.to_string id)
  in
  { ty_desc; ty_loc = Location.none }
;;

let rec occur r1 = function
  | Tye_const _ -> false
  | Tye_app (tye21, tye22s) -> occur r1 tye21 || List.exists tye22s ~f:(occur r1)
  | Tye_arrow (tye21, tye22) -> occur r1 tye21 || occur r1 tye22
  | Tye_var r2 when phys_equal r1 r2 -> true
  | Tye_var { contents = Tyv_link tye20 } -> occur r1 tye20
  | Tye_var { contents = Tyv_unbound _ } -> false
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
      let tm1', tye1 = g_term_exn env tm1 in
      let tm2', tye2 = g_term_exn (Env.add_var_type_bind env x tye1) tm2 in
      Tm_let (tm1', (x, tm2')), tye2
  in
  { term_desc = term_desc'; term_ty = tye; term_loc = tm.term_loc }, tye
;;

let g_dec_exn ~verbose env dec =
  let dec_desc', env' =
    match dec.Ast.dec_desc with
    | Dec_val (x_opt, tm) ->
      let tm', tye = g_term_exn env tm in
      if verbose
      then
        Format.printf
          "val %s: %s@."
          (Option.value x_opt ~default:"_")
          (Ast.string_of_ty (deref_tye tye));
      ( Ast.Dec_val (x_opt, Ast.map_ty_term ~f:deref_tye tm')
      , Option.value_map x_opt ~default:env ~f:(fun x -> Env.add_var_type_bind env x tye)
      )
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

let f_dec_exn ~verbose env dec = g_dec_exn ~verbose env dec
