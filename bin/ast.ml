open Core

type ty =
  { ty_desc : ty_desc
  ; ty_loc : Location.t
  }

and ty_desc =
  | Ty_const of string (** type constant: _weak42 *)
  | Ty_bool (** Boolean type: bool *)
  | Ty_list of ty (** list type: list(t0) *)
  | Ty_tensor of ty list (** multiplicative conjunction: t1 * t2 *)
  | Ty_lolli of ty * ty (** multiplicative disjunction: t1 -o t2 *)
  | Ty_with of ty * ty (** additive conjunction: t1 & t2 *)
  | Ty_plus of ty * ty (** additive disjunction: t1 + t2 *)

(** toplevel function type: (t1, t2) -> t0 *)
type fun_ty =
  { fun_ty_desc : ty list * ty
  ; fun_ty_loc : Location.t
  }

type 'ty term =
  { term_desc : 'ty term_desc
  ; term_ty : 'ty
  ; term_loc : Location.t
  }

and 'ty term_desc =
  | Tm_var of string (** variable: x *)
  | Tm_bool of bool (** Boolean constant: true, false *)
  | Tm_cond of 'ty term * 'ty term * 'ty term (** conditional: if e0 then e1 else e2 *)
  | Tm_nil (** empty list: nil) *)
  | Tm_cons of 'ty term * 'ty term (** cons list: cons(e1, e2) *)
  | Tm_matl of 'ty term * 'ty term * (string * string * 'ty term)
      (** list elimination: case e0 ( nil -> e1 | cons(x, y) -> e2 ) *)
  | Tm_tensor of 'ty term list (** tensor introduction: e1 * e2 *)
  | Tm_letp of 'ty term * (string list * 'ty term)
      (** tensor elimination: let x1 * x2 = e0 in e1 *)
  | Tm_abs of string * ty option * 'ty term (** lolli introduction: fun x -> e0 *)
  | Tm_app of 'ty term * 'ty term (** lolli elimination: e_1(e_2) *)
  | Tm_with of 'ty term * 'ty term (** with introduction: e1 & e2 *)
  | Tm_first of 'ty term (** with elimination (left): e0.l *)
  | Tm_second of 'ty term (** with elimination (right): e0.r *)
  | Tm_inl of 'ty term (** plus introduction (left): inl e0 *)
  | Tm_inr of 'ty term (** plus introduction (right): inr e0 *)
  | Tm_case of 'ty term * (string * 'ty term) * (string * 'ty term)
      (** plus elimination: case e0 ( inl x1 -> e1 | inr x2 -> e2 ) *)
  | Tm_let of 'ty term * (string * 'ty term) (** let: let x = e_1 in e_2 *)
  | Tm_call of string * 'ty term list (** function call: f(e1, e2, e3) *)
  | Tm_tick of float * 'ty term (** resource annotation: tick(1.0); e0 *)
  | Tm_share of 'ty term * (string * string * 'ty term)
      (** sharing: share e0 as x1 and x2 in e1  *)

type untyped_term = unit term
type typed_term = ty term

type ('fun_ty, 'ty) dec =
  { dec_desc : ('fun_ty, 'ty) dec_desc
  ; dec_loc : Location.t
  }

and ('fun_ty, 'ty) dec_desc =
  | Dec_defn of string * (string * ty option) list * ty option * 'fun_ty * 'ty term

type untyped_dec = (unit, unit) dec
type typed_dec = (fun_ty, ty) dec

type cmd =
  | Cmd_dec of untyped_dec
  | Cmd_show_type of string
  | Cmd_use_solver of string
  | Cmd_analyze of string
  | Cmd_set_degree of int
  | Cmd_print_stats of bool

let string_of_ty =
  let rec aux ty =
    match ty.ty_desc with
    | Ty_lolli (ty1, ty2) -> aux_tensor ty1 ^ " -o " ^ aux ty2
    | _ -> aux_tensor ty
  and aux_tensor ty =
    match ty.ty_desc with
    | Ty_tensor ty0s -> String.concat ~sep:" * " (List.map ty0s ~f:aux_additive)
    | _ -> aux_additive ty
  and aux_additive ty =
    match ty.ty_desc with
    | Ty_with (ty1, ty2) -> aux_simple ty1 ^ " & " ^ aux_additive ty2
    | Ty_plus (ty1, ty2) -> aux_simple ty1 ^ " + " ^ aux_additive ty2
    | _ -> aux_simple ty
  and aux_simple ty =
    match ty.ty_desc with
    | Ty_const name -> name
    | Ty_bool -> "bool"
    | Ty_list ty0 -> "list(" ^ aux ty0 ^ ")"
    | _ -> "(" ^ aux ty ^ ")"
  in
  aux
;;

let string_of_fun_ty { fun_ty_desc = arg_tys, res_ty; _ } =
  (match arg_tys with
  | [ arg_ty ] -> string_of_ty arg_ty
  | _ -> "(" ^ String.concat ~sep:", " (List.map arg_tys ~f:string_of_ty) ^ ")")
  ^ " -> "
  ^ string_of_ty res_ty
;;

let map_ty_term ~f =
  let rec aux { term_desc; term_ty; term_loc } =
    { term_desc =
        (match term_desc with
        | Tm_var x -> Tm_var x
        | Tm_bool b -> Tm_bool b
        | Tm_cond (tm0, tm1, tm2) -> Tm_cond (aux tm0, aux tm1, aux tm2)
        | Tm_nil -> Tm_nil
        | Tm_cons (tm1, tm2) -> Tm_cons (aux tm1, aux tm2)
        | Tm_matl (tm0, tm1, (x, y, tm2)) -> Tm_matl (aux tm0, aux tm1, (x, y, aux tm2))
        | Tm_tensor tms -> Tm_tensor (List.map tms ~f:aux)
        | Tm_letp (tm0, (xs, tm1)) -> Tm_letp (aux tm0, (xs, aux tm1))
        | Tm_abs (x, ty_opt, tm0) -> Tm_abs (x, ty_opt, aux tm0)
        | Tm_app (tm1, tm2) -> Tm_app (aux tm1, aux tm2)
        | Tm_with (tm1, tm2) -> Tm_with (aux tm1, aux tm2)
        | Tm_first tm0 -> Tm_first (aux tm0)
        | Tm_second tm0 -> Tm_second (aux tm0)
        | Tm_inl tm0 -> Tm_inl (aux tm0)
        | Tm_inr tm0 -> Tm_inr (aux tm0)
        | Tm_case (tm0, (x1, tm1), (x2, tm2)) ->
          Tm_case (aux tm0, (x1, aux tm1), (x2, aux tm2))
        | Tm_let (tm1, (x, tm2)) -> Tm_let (aux tm1, (x, aux tm2))
        | Tm_call (f, tm0s) -> Tm_call (f, List.map tm0s ~f:aux)
        | Tm_tick (c, tm0) -> Tm_tick (c, aux tm0)
        | Tm_share (tm0, (x1, x2, tm1)) -> Tm_share (aux tm0, (x1, x2, aux tm1)))
    ; term_ty = f term_ty
    ; term_loc
    }
  in
  aux
;;

module Var_map = struct
  include String.Map

  let union =
    merge ~f:(fun ~key:_ -> function
      | `Both (v1, _) -> Some v1
      | `Left v1 -> Some v1
      | `Right v2 -> Some v2)
  ;;

  let union_list = List.fold ~init:empty ~f:union
  let remove_list m = List.fold ~init:m ~f:remove

  let inter =
    merge ~f:(fun ~key:_ -> function
      | `Both (v1, _) -> Some v1
      | `Left _ | `Right _ -> None)
  ;;
end

let rec free_vars tm =
  match tm.term_desc with
  | Tm_var x -> Var_map.singleton x tm.term_ty
  | Tm_bool _ -> Var_map.empty
  | Tm_cond (tm0, tm1, tm2) ->
    Var_map.union_list [ free_vars tm0; free_vars tm1; free_vars tm2 ]
  | Tm_nil -> Var_map.empty
  | Tm_cons (tm1, tm2) -> Var_map.union (free_vars tm1) (free_vars tm2)
  | Tm_matl (tm0, tm1, (x, y, tm2)) ->
    Var_map.union_list
      [ free_vars tm0; free_vars tm1; Var_map.remove_list (free_vars tm2) [ x; y ] ]
  | Tm_tensor tms -> Var_map.union_list (List.map tms ~f:free_vars)
  | Tm_letp (tm0, (xs, tm1)) ->
    Var_map.union (free_vars tm0) (Var_map.remove_list (free_vars tm1) xs)
  | Tm_abs (x, _, tm0) -> Var_map.remove (free_vars tm0) x
  | Tm_app (tm1, tm2) -> Var_map.union (free_vars tm1) (free_vars tm2)
  | Tm_with (tm1, tm2) -> Var_map.union (free_vars tm1) (free_vars tm2)
  | Tm_first tm0 -> free_vars tm0
  | Tm_second tm0 -> free_vars tm0
  | Tm_inl tm0 -> free_vars tm0
  | Tm_inr tm0 -> free_vars tm0
  | Tm_case (tm0, (x1, tm1), (x2, tm2)) ->
    Var_map.union_list
      [ free_vars tm0
      ; Var_map.remove (free_vars tm1) x1
      ; Var_map.remove (free_vars tm2) x2
      ]
  | Tm_let (tm1, (x, tm2)) ->
    Var_map.union (free_vars tm1) (Var_map.remove (free_vars tm2) x)
  | Tm_call (_, tm0s) -> Var_map.union_list (List.map tm0s ~f:free_vars)
  | Tm_tick (_, tm0) -> free_vars tm0
  | Tm_share (tm0, (x1, x2, tm1)) ->
    Var_map.union (free_vars tm0) (Var_map.remove_list (free_vars tm1) [ x1; x2 ])
;;

module Call_site = struct
  type t = string [@@deriving sexp, compare, hash, equal]

  let fresh =
    let counter = ref 0 in
    fun ~fname ->
      let id = !counter in
      Int.incr counter;
      fname ^ "#" ^ Int.to_string id
  ;;

  let fname_of_t f = List.hd_exn (String.split f ~on:'#')
end

module Call_stack = struct
  type t = string * Call_site.t list [@@deriving sexp, compare, hash, equal]

  let string_of_t (fname, stack) = fname ^ " " ^ "[" ^ String.concat ~sep:", " stack ^ "]"
  let empty ~fname = fname, []

  let extend site (_, stack) =
    let fname = Call_site.fname_of_t site in
    let stack' =
      List.drop_while stack ~f:(fun site' -> not (Call_site.equal site site'))
    in
    fname, if List.is_empty stack' then site :: stack else stack'
  ;;

  let extend_k ~k site (_, stack) =
    let fname = Call_site.fname_of_t site in
    fname, List.take (site :: stack) k
  ;;
end
