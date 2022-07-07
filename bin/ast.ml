open Core

type ty =
  { ty_desc : ty_desc
  ; ty_loc : Location.t
  }

and ty_desc =
  | Ty_const of string (** type constant: _weak42 *)
  | Ty_bool (** Boolean type: bool *)
  | Ty_list of ty (** list type: list(t0) *)
  | Ty_tensor of ty * ty (** multiplicative conjunction: t1 * t2 *)
  | Ty_lolli of ty * ty (** multiplicative disjunction: t1 -o t2 *)
  | Ty_with of ty * ty (** additive conjunction: t1 & t2 *)
  | Ty_plus of ty * ty (** additive disjunction: t1 + t2 *)
  | Ty_diamond (** precious little diamond: <> *)

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
  | Tm_cons of 'ty term * 'ty term * 'ty term (** cons list: cons(d, e1, e2) *)
  | Tm_iter of 'ty term * 'ty term * (string * string * string * 'ty term)
      (** list iteration: iter e0 ( nil -> e1 | cons(d, x, _) with y -> e2 ) *)
  | Tm_tensor of 'ty term * 'ty term (** tensor introduction: e1 * e2 *)
  | Tm_letp of 'ty term * (string * string * 'ty term)
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

type untyped_term = unit term
type typed_term = ty term

type 'ty dec =
  { dec_desc : 'ty dec_desc
  ; dec_loc : Location.t
  }

and 'ty dec_desc =
  | Dec_val of string option * 'ty term
  | Dec_decl of string * ty * 'ty

type untyped_dec = unit dec
type typed_dec = ty dec

let string_of_ty =
  let rec aux ty =
    match ty.ty_desc with
    | Ty_lolli (ty1, ty2) -> aux_tensor ty1 ^ " -o " ^ aux ty2
    | _ -> aux_tensor ty
  and aux_tensor ty =
    match ty.ty_desc with
    | Ty_tensor (ty1, ty2) -> aux_additive ty1 ^ " * " ^ aux_tensor ty2
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
    | Ty_diamond -> "<>"
    | _ -> "(" ^ aux ty ^ ")"
  in
  aux
;;

let map_ty_term ~f =
  let rec aux { term_desc; term_ty; term_loc } =
    { term_desc =
        (match term_desc with
        | Tm_var x -> Tm_var x
        | Tm_bool b -> Tm_bool b
        | Tm_cond (tm0, tm1, tm2) -> Tm_cond (aux tm0, aux tm1, aux tm2)
        | Tm_nil -> Tm_nil
        | Tm_cons (tm0, tm1, tm2) -> Tm_cons (aux tm0, aux tm1, aux tm2)
        | Tm_iter (tm0, tm1, (d, x, y, tm2)) ->
          Tm_iter (aux tm0, aux tm1, (d, x, y, aux tm2))
        | Tm_tensor (tm1, tm2) -> Tm_tensor (aux tm1, aux tm2)
        | Tm_letp (tm0, (x1, x2, tm1)) -> Tm_letp (aux tm0, (x1, x2, aux tm1))
        | Tm_abs (x, ty_opt, tm0) -> Tm_abs (x, ty_opt, aux tm0)
        | Tm_app (tm1, tm2) -> Tm_app (aux tm1, aux tm2)
        | Tm_with (tm1, tm2) -> Tm_with (aux tm1, aux tm2)
        | Tm_first tm0 -> Tm_first (aux tm0)
        | Tm_second tm0 -> Tm_second (aux tm0)
        | Tm_inl tm0 -> Tm_inl (aux tm0)
        | Tm_inr tm0 -> Tm_inr (aux tm0)
        | Tm_case (tm0, (x1, tm1), (x2, tm2)) ->
          Tm_case (aux tm0, (x1, aux tm1), (x2, aux tm2))
        | Tm_let (tm1, (x, tm2)) -> Tm_let (aux tm1, (x, aux tm2)))
    ; term_ty = f term_ty
    ; term_loc
    }
  in
  aux
;;
