open Core

type ty =
  { ty_desc : ty_desc
  ; ty_loc : Location.t
  }

and ty_desc =
  | Ty_const of string (** type constant: int, bool, ... *)
  | Ty_app of ty * ty list (** type application: list(int), ... *)
  | Ty_arrow of ty * ty (** arrow type: t1 -> t2 *)

type 'ty term =
  { term_desc : 'ty term_desc
  ; term_ty : 'ty
  ; term_loc : Location.t
  }

and 'ty term_desc =
  | Tm_var of string (** variable: x *)
  | Tm_abs of string * 'ty term (** abstraction: fun x -> e0 *)
  | Tm_app of 'ty term * 'ty term (** application: e_1(e_2) *)
  | Tm_let of 'ty term * (string * 'ty term) (** let: let x = e_1 in e_2 *)

type untyped_term = unit term
type typed_term = ty term

type 'ty dec =
  { dec_desc : 'ty dec_desc
  ; dec_loc : Location.t
  }

and 'ty dec_desc =
  | Dec_val of string option * 'ty term
  | Dec_type of string
  | Dec_decl of string * ty

type untyped_dec = unit dec
type typed_dec = ty dec

let string_of_ty =
  let rec aux ty =
    match ty.ty_desc with
    | Ty_arrow (ty1, ty2) -> aux_simple ty1 ^ " -> " ^ aux ty2
    | _ -> aux_simple ty
  and aux_simple ty =
    match ty.ty_desc with
    | Ty_const name -> name
    | Ty_app (ty1, ty2s) ->
      aux_simple ty1 ^ "(" ^ String.concat ~sep:", " (List.map ty2s ~f:aux) ^ ")"
    | _ -> "(" ^ aux ty ^ ")"
  in
  aux
;;

let map_ty_term ~f =
  let rec aux { term_desc; term_ty; term_loc } =
    { term_desc =
        (match term_desc with
        | Tm_var x -> Tm_var x
        | Tm_abs (x, tm0) -> Tm_abs (x, aux tm0)
        | Tm_app (tm1, tm2) -> Tm_app (aux tm1, aux tm2)
        | Tm_let (tm1, (x, tm2)) -> Tm_let (aux tm1, (x, aux tm2)))
    ; term_ty = f term_ty
    ; term_loc
    }
  in
  aux
;;
