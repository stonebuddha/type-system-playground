open Core

type ty_id = int

type ty =
  { ty_desc : ty_desc
  ; ty_loc : Location.t
  }

and ty_desc =
  | Ty_const of string (** type constant: int, bool, ... *)
  | Ty_app of ty * ty list (** type application: list(int), ... *)
  | Ty_arrow of ty * ty (** arrow type: t1 -> t2 *)
  | Ty_record of ty (** record type: {row} *)
  | Ty_variant of ty (** variant type: [row] *)
  | Ty_row_empty (** empty row: "" *)
  | Ty_row_extend of string * ty * ty (** row extension: a: t, ...r *)
  | Ty_quan_var of ty_id (** quantified type variable: 'a *)
  | Ty_weak_var of ty_id (** weak type variable: '_weak42 *)

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
  | Tm_record_empty (** empty record: {} *)
  | Tm_record_extend of string * 'ty term * 'ty term (** record extension: {a= 1, ...r} *)
  | Tm_record_select of 'ty term * string (** record selection: r.a *)
  | Tm_record_restrict of 'ty term * string (** record restriction: {r - a} *)
  | Tm_variant of string * 'ty term (** variant value: `X 5 *)
  | Tm_case of 'ty term * (string * string * 'ty term) list * (string * 'ty term) option
      (** pattern match: case e0 ( `X x -> e1 | `Y y -> e2 | `Z z -> e3 ) *)

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

let fresh_ty_id =
  let counter = ref 0 in
  fun () ->
    let id = !counter in
    Int.incr counter;
    id
;;

let string_of_ty ty =
  let tbl = Hashtbl.create (module Int) in
  let count = ref 0 in
  let next_name () =
    let i = !count in
    Int.incr count;
    let name =
      String.of_char (Char.of_int_exn (97 + (i mod 26)))
      ^ if i >= 26 then Int.to_string (i / 26) else ""
    in
    name
  in
  let rec aux ty =
    match ty.ty_desc with
    | Ty_arrow (ty1, ty2) ->
      let ty1_str = aux_simple ty1 in
      let ty2_str = aux ty2 in
      ty1_str ^ " -> " ^ ty2_str
    | _ -> aux_simple ty
  and aux_simple ty =
    match ty.ty_desc with
    | Ty_const name -> name
    | Ty_app (ty1, ty2s) ->
      let ty1_str = aux_simple ty1 in
      let ty2s_str = String.concat ~sep:", " (List.map ty2s ~f:aux) in
      ty1_str ^ "(" ^ ty2s_str ^ ")"
    | Ty_record row -> "{" ^ aux_row row ^ "}"
    | Ty_variant row -> "[" ^ aux_row row ^ "]"
    | Ty_quan_var id ->
      (match Hashtbl.find tbl id with
      | Some name -> "'" ^ name
      | None ->
        let name = next_name () in
        Hashtbl.add_exn tbl ~key:id ~data:name;
        "'" ^ name)
    | Ty_weak_var id -> "'_weak" ^ Int.to_string id
    | _ -> "(" ^ aux ty ^ ")"
  and aux_row row =
    let rec sep acc row =
      match row.ty_desc with
      | Ty_row_empty -> List.rev acc, None
      | Ty_row_extend (l, ty, row0) -> sep ((l, ty) :: acc) row0
      | _ -> List.rev acc, Some row
    in
    let binds, rest_opt = sep [] row in
    match rest_opt with
    | None ->
      String.concat ~sep:", " (List.map binds ~f:(fun (l, ty) -> l ^ ": " ^ aux ty))
    | Some rest ->
      String.concat (List.map binds ~f:(fun (l, ty) -> l ^ ": " ^ aux ty ^ ", "))
      ^ "..."
      ^ aux rest
  in
  aux ty
;;

let map_ty_term ~f =
  let rec aux { term_desc; term_ty; term_loc } =
    { term_desc =
        (match term_desc with
        | Tm_var x -> Tm_var x
        | Tm_abs (x, tm0) -> Tm_abs (x, aux tm0)
        | Tm_app (tm1, tm2) -> Tm_app (aux tm1, aux tm2)
        | Tm_let (tm1, (x, tm2)) -> Tm_let (aux tm1, (x, aux tm2))
        | Tm_record_empty -> Tm_record_empty
        | Tm_record_extend (l, tm1, tm2) -> Tm_record_extend (l, aux tm1, aux tm2)
        | Tm_record_select (tm0, l) -> Tm_record_select (aux tm0, l)
        | Tm_record_restrict (tm0, l) -> Tm_record_restrict (aux tm0, l)
        | Tm_variant (l, tm0) -> Tm_variant (l, aux tm0)
        | Tm_case (tm0, pat_cases, default_case_opt) ->
          Tm_case
            ( aux tm0
            , List.map pat_cases ~f:(fun (l, x, tm) -> l, x, aux tm)
            , Option.map default_case_opt ~f:(fun (x, tm) -> x, aux tm) ))
    ; term_ty = f term_ty
    ; term_loc
    }
  in
  aux
;;
