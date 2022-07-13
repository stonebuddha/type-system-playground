open Core

module Make (B : Potential.BACKEND) = struct
  module P = Potential.Make (B)
  include P

  type 'annot pure_tyexp =
    | Tye_const of string
    | Tye_bool
    | Tye_list of 'annot rich_tyexp
    | Tye_tensor of 'annot pure_tyexp list
    | Tye_lolli of 'annot fun_tyexp
    | Tye_with of 'annot fun_tyexp * 'annot fun_tyexp
    | Tye_plus of 'annot rich_tyexp * 'annot rich_tyexp

  and 'annot rich_tyexp = 'annot pure_tyexp * 'annot
  and 'annot fun_tyexp = Tye_fun of 'annot rich_tyexp * 'annot rich_tyexp

  type analyzing_pure_tyexp = B.lp_var pure_tyexp
  type analyzing_rich_tyexp = B.lp_var rich_tyexp
  type analyzing_fun_tyexp = B.lp_var fun_tyexp
  type analyzed_pure_tyexp = F.t pure_tyexp
  type analyzed_rich_tyexp = F.t rich_tyexp
  type analyzed_fun_tyexp = F.t fun_tyexp

  let rec string_of_tye ~f l =
    let rec aux = function
      | Tye_lolli (Tye_fun (rtye01, rtye02)) ->
        string_of_rtye ~f `Tensor_ty rtye01 ^ " -o " ^ string_of_rtye ~f `Ty rtye02
      | tye -> aux_tensor tye
    and aux_tensor = function
      | Tye_tensor tye0s -> String.concat ~sep:" * " (List.map tye0s ~f:aux_additive)
      | tye -> aux_additive tye
    and aux_additive = function
      | Tye_with (Tye_fun ((_, pot11), rtye12), Tye_fun ((_, pot21), rtye22)) ->
        string_of_rtye ~f `Simple_ty rtye12
        ^ " "
        ^ Option.value_map (f pot11) ~default:"" ~f:(fun pot11 -> "[" ^ pot11 ^ "]")
        ^ "&"
        ^ Option.value_map (f pot21) ~default:"" ~f:(fun pot21 -> "[" ^ pot21 ^ "]")
        ^ " "
        ^ string_of_rtye ~f `Additive_ty rtye22
      | Tye_plus (rtye1, rtye2) ->
        string_of_rtye ~f `Simple_ty rtye1 ^ " + " ^ string_of_rtye ~f `Additive_ty rtye2
      | tye -> aux_simple tye
    and aux_simple = function
      | Tye_const name -> name
      | Tye_bool -> "bool"
      | Tye_list rtye0 -> "list(" ^ string_of_rtye ~f `Ty rtye0 ^ ")"
      | tye -> "(" ^ aux tye ^ ")"
    in
    match l with
    | `Ty -> aux
    | `Tensor_ty -> aux_tensor
    | `Additive_ty -> aux_additive
    | `Simple_ty -> aux_simple

  and string_of_rtye ~f l (tye, pot) =
    match f pot with
    | None -> string_of_tye ~f l tye
    | Some pot_str -> "<" ^ string_of_tye ~f `Ty tye ^ ", " ^ pot_str ^ ">"

  and string_of_ftye ~f (Tye_fun ((arg_tye, arg_pot), res_rtye)) =
    (match arg_tye with
    | Tye_tensor [ _ ] -> string_of_rtye ~f `Ty (arg_tye, arg_pot)
    | Tye_tensor arg_tye0s ->
      let arg_tye0s_str =
        "(" ^ String.concat ~sep:", " (List.map arg_tye0s ~f:(string_of_tye ~f `Ty)) ^ ")"
      in
      (match f arg_pot with
      | None -> arg_tye0s_str
      | Some arg_pot_str -> "<" ^ arg_tye0s_str ^ ", " ^ arg_pot_str ^ ">")
    | _ -> assert false)
    ^ " -> "
    ^ string_of_rtye ~f `Ty res_rtye
  ;;

  let rec map_annot_tye ~f = function
    | Tye_const name -> Tye_const name
    | Tye_bool -> Tye_bool
    | Tye_list rtye0 -> Tye_list (map_annot_rtye ~f rtye0)
    | Tye_tensor tye0s -> Tye_tensor (List.map tye0s ~f:(map_annot_tye ~f))
    | Tye_lolli ftye0 -> Tye_lolli (map_annot_ftye ~f ftye0)
    | Tye_with (ftye1, ftye2) ->
      Tye_with (map_annot_ftye ~f ftye1, map_annot_ftye ~f ftye2)
    | Tye_plus (rtye1, rtye2) ->
      Tye_plus (map_annot_rtye ~f rtye1, map_annot_rtye ~f rtye2)

  and map_annot_rtye ~f (tye, pot) = map_annot_tye ~f tye, f pot

  and map_annot_ftye ~f (Tye_fun (arg_rtye, res_rtye)) =
    Tye_fun (map_annot_rtye ~f arg_rtye, map_annot_rtye ~f res_rtye)
  ;;

  let rec get_coefs_tye ~is_negative l = function
    | Tye_const _ -> [], []
    | Tye_bool -> [], []
    | Tye_list rtye0 -> get_coefs_rtye ~is_negative F.(l * of_int 10) rtye0
    | Tye_tensor tye0s ->
      let coefs0s, inv_coefs0s =
        List.unzip (List.map tye0s ~f:(get_coefs_tye ~is_negative l))
      in
      List.concat coefs0s, List.concat inv_coefs0s
    | Tye_lolli ftye0 -> get_coefs_ftye ~is_negative F.one ftye0
    | Tye_with (ftye1, ftye2) ->
      let coefs1, inv_coefs1 = get_coefs_ftye ~is_negative F.one ftye1 in
      let coefs2, inv_coefs2 = get_coefs_ftye ~is_negative F.one ftye2 in
      coefs1 @ coefs2, inv_coefs1 @ inv_coefs2
    | Tye_plus (rtye1, rtye2) ->
      let coefs1, inv_coefs1 = get_coefs_rtye ~is_negative l rtye1 in
      let coefs2, inv_coefs2 = get_coefs_rtye ~is_negative l rtye2 in
      coefs1 @ coefs2, inv_coefs1 @ inv_coefs2

  and get_coefs_rtye ~is_negative l (tye, pot) =
    let coefs, inv_coefs = get_coefs_tye ~is_negative l tye in
    (pot, if is_negative then l else F.(-l)) :: coefs, inv_coefs

  and get_coefs_ftye ~is_negative l (Tye_fun (arg_rtye, res_rtye)) =
    let arg_coefs, arg_inv_coefs =
      get_coefs_rtye ~is_negative:(not is_negative) l arg_rtye
    in
    let res_coefs, res_inv_coefs = get_coefs_rtye ~is_negative l res_rtye in
    arg_inv_coefs @ res_coefs, arg_coefs @ res_inv_coefs
  ;;

  let get_coefs_list_for_optimizing_ftye ftye =
    let pos_coefs, neg_coefs = get_coefs_ftye ~is_negative:false (F.of_int 10) ftye in
    [ neg_coefs; pos_coefs ]
  ;;

  let embed_ty =
    let rec aux ty =
      match ty with
      | Infer.Tye_bool -> Tye_bool
      | Tye_list ty0 -> Tye_list (aux ty0, new_nonneg_annot ())
      | Tye_tensor ty0s -> Tye_tensor (List.map ty0s ~f:aux)
      | Tye_lolli (ty1, ty2) ->
        Tye_lolli
          (Tye_fun ((aux ty1, new_nonneg_annot ()), (aux ty2, new_nonneg_annot ())))
      | Tye_with (ty1, ty2) ->
        Tye_with
          ( Tye_fun ((Tye_tensor [], new_nonneg_annot ()), (aux ty1, new_nonneg_annot ()))
          , Tye_fun ((Tye_tensor [], new_nonneg_annot ()), (aux ty2, new_nonneg_annot ()))
          )
      | Tye_plus (ty1, ty2) ->
        Tye_plus ((aux ty1, new_nonneg_annot ()), (aux ty2, new_nonneg_annot ()))
      | Tye_var { contents = Tyv_link ty0 } -> aux ty0
      | Tye_var { contents = Tyv_unbound id } -> Tye_const ("_weak" ^ Int.to_string id)
    in
    aux
  ;;

  let rec assert_eq_tye =
    let rec aux tye1 tye2 =
      match tye1, tye2 with
      | Tye_const name1, Tye_const name2 when String.(name1 = name2) -> ()
      | Tye_bool, Tye_bool -> ()
      | Tye_list rtye10, Tye_list rtye20 -> assert_eq_rtye rtye10 rtye20
      | Tye_tensor tye10s, Tye_tensor tye20s -> List.iter2_exn tye10s tye20s ~f:aux
      | Tye_lolli ftye1, Tye_lolli ftye2 -> assert_eq_ftye ftye1 ftye2
      | Tye_with (ftye11, ftye12), Tye_with (ftye21, ftye22) ->
        assert_eq_ftye ftye11 ftye21;
        assert_eq_ftye ftye12 ftye22
      | Tye_plus (rtye11, rtye12), Tye_plus (rtye21, rtye22) ->
        assert_eq_rtye rtye11 rtye21;
        assert_eq_rtye rtye12 rtye22
      | _ -> assert false
    in
    aux

  and assert_eq_rtye (tye1, pot1) (tye2, pot2) =
    assert_eq_tye tye1 tye2;
    assert_eq_annot pot1 pot2

  and assert_eq_ftye (Tye_fun (arg_rtye1, res_rtye1)) (Tye_fun (arg_rtye2, res_rtye2)) =
    assert_eq_rtye arg_rtye1 arg_rtye2;
    assert_eq_rtye res_rtye1 res_rtye2
  ;;

  let rec assert_potential_free_tye =
    let rec aux tye =
      match tye with
      | Tye_const _ -> ()
      | Tye_bool -> ()
      | Tye_list rtye0 -> assert_potential_free_rtye rtye0
      | Tye_tensor tye0s -> List.iter tye0s ~f:aux
      | Tye_lolli _ -> ()
      | Tye_with _ -> ()
      | Tye_plus (rtye1, rtye2) ->
        assert_potential_free_rtye rtye1;
        assert_potential_free_rtye rtye2
    in
    aux

  and assert_potential_free_rtye (tye, pot) =
    assert_potential_free_tye tye;
    assert_eq_annot_scalar pot F.zero
  ;;

  let rec add_tye =
    let rec aux tye1 tye2 =
      match tye1, tye2 with
      | Tye_const name1, Tye_const name2 when String.(name1 = name2) -> Tye_const name1
      | Tye_bool, Tye_bool -> Tye_bool
      | Tye_list rtye10, Tye_list rtye20 -> Tye_list (add_rtye rtye10 rtye20)
      | Tye_tensor tye10s, Tye_tensor tye20s ->
        Tye_tensor (List.map2_exn tye10s tye20s ~f:aux)
      | Tye_lolli ftye1, Tye_lolli ftye2 ->
        assert_eq_ftye ftye1 ftye2;
        Tye_lolli ftye1
      | Tye_with (ftye11, ftye12), Tye_with (ftye21, ftye22) ->
        assert_eq_ftye ftye11 ftye21;
        assert_eq_ftye ftye12 ftye22;
        Tye_with (ftye11, ftye12)
      | Tye_plus (rtye11, rtye12), Tye_plus (rtye21, rtye22) ->
        Tye_plus (add_rtye rtye11 rtye21, add_rtye rtye12 rtye22)
      | _ -> assert false
    in
    aux

  and add_rtye (tye1, pot1) (tye2, pot2) = add_tye tye1 tye2, add_annot pot1 pot2

  let rec min_tye =
    let rec aux tye1 tye2 =
      match tye1, tye2 with
      | Tye_const name1, Tye_const name2 when String.(name1 = name2) -> Tye_const name1
      | Tye_bool, Tye_bool -> Tye_bool
      | Tye_list rtye10, Tye_list rtye20 -> Tye_list (min_rtye rtye10 rtye20)
      | Tye_tensor tye10s, Tye_tensor tye20s ->
        Tye_tensor (List.map2_exn tye10s tye20s ~f:aux)
      | Tye_lolli ftye1, Tye_lolli ftye2 -> Tye_lolli (min_ftye ftye1 ftye2)
      | Tye_with (ftye11, ftye12), Tye_with (ftye21, ftye22) ->
        Tye_with (min_ftye ftye11 ftye21, min_ftye ftye12 ftye22)
      | Tye_plus (rtye11, rtye12), Tye_plus (rtye21, rtye22) ->
        Tye_plus (min_rtye rtye11 rtye21, min_rtye rtye12 rtye22)
      | _ -> assert false
    in
    aux

  and min_rtye (tye1, pot1) (tye2, pot2) = min_tye tye1 tye2, min_annot pot1 pot2

  and min_ftye (Tye_fun (arg_rtye1, res_rtye1)) (Tye_fun (arg_rtye2, res_rtye2)) =
    Tye_fun (max_rtye arg_rtye1 arg_rtye2, min_rtye res_rtye1 res_rtye2)

  and max_tye =
    let rec aux tye1 tye2 =
      match tye1, tye2 with
      | Tye_const name1, Tye_const name2 when String.(name1 = name2) -> Tye_const name1
      | Tye_bool, Tye_bool -> Tye_bool
      | Tye_list rtye10, Tye_list rtye20 -> Tye_list (max_rtye rtye10 rtye20)
      | Tye_tensor tye10s, Tye_tensor tye20s ->
        Tye_tensor (List.map2_exn tye10s tye20s ~f:aux)
      | Tye_lolli ftye1, Tye_lolli ftye2 -> Tye_lolli (max_ftye ftye1 ftye2)
      | Tye_with (ftye11, ftye12), Tye_with (ftye21, ftye22) ->
        Tye_with (max_ftye ftye11 ftye21, max_ftye ftye12 ftye22)
      | Tye_plus (rtye11, rtye12), Tye_plus (rtye21, rtye22) ->
        Tye_plus (max_rtye rtye11 rtye21, max_rtye rtye12 rtye22)
      | _ -> assert false
    in
    aux

  and max_rtye (tye1, pot1) (tye2, pot2) = max_tye tye1 tye2, max_annot pot1 pot2

  and max_ftye (Tye_fun (arg_rtye1, res_rtye1)) (Tye_fun (arg_rtye2, res_rtye2)) =
    Tye_fun (min_rtye arg_rtye1 arg_rtye2, max_rtye res_rtye1 res_rtye2)
  ;;
end
