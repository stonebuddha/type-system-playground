open Core

module Make (B : Potential.BACKEND) = struct
  module P = Potential.Make (B)
  include P

  module F = struct
    include F

    let rec pow a k =
      if k = 0
      then one
      else if k = 1
      then a
      else if k = 2
      then a * a
      else if k = 3
      then a * a * a
      else (
        let b = pow a (k asr 1) in
        if k land 1 = 1 then b * b * a else b * b)
    ;;
  end

  module rec Q : sig
    type 'annot pot = 'annot I.Map.t

    val string_of_pot
      :  prefix:string
      -> f:('annot -> string option)
      -> 'annot pot
      -> string

    val new_nonneg_pot : degree:int -> _ T.pure_tyexp -> B.lp_var pot
    val zero_pot : degree:int -> _ T.pure_tyexp -> B.lp_var pot
    val assert_eq_pot : B.lp_var pot -> B.lp_var pot -> unit
    val assert_zero_pot : B.lp_var pot -> unit
    val add_pot_unequal_inds : B.lp_var pot -> B.lp_var pot -> B.lp_var pot
    val add_pot_annot : on_ind:I.t -> B.lp_var pot -> B.lp_var -> B.lp_var pot
    val sub_pot_annot : on_ind:I.t -> B.lp_var pot -> B.lp_var -> B.lp_var pot
    val min_pot : B.lp_var pot -> B.lp_var pot -> B.lp_var pot
    val max_pot : B.lp_var pot -> B.lp_var pot -> B.lp_var pot
    val split_pot : B.lp_var pot -> B.lp_var pot * B.lp_var pot
    val weaken_pot : B.lp_var pot -> B.lp_var pot
  end = struct
    type 'annot pot = 'annot I.Map.t

    let string_of_pot ~prefix ~f pot =
      String.concat
        ~sep:"\n"
        (List.map
           ~f:snd
           (I.Map.to_alist
              (I.Map.filter_mapi pot ~f:(fun ~key:ind ~data:annot ->
                   match f annot with
                   | None -> None
                   | Some annot_str ->
                     Some (prefix ^ I.string_of_t ~show_name:true ind ^ " ~> " ^ annot_str)))))
    ;;

    let new_nonneg_pot ~degree tye =
      I.make_pot ~degree tye ~f:(fun _ -> new_nonneg_annot ())
    ;;

    let zero_pot ~degree tye = I.make_pot ~degree tye ~f:(fun _ -> zero_annot)
    let assert_eq_pot = I.Map.iter2_exn ~f:assert_eq_annot
    let assert_zero_pot = I.Map.iter ~f:(fun annot -> assert_eq_annot_scalar annot F.zero)

    let add_pot_unequal_inds =
      I.Map.merge ~f:(fun ~key:_ -> function
        | `Both (annot1, annot2) -> Some (add_annot annot1 annot2)
        | `Left annot1 -> Some annot1
        | `Right annot2 -> Some annot2)
    ;;

    let add_pot_annot ~on_ind pot annot =
      I.Map.set pot ~key:on_ind ~data:(add_annot (I.Map.find_exn pot on_ind) annot)
    ;;

    let sub_pot_annot ~on_ind pot annot =
      I.Map.set pot ~key:on_ind ~data:(sub_annot (I.Map.find_exn pot on_ind) annot)
    ;;

    let min_pot = I.Map.map2_exn ~f:min_annot
    let max_pot = I.Map.map2_exn ~f:max_annot
    let split_pot pot = I.Map.unzip (I.Map.map ~f:split_annot pot)
    let weaken_pot = I.Map.map ~f:weaken_annot
  end

  and T : sig
    type 'annot pure_tyexp =
      | Tye_const of string
      | Tye_bool
      | Tye_list of 'annot pure_tyexp
      | Tye_tensor of (string * 'annot pure_tyexp) list
      | Tye_lolli of 'annot fun_tyexp
      | Tye_with of 'annot fun_tyexp * 'annot fun_tyexp
      | Tye_plus of 'annot pure_tyexp * 'annot pure_tyexp

    and 'annot rich_tyexp = 'annot pure_tyexp * 'annot Q.pot
    and 'annot fun_tyexp = Tye_fun of 'annot rich_tyexp * 'annot rich_tyexp

    type analyzing_pure_tyexp = B.lp_var pure_tyexp
    type analyzing_rich_tyexp = B.lp_var rich_tyexp
    type analyzing_fun_tyexp = B.lp_var fun_tyexp
    type analyzed_pure_tyexp = F.t pure_tyexp
    type analyzed_rich_tyexp = F.t rich_tyexp
    type analyzed_fun_tyexp = F.t fun_tyexp
  end = struct
    type 'annot pure_tyexp =
      | Tye_const of string
      | Tye_bool
      | Tye_list of 'annot pure_tyexp
      | Tye_tensor of (string * 'annot pure_tyexp) list
      | Tye_lolli of 'annot fun_tyexp
      | Tye_with of 'annot fun_tyexp * 'annot fun_tyexp
      | Tye_plus of 'annot pure_tyexp * 'annot pure_tyexp

    and 'annot rich_tyexp = 'annot pure_tyexp * 'annot Q.pot
    and 'annot fun_tyexp = Tye_fun of 'annot rich_tyexp * 'annot rich_tyexp

    type analyzing_pure_tyexp = B.lp_var pure_tyexp
    type analyzing_rich_tyexp = B.lp_var rich_tyexp
    type analyzing_fun_tyexp = B.lp_var fun_tyexp
    type analyzed_pure_tyexp = F.t pure_tyexp
    type analyzed_rich_tyexp = F.t rich_tyexp
    type analyzed_fun_tyexp = F.t fun_tyexp
  end

  and I : sig
    type t [@@deriving sexp, compare]

    val string_of_t : ?show_name:bool -> t -> string
    val degree : t -> int
    val tensor_named : (string * t) list -> t
    val split_tensor : t -> on_var:string -> t * t
    val split_tensor_multi : t -> on_vars:String.Set.t -> t * t
    val extend_tensor : t -> t String.Map.t -> t
    val shift_cons : t -> t -> t list
    val shift_inl : t -> t list
    val shift_inr : t -> t list
    val share : t -> t -> (t * int) list

    module Map : Util.MAP with type Key.t = t

    val star_of : _ T.pure_tyexp -> t
    val all_inds_exact : degree:int -> _ T.pure_tyexp -> t list
    val all_inds_up_to : degree:int -> _ T.pure_tyexp -> t list
    val make_pot : degree:int -> f:(t -> 'a) -> _ T.pure_tyexp -> 'a Q.pot
  end = struct
    include Index

    let rec star_of = function
      | T.Tye_const _ -> star
      | Tye_bool -> star
      | Tye_list _ -> list []
      | Tye_tensor tye0s ->
        tensor_named (List.map tye0s ~f:(fun (name0, tye0) -> name0, star_of tye0))
      | Tye_lolli _ -> star
      | Tye_with _ -> star
      | Tye_plus _ -> star
    ;;

    let rec all_inds_exact ~degree tye =
      if degree = 0
      then [ star_of tye ]
      else (
        match tye with
        | Tye_const _ -> []
        | Tye_bool -> []
        | Tye_list tye0 ->
          let rec aux l deg =
            if l = 0
            then if deg = 0 then [ [] ] else []
            else (
              let acc = ref [] in
              for d = 0 to deg do
                acc
                  := List.map
                       (List.cartesian_product
                          (all_inds_exact ~degree:d tye0)
                          (aux (l - 1) (deg - d)))
                       ~f:(fun (hd, tl) -> hd :: tl)
                     @ !acc
              done;
              !acc)
          in
          let acc = ref [] in
          for k = 1 to degree do
            acc := List.map (aux k (degree - k)) ~f:list @ !acc
          done;
          !acc
        | Tye_tensor tye0s ->
          let rec aux rest deg =
            match rest with
            | [] -> if deg = 0 then [ [] ] else []
            | (name0, tye0) :: rest' ->
              let acc = ref [] in
              for d = 0 to deg do
                acc
                  := List.map
                       (List.cartesian_product
                          (all_inds_exact ~degree:d tye0)
                          (aux rest' (deg - d)))
                       ~f:(fun (hd, tl) -> (name0, hd) :: tl)
                     @ !acc
              done;
              !acc
          in
          List.map (aux tye0s degree) ~f:tensor_named
        | Tye_lolli _ -> []
        | Tye_with _ -> []
        | Tye_plus (tye1, tye2) ->
          List.map ~f:inl (all_inds_exact ~degree:(degree - 1) tye1)
          @ List.map ~f:inr (all_inds_exact ~degree:(degree - 1) tye2))
    ;;

    let all_inds_up_to ~degree tye =
      let acc = ref [] in
      for d = 0 to degree do
        acc := all_inds_exact ~degree:d tye @ !acc
      done;
      !acc
    ;;

    let make_pot ~degree ~f tye =
      Map.of_alist_exn (List.map (all_inds_up_to ~degree tye) ~f:(fun ind -> ind, f ind))
    ;;
  end

  module CI = struct
    type t =
      { embed : I.t
      ; vars : String.Set.t
      }
    [@@deriving sexp, compare]

    let star_of binds =
      { embed = I.star_of (Tye_tensor (Map.to_alist binds)); vars = Map.key_set binds }
    ;;

    let degree { embed; _ } = I.degree embed

    let all_cinds_exact ~degree binds =
      List.map
        (I.all_inds_exact ~degree (Tye_tensor (Map.to_alist binds)))
        ~f:(fun ind -> { embed = ind; vars = Map.key_set binds })
    ;;

    let all_cinds_up_to ~degree binds =
      List.map
        (I.all_inds_up_to ~degree (Tye_tensor (Map.to_alist binds)))
        ~f:(fun ind -> { embed = ind; vars = Map.key_set binds })
    ;;

    let split { embed; vars } ~on_var =
      let ind, embed' = I.split_tensor embed ~on_var in
      ind, { embed = embed'; vars = Set.remove vars on_var }
    ;;

    let split_multi { embed; vars } ~on_vars =
      let embed1, embed2 = I.split_tensor_multi embed ~on_vars in
      { embed = embed1; vars = on_vars }, { embed = embed2; vars = Set.diff vars on_vars }
    ;;

    let extend { embed; vars } x ind =
      let embed' = I.extend_tensor embed (String.Map.singleton x ind) in
      { embed = embed'; vars = Set.add vars x }
    ;;

    module Map = Util.Make_map (struct
      type nonrec t = t [@@deriving sexp, compare]
    end)

    let make_cpot ~degree ~f tye =
      Map.of_alist_exn
        (List.map (all_cinds_up_to ~degree tye) ~f:(fun cind -> cind, f cind))
    ;;
  end

  include Q
  include T

  let rec string_of_tye ~f l =
    let rec aux = function
      | Tye_lolli (Tye_fun (rtye01, rtye02)) ->
        string_of_rtye ~f `Tensor_ty rtye01 ^ " -o " ^ string_of_rtye ~f `Ty rtye02
      | tye -> aux_tensor tye
    and aux_tensor = function
      | Tye_tensor tye0s ->
        String.concat ~sep:" * " (List.map tye0s ~f:(fun (_, tye0) -> aux_additive tye0))
      | tye -> aux_additive tye
    and aux_additive = function
      | Tye_with (Tye_fun (_, rtye12), Tye_fun (_, rtye22)) ->
        string_of_rtye ~f `Simple_ty rtye12
        ^ " & "
        ^ string_of_rtye ~f `Additive_ty rtye22
      | Tye_plus (tye1, tye2) -> aux_simple tye1 ^ " + " ^ aux_additive tye2
      | tye -> aux_simple tye
    and aux_simple = function
      | Tye_const name -> name
      | Tye_bool -> "bool"
      | Tye_list tye0 -> "list(" ^ aux tye0 ^ ")"
      | tye -> "(" ^ aux tye ^ ")"
    in
    match l with
    | `Ty -> aux
    | `Tensor_ty -> aux_tensor
    | `Additive_ty -> aux_additive
    | `Simple_ty -> aux_simple

  and string_of_rtye ~f l (tye, _) = string_of_tye ~f l tye

  and string_of_ftye ~f (Tye_fun ((arg_tye, arg_pot), (res_tye, res_pot))) =
    let arg_pot_str = Q.string_of_pot ~prefix:"    " ~f arg_pot in
    let res_pot_str = Q.string_of_pot ~prefix:"    " ~f res_pot in
    (match arg_tye with
    | Tye_tensor arg_tye0s ->
      "("
      ^ String.concat
          ~sep:", "
          (List.map arg_tye0s ~f:(fun (name0, arg_tye0) ->
               List.hd_exn (String.split ~on:'.' name0)
               ^ ": "
               ^ string_of_tye ~f `Ty arg_tye0))
      ^ ")"
    | _ -> assert false)
    ^ " -> "
    ^ string_of_tye ~f `Ty res_tye
    ^ (if String.is_empty arg_pot_str
      then ""
      else "\n" ^ "  non-zero annotations in argument:\n" ^ arg_pot_str)
    ^
    if String.is_empty res_pot_str
    then ""
    else "\n" ^ "  non-zero annotations in result:\n" ^ res_pot_str
  ;;

  let rec map_annot_tye ~f = function
    | Tye_const name -> Tye_const name
    | Tye_bool -> Tye_bool
    | Tye_list tye0 -> Tye_list (map_annot_tye ~f tye0)
    | Tye_tensor tye0s ->
      Tye_tensor (List.map tye0s ~f:(fun (name0, tye0) -> name0, map_annot_tye ~f tye0))
    | Tye_lolli ftye0 -> Tye_lolli (map_annot_ftye ~f ftye0)
    | Tye_with (ftye1, ftye2) ->
      Tye_with (map_annot_ftye ~f ftye1, map_annot_ftye ~f ftye2)
    | Tye_plus (tye1, tye2) -> Tye_plus (map_annot_tye ~f tye1, map_annot_tye ~f tye2)

  and map_annot_rtye ~f (tye, pot) = map_annot_tye ~f tye, I.Map.map ~f pot

  and map_annot_ftye ~f (Tye_fun (arg_rtye, res_rtye)) =
    Tye_fun (map_annot_rtye ~f arg_rtye, map_annot_rtye ~f res_rtye)
  ;;

  let rec get_coefs_tye ~is_negative l = function
    | Tye_const _ -> [], []
    | Tye_bool -> [], []
    | Tye_list tye0 -> get_coefs_tye ~is_negative l tye0
    | Tye_tensor tye0s ->
      let coefss, inv_coefss =
        List.unzip
          (List.map tye0s ~f:(fun (_, tye0) -> get_coefs_tye ~is_negative l tye0))
      in
      List.concat coefss, List.concat inv_coefss
    | Tye_lolli ftye0 -> get_coefs_ftye ~is_negative F.one ftye0
    | Tye_with (ftye1, ftye2) ->
      let coefs1, inv_coefs1 = get_coefs_ftye ~is_negative F.one ftye1 in
      let coefs2, inv_coefs2 = get_coefs_ftye ~is_negative F.one ftye2 in
      coefs1 @ coefs2, inv_coefs1 @ inv_coefs2
    | Tye_plus (tye1, tye2) ->
      let coefs1, inv_coefs1 = get_coefs_tye ~is_negative l tye1 in
      let coefs2, inv_coefs2 = get_coefs_tye ~is_negative l tye2 in
      coefs1 @ coefs2, inv_coefs1 @ inv_coefs2

  and get_coefs_rtye ~is_negative l (tye, pot) =
    let coefs, inv_coefs = get_coefs_tye ~is_negative l tye in
    ( I.Map.fold pot ~init:[] ~f:(fun ~key:ind ~data:annot acc ->
          let w = F.(l * pow (of_int 10) (I.degree ind)) in
          (annot, if is_negative then w else F.(-w)) :: acc)
      @ coefs
    , inv_coefs )

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

  let embed_ty ~degree =
    let rec aux ty =
      match ty with
      | Infer.Tye_bool -> Tye_bool
      | Tye_list ty0 -> Tye_list (aux ty0)
      | Tye_tensor ty0s ->
        Tye_tensor (List.mapi ty0s ~f:(fun i ty0 -> Int.to_string i, aux ty0))
      | Tye_lolli (ty1, ty2) ->
        let tye1 = aux ty1 in
        let tye2 = aux ty2 in
        Tye_lolli
          (Tye_fun
             ((tye1, new_nonneg_pot ~degree tye1), (tye2, new_nonneg_pot ~degree tye2)))
      | Tye_with (ty1, ty2) ->
        let tye1 = aux ty1 in
        let tye2 = aux ty2 in
        Tye_with
          ( Tye_fun
              ( (Tye_tensor [], new_nonneg_pot ~degree (Tye_tensor []))
              , (tye1, new_nonneg_pot ~degree tye1) )
          , Tye_fun
              ( (Tye_tensor [], new_nonneg_pot ~degree (Tye_tensor []))
              , (tye2, new_nonneg_pot ~degree tye2) ) )
      | Tye_plus (ty1, ty2) -> Tye_plus (aux ty1, aux ty2)
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
      | Tye_list tye10, Tye_list tye20 -> aux tye10 tye20
      | Tye_tensor tye10s, Tye_tensor tye20s ->
        List.iter2_exn tye10s tye20s ~f:(fun (name10, tye10) (name20, tye20) ->
            assert (String.(name10 = name20));
            aux tye10 tye20)
      | Tye_lolli ftye1, Tye_lolli ftye2 -> assert_eq_ftye ftye1 ftye2
      | Tye_with (ftye11, ftye12), Tye_with (ftye21, ftye22) ->
        assert_eq_ftye ftye11 ftye21;
        assert_eq_ftye ftye12 ftye22
      | Tye_plus (tye11, tye12), Tye_plus (tye21, tye22) ->
        aux tye11 tye21;
        aux tye12 tye22
      | _ -> assert false
    in
    aux

  and assert_eq_rtye (tye1, pot1) (tye2, pot2) =
    assert_eq_tye tye1 tye2;
    assert_eq_pot pot1 pot2

  and assert_eq_ftye (Tye_fun (arg_rtye1, res_rtye1)) (Tye_fun (arg_rtye2, res_rtye2)) =
    assert_eq_rtye arg_rtye1 arg_rtye2;
    assert_eq_rtye res_rtye1 res_rtye2
  ;;

  let rec min_tye =
    let rec aux tye1 tye2 =
      match tye1, tye2 with
      | Tye_const name1, Tye_const name2 when String.(name1 = name2) -> Tye_const name1
      | Tye_bool, Tye_bool -> Tye_bool
      | Tye_list tye10, Tye_list tye20 -> Tye_list (aux tye10 tye20)
      | Tye_tensor tye10s, Tye_tensor tye20s ->
        Tye_tensor
          (List.map2_exn tye10s tye20s ~f:(fun (name10, tye10) (name20, tye20) ->
               assert (String.(name10 = name20));
               name10, aux tye10 tye20))
      | Tye_lolli ftye1, Tye_lolli ftye2 -> Tye_lolli (min_ftye ftye1 ftye2)
      | Tye_with (ftye11, ftye12), Tye_with (ftye21, ftye22) ->
        Tye_with (min_ftye ftye11 ftye21, min_ftye ftye12 ftye22)
      | Tye_plus (tye11, tye12), Tye_plus (tye21, tye22) ->
        Tye_plus (aux tye11 tye21, aux tye12 tye22)
      | _ -> assert false
    in
    aux

  and min_rtye (tye1, pot1) (tye2, pot2) = min_tye tye1 tye2, min_pot pot1 pot2

  and min_ftye (Tye_fun (arg_rtye1, res_rtye1)) (Tye_fun (arg_rtye2, res_rtye2)) =
    Tye_fun (max_rtye arg_rtye1 arg_rtye2, min_rtye res_rtye1 res_rtye2)

  and max_tye =
    let rec aux tye1 tye2 =
      match tye1, tye2 with
      | Tye_const name1, Tye_const name2 when String.(name1 = name2) -> Tye_const name1
      | Tye_bool, Tye_bool -> Tye_bool
      | Tye_list tye10, Tye_list tye20 -> Tye_list (aux tye10 tye20)
      | Tye_tensor tye10s, Tye_tensor tye20s ->
        Tye_tensor
          (List.map2_exn tye10s tye20s ~f:(fun (name10, tye10) (name20, tye20) ->
               assert (String.(name10 = name20));
               name10, aux tye10 tye20))
      | Tye_lolli ftye1, Tye_lolli ftye2 -> Tye_lolli (max_ftye ftye1 ftye2)
      | Tye_with (ftye11, ftye12), Tye_with (ftye21, ftye22) ->
        Tye_with (max_ftye ftye11 ftye21, max_ftye ftye12 ftye22)
      | Tye_plus (tye11, tye12), Tye_plus (tye21, tye22) ->
        Tye_plus (aux tye11 tye21, aux tye12 tye22)
      | _ -> assert false
    in
    aux

  and max_rtye (tye1, pot1) (tye2, pot2) = max_tye tye1 tye2, max_pot pot1 pot2

  and max_ftye (Tye_fun (arg_rtye1, res_rtye1)) (Tye_fun (arg_rtye2, res_rtye2)) =
    Tye_fun (min_rtye arg_rtye1 arg_rtye2, max_rtye res_rtye1 res_rtye2)
  ;;

  let rec zero_copy_tye_cf ~degree =
    let rec aux tye =
      match tye with
      | Tye_const name -> Tye_const name
      | Tye_bool -> Tye_bool
      | Tye_list tye0 -> Tye_list (aux tye0)
      | Tye_tensor tye0s ->
        Tye_tensor (List.map tye0s ~f:(fun (name0, tye0) -> name0, aux tye0))
      | Tye_lolli ftye0 -> Tye_lolli (zero_copy_ftye_cf ~degree ftye0)
      | Tye_with (ftye1, ftye2) ->
        Tye_with (zero_copy_ftye_cf ~degree ftye1, zero_copy_ftye_cf ~degree ftye2)
      | Tye_plus (tye1, tye2) -> Tye_plus (aux tye1, aux tye2)
    in
    aux

  and zero_copy_rtye_cf ~degree (tye, _) =
    zero_copy_tye_cf ~degree tye, zero_pot ~degree tye

  and zero_copy_ftye_cf ~degree (Tye_fun (arg_rtye, res_rtye)) =
    Tye_fun (zero_copy_rtye_cf ~degree arg_rtye, zero_copy_rtye_cf ~degree res_rtye)
  ;;

  let rec zero_out_tye_cf =
    let rec aux tye =
      match tye with
      | Tye_const _ -> ()
      | Tye_bool -> ()
      | Tye_list tye0 -> aux tye0
      | Tye_tensor tye0s -> List.iter tye0s ~f:(fun (_, tye0) -> aux tye0)
      | Tye_lolli ftye0 -> zero_out_ftye_cf ftye0
      | Tye_with (ftye1, ftye2) ->
        zero_out_ftye_cf ftye1;
        zero_out_ftye_cf ftye2
      | Tye_plus (tye1, tye2) ->
        aux tye1;
        aux tye2
    in
    aux

  and zero_out_rtye_cf (tye, pot) =
    zero_out_tye_cf tye;
    assert_zero_pot pot

  and zero_out_ftye_cf (Tye_fun (arg_rtye, res_rtye)) =
    zero_out_rtye_cf arg_rtye;
    zero_out_rtye_cf res_rtye
  ;;

  let add_tye_cf =
    let rec aux tye1 tye2 =
      match tye1, tye2 with
      | Tye_const name1, Tye_const name2 when String.(name1 = name2) -> Tye_const name1
      | Tye_bool, Tye_bool -> Tye_bool
      | Tye_list tye10, Tye_list tye20 -> Tye_list (aux tye10 tye20)
      | Tye_tensor tye10s, Tye_tensor tye20s ->
        Tye_tensor
          (List.map2_exn tye10s tye20s ~f:(fun (name10, tye10) (name20, tye20) ->
               assert (String.(name10 = name20));
               name10, aux tye10 tye20))
      | Tye_lolli ftye1, Tye_lolli ftye2 ->
        zero_out_ftye_cf ftye2;
        Tye_lolli ftye1
      | Tye_with (ftye11, ftye12), Tye_with (ftye21, ftye22) ->
        zero_out_ftye_cf ftye21;
        zero_out_ftye_cf ftye22;
        Tye_with (ftye11, ftye12)
      | Tye_plus (tye11, tye12), Tye_plus (tye21, tye22) ->
        Tye_plus (aux tye11 tye21, aux tye12 tye22)
      | _ -> assert false
    in
    aux
  ;;

  let split_tye_cf ~degree =
    let rec aux tye =
      match tye with
      | Tye_const name -> Tye_const name, Tye_const name
      | Tye_bool -> Tye_bool, Tye_bool
      | Tye_list tye0 ->
        let tye10, tye20 = aux tye0 in
        Tye_list tye10, Tye_list tye20
      | Tye_tensor tye0s ->
        let tye10s, tye20s =
          List.unzip
            (List.map tye0s ~f:(fun (name0, tye0) ->
                 let tye10, tye20 = aux tye0 in
                 (name0, tye10), (name0, tye20)))
        in
        Tye_tensor tye10s, Tye_tensor tye20s
      | Tye_lolli ftye0 -> Tye_lolli ftye0, Tye_lolli (zero_copy_ftye_cf ~degree ftye0)
      | Tye_with (ftye1, ftye2) ->
        ( Tye_with (ftye1, ftye2)
        , Tye_with (zero_copy_ftye_cf ~degree ftye1, zero_copy_ftye_cf ~degree ftye2) )
      | Tye_plus (tye1, tye2) ->
        let tye11, tye21 = aux tye1 in
        let tye12, tye22 = aux tye2 in
        Tye_plus (tye11, tye12), Tye_plus (tye21, tye22)
    in
    aux
  ;;
end
