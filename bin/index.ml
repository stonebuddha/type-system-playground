open Core

type t =
  { desc : desc
  ; deg : int
  }

and desc =
  | Ind_star
  | Ind_list of t list
  | Ind_tensor of (string * t) list
  | Ind_inl of t
  | Ind_inr of t
[@@deriving sexp, compare, hash, equal]

let rec string_of_t ?(show_name = false) ind =
  match ind.desc with
  | Ind_star -> "*"
  | Ind_list ind0s -> "[" ^ String.concat ~sep:", " (List.map ind0s ~f:string_of_t) ^ "]"
  | Ind_tensor named_ind0s ->
    "("
    ^ String.concat
        ~sep:", "
        (List.map named_ind0s ~f:(fun (name0, ind0) ->
             (if show_name then List.hd_exn (String.split ~on:'.' name0) ^ ": " else "")
             ^ string_of_t ind0))
    ^ ")"
  | Ind_inl ind0 -> "inl" ^ "(" ^ string_of_t ind0 ^ ")"
  | Ind_inr ind0 -> "inr" ^ "(" ^ string_of_t ind0 ^ ")"
;;

let degree { deg; _ } = deg
let star = { desc = Ind_star; deg = 0 }

let list ind0s =
  { desc = Ind_list ind0s
  ; deg = List.length ind0s + List.sum (module Int) ind0s ~f:degree
  }
;;

let inv_list ind =
  match ind.desc with
  | Ind_list ind0s -> ind0s
  | _ -> assert false
;;

let tensor var_ind_binds =
  let named_ind0s = Map.to_alist var_ind_binds in
  { desc = Ind_tensor named_ind0s
  ; deg = List.sum (module Int) named_ind0s ~f:(fun (_, ind0) -> ind0.deg)
  }
;;

let tensor_named named_ind0s = tensor (String.Map.of_alist_exn named_ind0s)
let inl ind0 = { desc = Ind_inl ind0; deg = ind0.deg + 1 }
let inr ind0 = { desc = Ind_inr ind0; deg = ind0.deg + 1 }

let split_tensor ind ~on_var =
  match ind.desc with
  | Ind_tensor named_ind0s ->
    let left, right =
      List.partition_map named_ind0s ~f:(fun ((name0, _) as ind0) ->
          if String.(name0 = on_var) then Either.first ind0 else Either.second ind0)
    in
    let ind_on_var = snd (List.hd_exn left) in
    ind_on_var, { desc = Ind_tensor right; deg = ind.deg - ind_on_var.deg }
  | _ -> assert false
;;

let split_tensor_multi ind ~on_vars =
  match ind.desc with
  | Ind_tensor named_ind0s ->
    let left, right =
      List.partition_map named_ind0s ~f:(fun ((name0, _) as ind0) ->
          if Set.mem on_vars name0 then Either.first ind0 else Either.second ind0)
    in
    tensor_named left, tensor_named right
  | _ -> assert false
;;

let extend_tensor ind var_ind_binds =
  match ind.desc with
  | Ind_tensor named_ind0s ->
    tensor
      (Map.merge (String.Map.of_alist_exn named_ind0s) var_ind_binds ~f:(fun ~key:_ ->
         function
         | `Both _ -> assert false
         | `Left ind | `Right ind -> Some ind))
  | _ -> assert false
;;

let shift_cons ind_h ind_t =
  if ind_h.deg = 0
  then [ ind_t; list (ind_h :: inv_list ind_t) ]
  else [ list (ind_h :: inv_list ind_t) ]
;;

let shift_inl ind0 = if ind0.deg = 0 then [ star; inl ind0 ] else [ inl ind0 ]
let shift_inr ind0 = if ind0.deg = 0 then [ star; inr ind0 ] else [ inr ind0 ]

let rec cartesian_products ls =
  match ls with
  | [] -> [ [] ]
  | ls_hd :: ls_tl ->
    List.map
      (List.cartesian_product ls_hd (cartesian_products ls_tl))
      ~f:(fun (hd, tl) -> hd :: tl)
;;

let interleave xs ys =
  let memo =
    Array.make_matrix ~dimx:(List.length xs + 1) ~dimy:(List.length ys + 1) None
  in
  let rec dp xn yn xs ys =
    match memo.(xn).(yn) with
    | Some acc -> acc
    | None ->
      let acc = dp' xn yn xs ys in
      memo.(xn).(yn) <- Some acc;
      acc
  and dp' xn yn xs ys =
    match xs, ys with
    | [], _ -> [ List.map ys ~f:(fun y -> star, y) ]
    | _, [] -> [ List.map xs ~f:(fun x -> x, star) ]
    | x :: xs', y :: ys' ->
      let x_first = List.map (dp (xn + 1) yn xs' ys) ~f:(List.cons (x, star)) in
      let y_first = List.map (dp xn (yn + 1) xs ys') ~f:(List.cons (star, y)) in
      let xys = List.map (dp (xn + 1) (yn + 1) xs' ys') ~f:(List.cons (x, y)) in
      x_first @ y_first @ xys
  in
  dp 0 0 xs ys
;;

(* p_i * p_j = \sum_k c^(i,j)_k p_k *)
let rec share i j =
  match i.desc, j.desc with
  | Ind_star, _ -> [ j, 1 ]
  | _, Ind_star -> [ i, 1 ]
  | Ind_list [], _ -> [ j, 1 ]
  | _, Ind_list [] -> [ i, 1 ]
  | Ind_list i0s, Ind_list j0s ->
    List.concat_map (interleave i0s j0s) ~f:(fun l ->
        List.map
          (cartesian_products (List.map l ~f:(fun (i0, j0) -> share i0 j0)))
          ~f:(fun kcs ->
            let ks, cs = List.unzip kcs in
            list ks, List.reduce_exn ~f:( * ) (1 :: cs)))
  | Ind_tensor named_i0s, Ind_tensor named_j0s ->
    let names = fst (List.unzip named_i0s) in
    List.map
      (cartesian_products
         (List.map2_exn named_i0s named_j0s ~f:(fun (_, i0) (_, j0) -> share i0 j0)))
      ~f:(fun kcs ->
        let ks, cs = List.unzip kcs in
        tensor_named (List.zip_exn names ks), List.reduce_exn ~f:( * ) (1 :: cs))
  | Ind_inl i0, Ind_inl j0 -> List.map (share i0 j0) ~f:(fun (k, c) -> inl k, c)
  | Ind_inr i0, Ind_inr j0 -> List.map (share i0 j0) ~f:(fun (k, c) -> inr k, c)
  | Ind_inl _, Ind_inr _ -> []
  | Ind_inr _, Ind_inl _ -> []
  | _ -> assert false
;;

module Map = Util.Make_map (struct
  type nonrec t = t [@@deriving sexp, compare]
end)
