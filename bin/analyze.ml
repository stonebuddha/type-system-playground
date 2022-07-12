open Core

exception Analysis_error of string * Location.t

let () =
  Location.register_error_of_exn (function
      | Analysis_error (msg, loc) -> Some (Location.errorf ~loc "%s" msg)
      | _ -> None)
;;

module Make (B : Potential.BACKEND) = struct
  module P = Potential.Make (B)
  include P

  let iteratively_solve ~print_stats =
    let rec aux sol_opt = function
      | [] -> sol_opt
      | coefs :: rest ->
        B.update_objective_coefficients lpman coefs;
        if Option.is_none sol_opt
        then (
          B.set_log_level lpman 0;
          if print_stats then Format.printf "%a" B.pp_stats lpman;
          B.initial_solve lpman `Minimize)
        else B.solve_primal lpman `Minimize;
        (match B.status lpman with
        | `Solved ->
          let sol = B.primal_column_solution lpman in
          List.iter coefs ~f:(fun (v, _) -> assert_eq_annot_scalar v (sol v));
          aux (Some sol) rest
        | `Failed -> sol_opt)
    in
    aux None
  ;;
end

let f_dec (solver : (module Potential.BACKEND)) ~verbose ~degree:_ ~print_stats:_ _ dec =
  let module B = (val solver : Potential.BACKEND) in
  let module M = Make (B) in
  match dec.Ast.dec_desc with
  | Dec_defn (f, _, _, ftye, _) ->
    if verbose
    then Format.printf "defn %s: %s@." f (Ast.string_of_fun_ty (Infer.deref_fun_tye ftye))
;;
