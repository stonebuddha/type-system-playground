module type FLOAT = sig
  type t

  val zero : t
  val one : t
  val minus_one : t
  val infinity : t
  val neg_infinity : t
  val abs : t -> t
  val ( ~- ) : t -> t
  val ( + ) : t -> t -> t
  val ( - ) : t -> t -> t
  val ( * ) : t -> t -> t
  val ( / ) : t -> t -> t
  val ( >= ) : t -> t -> bool
  val ( < ) : t -> t -> bool
  val ( > ) : t -> t -> bool
  val ( <= ) : t -> t -> bool
  val is_zero : t -> bool
  val of_int : int -> t
  val of_float : float -> t
  val of_mpq : Mpqf.t -> t
  val pp : Format.formatter -> t -> unit
  val string_of_t : t -> string
end

module type BACKEND = sig
  module F : FLOAT

  type lp_manager
  type lp_var

  val create_lp_manager : unit -> lp_manager

  val add_lprow
    :  lp_manager
    -> ?k:F.t
    -> (lp_var * F.t) list
    -> [ `Eq | `Ge | `Le ]
    -> unit

  val new_lpvar : ?lower:F.t -> ?upper:F.t -> lp_manager -> lp_var
  val update_objective_coefficients : lp_manager -> (lp_var * F.t) list -> unit
  val set_log_level : lp_manager -> int -> unit
  val initial_solve : lp_manager -> [ `Maximize | `Minimize ] -> unit
  val solve_primal : lp_manager -> [ `Maximize | `Minimize ] -> unit
  val primal_objective_value : lp_manager -> F.t
  val primal_column_solution : lp_manager -> lp_var -> F.t
  val status : lp_manager -> [ `Failed | `Solved ]
  val pp_stats : Format.formatter -> lp_manager -> unit
end

module type S = sig
  module F : FLOAT

  type lp_manager
  type lp_var

  val lpman : lp_manager
  val new_nonneg_annot : unit -> lp_var
  val const_annot : F.t -> lp_var
  val zero_annot : lp_var
  val assert_eq_annot : lp_var -> lp_var -> unit
  val assert_eq_annot_scalar : lp_var -> F.t -> unit
  val assert_ge_annot : lp_var -> lp_var -> unit
  val assert_ge_annot_scalar : lp_var -> F.t -> unit
  val assert_ge_scalar_annot : F.t -> lp_var -> unit
  val scale_annot : F.t -> lp_var -> lp_var
  val add_annot : lp_var -> lp_var -> lp_var
  val add_scale_annot : lp_var -> F.t -> lp_var -> lp_var
  val add_annot_scalar : lp_var -> F.t -> lp_var
  val sub_annot : lp_var -> lp_var -> lp_var
  val sub_scale_annot : lp_var -> F.t -> lp_var -> lp_var
  val sub_annot_scalar : lp_var -> F.t -> lp_var
  val sub_scalar_annot : F.t -> lp_var -> lp_var
  val min_annot : lp_var -> lp_var -> lp_var
  val min_annot_scalar : lp_var -> F.t -> lp_var
  val max_annot : lp_var -> lp_var -> lp_var
  val max_annot_scalar : lp_var -> F.t -> lp_var
  val split_annot : lp_var -> lp_var * lp_var
  val weaken_annot : lp_var -> lp_var
  val relax_annot : lp_var -> lp_var
end

module Make (B : BACKEND) :
  S with type lp_manager := B.lp_manager and type lp_var := B.lp_var and type F.t = B.F.t =
struct
  module F = B.F

  let lpman = B.create_lp_manager ()
  let new_nonneg_annot () = B.new_lpvar ~lower:F.zero lpman
  let const_annot k = B.new_lpvar ~lower:k ~upper:k lpman
  let zero_annot = const_annot F.zero

  let assert_eq_annot lpvar1 lpvar2 =
    B.add_lprow lpman [ lpvar1, F.one; lpvar2, F.minus_one ] `Eq
  ;;

  let assert_eq_annot_scalar lpvar k = B.add_lprow lpman ~k [ lpvar, F.one ] `Eq

  let assert_ge_annot lpvar1 lpvar2 =
    B.add_lprow lpman [ lpvar1, F.one; lpvar2, F.minus_one ] `Ge
  ;;

  let assert_ge_annot_scalar lpvar k = B.add_lprow lpman ~k [ lpvar, F.one ] `Ge
  let assert_ge_scalar_annot k lpvar = B.add_lprow lpman ~k [ lpvar, F.one ] `Le

  let scale_annot k lpvar =
    let lpvar' = new_nonneg_annot () in
    B.add_lprow lpman [ lpvar', F.one; (lpvar, F.(-k)) ] `Eq;
    lpvar'
  ;;

  let add_annot lpvar1 lpvar2 =
    let lpvar = new_nonneg_annot () in
    B.add_lprow lpman [ lpvar, F.one; lpvar1, F.minus_one; lpvar2, F.minus_one ] `Eq;
    lpvar
  ;;

  let add_scale_annot lpvar1 k lpvar2 =
    let lpvar = new_nonneg_annot () in
    B.add_lprow lpman [ lpvar, F.one; lpvar1, F.minus_one; (lpvar2, F.(-k)) ] `Eq;
    lpvar
  ;;

  let add_annot_scalar lpvar1 k =
    let lpvar = new_nonneg_annot () in
    B.add_lprow lpman ~k [ lpvar, F.one; lpvar1, F.minus_one ] `Eq;
    lpvar
  ;;

  let sub_annot lpvar1 lpvar2 =
    let lpvar = new_nonneg_annot () in
    B.add_lprow lpman [ lpvar, F.one; lpvar1, F.minus_one; lpvar2, F.one ] `Eq;
    lpvar
  ;;

  let sub_scale_annot lpvar1 k lpvar2 =
    let lpvar = new_nonneg_annot () in
    B.add_lprow lpman [ lpvar, F.one; lpvar1, F.minus_one; lpvar2, k ] `Eq;
    lpvar
  ;;

  let sub_annot_scalar lpvar1 k =
    let lpvar = new_nonneg_annot () in
    B.add_lprow lpman ~k:F.(-k) [ lpvar, F.one; lpvar1, F.minus_one ] `Eq;
    lpvar
  ;;

  let sub_scalar_annot k lpvar2 =
    let lpvar = new_nonneg_annot () in
    B.add_lprow lpman ~k [ lpvar, F.one; lpvar2, F.one ] `Eq;
    lpvar
  ;;

  let min_annot lpvar1 lpvar2 =
    let lpvar = new_nonneg_annot () in
    assert_ge_annot lpvar1 lpvar;
    assert_ge_annot lpvar2 lpvar;
    lpvar
  ;;

  let min_annot_scalar lpvar1 k =
    let lpvar = new_nonneg_annot () in
    assert_ge_annot lpvar1 lpvar;
    assert_ge_scalar_annot k lpvar;
    lpvar
  ;;

  let max_annot lpvar1 lpvar2 =
    let lpvar = new_nonneg_annot () in
    assert_ge_annot lpvar lpvar1;
    assert_ge_annot lpvar lpvar2;
    lpvar
  ;;

  let max_annot_scalar lpvar1 k =
    let lpvar = new_nonneg_annot () in
    assert_ge_annot lpvar lpvar1;
    assert_ge_annot_scalar lpvar k;
    lpvar
  ;;

  let split_annot lpvar =
    let lpvar1 = new_nonneg_annot () in
    let lpvar2 = new_nonneg_annot () in
    B.add_lprow lpman [ lpvar1, F.one; lpvar2, F.one; lpvar, F.minus_one ] `Eq;
    lpvar1, lpvar2
  ;;

  let weaken_annot lpvar =
    let lpvar' = new_nonneg_annot () in
    assert_ge_annot lpvar' lpvar;
    lpvar'
  ;;

  let relax_annot lpvar =
    let lpvar' = new_nonneg_annot () in
    assert_ge_annot lpvar lpvar';
    lpvar'
  ;;
end
