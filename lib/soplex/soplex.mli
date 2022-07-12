module F : sig
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

type lp_manager
type lp_var

val create_lp_manager : unit -> lp_manager
val add_lprow : lp_manager -> ?k:F.t -> (lp_var * F.t) list -> [ `Eq | `Ge | `Le ] -> unit
val new_lpvar : ?lower:F.t -> ?upper:F.t -> lp_manager -> lp_var
val update_objective_coefficients : lp_manager -> (lp_var * F.t) list -> unit
val set_log_level : lp_manager -> int -> unit
val initial_solve : lp_manager -> [ `Maximize | `Minimize ] -> unit
val solve_primal : lp_manager -> [ `Maximize | `Minimize ] -> unit
val primal_objective_value : lp_manager -> F.t
val primal_column_solution : lp_manager -> lp_var -> F.t
val status : lp_manager -> [ `Solved | `Failed ]
val pp_stats : Format.formatter -> lp_manager -> unit
