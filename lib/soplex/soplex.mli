type lp_manager
type lp_var

val create_lp_manager : unit -> lp_manager

val add_lprow
  :  lp_manager
  -> ?k:Mpqf.t
  -> (lp_var * Mpqf.t) list
  -> [ `Eq | `Ge | `Le ]
  -> unit

val new_lpvar : lp_manager -> lp_var
val update_objective_coefficients : lp_manager -> (lp_var * Mpqf.t) list -> unit
val set_log_level : lp_manager -> int -> unit
val solve_primal : lp_manager -> [ `Maximize | `Minimize ] -> unit
val primal_objective_value : lp_manager -> Mpqf.t
val primal_column_solution : lp_manager -> lp_var -> Mpqf.t
val status : lp_manager -> [ `Solved | `Failed ]
val pp_stats : Format.formatter -> lp_manager -> unit
