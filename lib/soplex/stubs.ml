(** Types *)

type t

type direction =
  | Maximize
  | Minimize

type row =
  { row_lower : Mpqf.t
  ; row_upper : Mpqf.t
  ; row_elements : (int * Mpqf.t) array
  }

type column =
  { column_obj : Mpqf.t
  ; column_lower : Mpqf.t
  ; column_upper : Mpqf.t
  ; column_elements : (int * Mpqf.t) array
  }

type status =
  | Optimal (** primal feasible and bounded, dual feasible and bounded *)
  | Infeasible (** primal infeasible, dual unbounded or infeasible *)
  | Unbounded (** primal unbounded, dual infeasible *)
  | Inf_or_unbd
  | Suboptimal
  | Other

(** Creating model *)

external create : unit -> t = "soplex_create"

(** Getters and setters of problem parameters *)

external number_rows : t -> int = "soplex_number_rows"
external number_columns : t -> int = "soplex_number_columns"
external number_elements : t -> int = "soplex_number_elements"
external direction : t -> direction = "soplex_direction"
external set_direction : t -> direction -> unit = "soplex_set_direction"
external add_rows : t -> row array -> int -> unit = "soplex_add_rows"
external delete_rows : t -> int array -> unit = "soplex_delete_rows"
external add_columns : t -> column array -> int -> unit = "soplex_add_columns"
external delete_columns : t -> int array -> unit = "soplex_delete_columns"
external objective_coefficients : t -> Mpqf.t array = "soplex_objective_coefficients"

external change_objective_coefficients
  :  t
  -> Mpqf.t array
  -> unit
  = "soplex_change_objective_coefficients"

(** Getters and setters of solver parameters *)

external log_level : t -> int = "soplex_log_level"
external set_log_level : t -> int -> unit = "soplex_set_log_level"

(** Solver operations *)

external solve : t -> unit = "soplex_solve"

(** Retrieving solutions *)

external objective_value : t -> Mpqf.t = "soplex_objective_value"
external primal_column_solution : t -> Mpqf.t array = "soplex_primal_column_solution"
external status : t -> status = "soplex_status"

(** MPS operations *)

external read_mps : t -> string -> unit = "soplex_read_mps"
external write_mps : t -> string -> unit = "soplex_write_mps"
