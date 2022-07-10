(** Types *)

type t

type direction =
  | Maximize
  | Minimize

type row =
  { row_lower : float
  ; row_upper : float
  ; row_elements : (int * float) array
  }

type column =
  { column_obj : float
  ; column_lower : float
  ; column_upper : float
  ; column_elements : (int * float) array
  }

type status =
  | Optimal (** primal feasible and bounded, dual feasible and bounded *)
  | Infeasible (** primal infeasible, dual unbounded or infeasible *)
  | Unbounded (** primal unbounded, dual infeasible *)
  | Inf_or_unbd
  | Suboptimal
  | Other

(** Creating model *)

external create : unit -> t = "clp_create"

(** Getters and setters of problem parameters *)

external resize : t -> int -> int -> unit = "clp_resize"
external number_rows : t -> int = "clp_number_rows"
external number_columns : t -> int = "clp_number_columns"
external number_elements : t -> int = "clp_number_elements"
external direction : t -> direction = "clp_direction"
external set_direction : t -> direction -> unit = "clp_set_direction"
external add_rows : t -> row array -> int -> unit = "clp_add_rows"
external delete_rows : t -> int array -> unit = "clp_delete_rows"
external add_columns : t -> column array -> int -> unit = "clp_add_columns"
external delete_columns : t -> int array -> unit = "clp_delete_columns"
external row_lower : t -> float array = "clp_row_lower"
external change_row_lower : t -> float array -> unit = "clp_change_row_lower"
external row_upper : t -> float array = "clp_row_upper"
external change_row_upper : t -> float array -> unit = "clp_change_row_upper"
external column_lower : t -> float array = "clp_column_lower"
external change_column_lower : t -> float array -> unit = "clp_change_column_lower"
external column_upper : t -> float array = "clp_column_upper"
external change_column_upper : t -> float array -> unit = "clp_change_column_upper"
external objective_coefficients : t -> float array = "clp_objective_coefficients"

external change_objective_coefficients
  :  t
  -> float array
  -> unit
  = "clp_change_objective_coefficients"

(** Getters and setters of solver parameters*)

external log_level : t -> int = "clp_log_level"
external set_log_level : t -> int -> unit = "clp_set_log_level"

(** Solver operations *)

external primal : t -> unit = "clp_primal"
external dual : t -> unit = "clp_dual"
external initial_solve : t -> unit = "clp_initial_solve"
external initial_primal : t -> unit = "clp_initial_primal"
external initial_dual : t -> unit = "clp_initial_dual"
external initial_barrier : t -> unit = "clp_initial_barrier"

(** Retrieving solutions *)

external objective_value : t -> float = "clp_objective_value"
external primal_row_solution : t -> float array = "clp_primal_row_solution"
external primal_column_solution : t -> float array = "clp_primal_column_solution"
external dual_row_solution : t -> float array = "clp_dual_row_solution"
external dual_column_solution : t -> float array = "clp_dual_column_solution"
external status : t -> status = "clp_status"

(** MPS operations *)

external read_mps : t -> string -> unit = "clp_read_mps"
external write_mps : t -> string -> unit = "clp_write_mps"
