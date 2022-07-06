open Core

module type LANG = sig
  val name : string

  type command
  type environment

  val parse_command : Lexing.lexbuf -> (command, exn) Result.t
  val parse_file : Lexing.lexbuf -> (command list, exn) Result.t
  val create_environment : unit -> environment
  val execute : command -> from:environment -> verbose:bool -> (environment, exn) Result.t
  val preludes : string list
end

module Make : functor (L : LANG) -> sig
  val main : unit -> unit
  val produce_prelude_environment : unit -> L.environment
end
