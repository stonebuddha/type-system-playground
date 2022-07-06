open Core

module Lang = struct
  let name = "stlc"

  type command = Ast.untyped_dec
  type environment = Infer.Env.t

  let parse_command = Parse.dec
  let parse_file = Parse.file
  let create_environment () = Infer.Env.empty

  let execute cmd ~from ~verbose =
    Result.try_with (fun () -> snd (Infer.f_dec_exn ~verbose from cmd))
  ;;

  let preludes = []
end

module Top = Repl.Make (Lang)
