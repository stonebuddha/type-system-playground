open Core

module Lang = struct
  let name = "ltlc"

  type command = Ast.untyped_dec
  type environment = Infer.Env.t * Analyze.Env.t

  let parse_command = Parse.dec
  let parse_file = Parse.file
  let create_environment () = Infer.Env.empty, Analyze.Env.empty

  let execute cmd ~from:(infer_env, analyze_env) ~verbose =
    Result.try_with (fun () ->
        let cmd', infer_env' = Infer.f_dec_exn infer_env cmd in
        let analyze_env' = Analyze.f_dec_exn ~verbose analyze_env cmd' in
        infer_env', analyze_env')
  ;;

  let preludes = [ "test/prelude.txt" ]
end

module Top = Repl.Make (Lang)
