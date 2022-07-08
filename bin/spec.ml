open Core

module Lang = struct
  let name = "lfpl"

  type command = Ast.cmd
  type environment = Infer.Env.t

  let parse_command = Parse.cmd
  let parse_file = Parse.file
  let create_environment () = Infer.Env.empty

  let execute cmd ~from:infer_env ~verbose =
    Result.try_with (fun () ->
        match cmd with
        | Ast.Cmd_dec dec ->
          let dec', infer_env' = Infer.f_dec_exn infer_env dec in
          Analyze.f_dec_exn ~verbose dec';
          infer_env'
        | Cmd_show_type f ->
          (match Infer.Env.find_fun_type_bind infer_env f with
          | Some ftye ->
            if verbose
            then
              Format.printf
                "type of %s is %s@."
                f
                (Ast.string_of_fun_ty (Infer.deref_fun_tye ftye))
          | None ->
            if verbose then Format.eprintf "@{<error>Error@}: function %s not found@." f);
          infer_env)
  ;;

  let preludes = [ "test/prelude.txt" ]
end

module Top = Repl.Make (Lang)
