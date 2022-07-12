open Core

module Lang = struct
  let name = "aara-base"

  type command = Ast.cmd
  type environment = Infer.Env.t * Infer.Fundef.t

  let parse_command = Parse.cmd
  let parse_file = Parse.file
  let create_environment () = Infer.Env.empty, Infer.Fundef.empty
  let lp_backend = ref (module Soplex : Potential.BACKEND)
  let analysis_degree = ref 1
  let print_stats = ref false

  let execute cmd ~from:(infer_env, fdef) ~verbose =
    Result.try_with (fun () ->
        match cmd with
        | Ast.Cmd_dec dec ->
          let dec', infer_env' = Infer.f_dec_exn infer_env dec in
          let normalized_dec = Normalize.f_dec ~elim_reuse:true dec' in
          let fdef' =
            match normalized_dec.dec_desc with
            | Dec_defn (f, _, _, _, _) ->
              Infer.Fundef.add_fun_definition fdef f normalized_dec
          in
          Analyze.f_dec
            !lp_backend
            ~verbose
            ~degree:!analysis_degree
            ~print_stats:!print_stats
            fdef'
            normalized_dec;
          infer_env', fdef'
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
          infer_env, fdef
        | Cmd_use_solver b ->
          (match b with
          | "soplex" ->
            lp_backend := (module Soplex : Potential.BACKEND);
            if verbose then Format.printf "use backend soplex@."
          | "clp" ->
            lp_backend := (module Clp : Potential.BACKEND);
            if verbose then Format.printf "use backend clp@."
          | _ -> if verbose then Format.eprintf "@{<error>Error@}: unknown backend %s@." b);
          infer_env, fdef
        | Cmd_analyze f ->
          (match Infer.Fundef.find_fun_definition fdef f with
          | Some dec ->
            Analyze.f_dec
              !lp_backend
              ~verbose
              ~degree:!analysis_degree
              ~print_stats:!print_stats
              fdef
              dec
          | None ->
            if verbose then Format.eprintf "@{<error>Error@}: function %s not found@." f);
          infer_env, fdef
        | Cmd_set_degree d ->
          if d >= 1
          then (
            analysis_degree := d;
            if verbose then Format.printf "set analysis degree to %d@." d)
          else if verbose
          then Format.eprintf "@{<error>Error@}: analysis degree must be positive@.";
          infer_env, fdef
        | Cmd_print_stats flag ->
          print_stats := flag;
          if verbose
          then Format.eprintf "set print-stats flag to %s@." (Bool.to_string flag);
          infer_env, fdef)
  ;;

  let preludes = [ "test/prelude.txt" ]
end

module Top = Repl.Make (Lang)
