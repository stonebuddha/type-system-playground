open Core
open Result.Let_syntax

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

module Make (L : LANG) = struct
  exception Invalid_option of string

  let () =
    Caml.Printexc.register_printer (function
        | Invalid_option msg -> Some ("invalid option (" ^ msg ^ ")")
        | _ -> None)
  ;;

  let report_error exn =
    try Format.eprintf "%a" Location.report_exception exn with
    | _ -> Format.eprintf "@{<error>Error@}: %a@." Exn.pp exn
  ;;

  let report_result_and_exit res =
    match res with
    | Ok res -> res
    | Error exn ->
      report_error exn;
      exit 1
  ;;

  let parse_file filename =
    match Sys.file_exists filename with
    | `No | `Unknown -> Error (Invalid_option (filename ^ " does not exist"))
    | `Yes ->
      In_channel.with_file filename ~f:(fun inchan ->
          let lexbuf = Lexing.from_channel inchan in
          Location.init lexbuf filename;
          Location.input_name := filename;
          Location.input_lexbuf := Some lexbuf;
          L.parse_file lexbuf)
  ;;

  let execute_file ~from ~verbose filename =
    let%bind cmds = parse_file filename in
    List.fold_result cmds ~init:from ~f:(fun acc cmd -> L.execute cmd ~from:acc ~verbose)
  ;;

  let toplevel ~from =
    let eof =
      match Sys.os_type with
      | "Unix" | "Cygwin" -> "Ctrl-D"
      | "Win32" -> "Ctrl-Z"
      | _ -> "EOF"
    in
    Format.printf "REPL for the %s language.@." L.name;
    Format.printf "Enter %s to leave.@." eof;
    let phrase_buffer = Buffer.create 1024 in
    let first_line = ref true in
    let got_eof = ref false in
    let lexbuf =
      Lexing.from_function (fun buffer len ->
          if !got_eof
          then (
            got_eof := false;
            0)
          else (
            let prompt_now = if !first_line then "# " else "  " in
            first_line := false;
            Format.printf "%s@?" prompt_now;
            let len, eof =
              let i = ref 0 in
              try
                while true do
                  if !i >= len then raise Exit;
                  let c_opt = In_channel.(input_char stdin) in
                  match c_opt with
                  | None -> raise End_of_file
                  | Some c ->
                    Bytes.set buffer !i c;
                    Buffer.add_char phrase_buffer c;
                    Int.incr i;
                    if Char.(c = '\n') then raise Exit
                done;
                !i, false
              with
              | End_of_file -> !i, true
              | Exit -> !i, false
            in
            if eof
            then (
              Location.echo_eof ();
              if len > 0 then got_eof := true;
              len)
            else len))
    in
    Location.init lexbuf "//toplevel//";
    Location.input_name := "//toplevel//";
    Location.input_lexbuf := Some lexbuf;
    Location.input_phrase_buffer := Some phrase_buffer;
    Sys.catch_break true;
    let rec loop env =
      let env' =
        try
          Lexing.flush_input lexbuf;
          Buffer.reset phrase_buffer;
          Location.reset ();
          first_line := true;
          Result.ok_exn
            (let%bind cmd = L.parse_command lexbuf in
             L.execute cmd ~from:env ~verbose:true)
        with
        | End_of_file -> exit 0
        | Sys.Break ->
          Format.eprintf "Interrupted.@.";
          env
        | exn ->
          report_error exn;
          env
      in
      loop env'
    in
    loop from
  ;;

  let driver =
    Command.basic
      ~summary:("The " ^ L.name ^ " language")
      Command.Param.(
        map
          (both
             (anon (sequence ("filename" %: Filename.arg_type)))
             (flag "-no-wrapper" no_arg ~doc:" run without a command-line wrapper"))
          ~f:(fun (filenames, no_wrapper) () ->
            if not no_wrapper
            then (
              let original_argv = Sys.get_argv () in
              let n = Array.length original_argv + 2 in
              let argv = Array.create ~len:n "" in
              Array.blit ~src:original_argv ~src_pos:0 ~dst:argv ~dst_pos:1 ~len:(n - 2);
              argv.(n - 1) <- "-no-wrapper";
              argv.(0) <- "rlwrap";
              try
                ignore
                  (Unix.exec ~prog:"rlwrap" ~argv:(Array.to_list argv) () : never_returns)
              with
              | _ -> ());
            let env =
              report_result_and_exit
                (List.fold_result
                   (L.preludes @ filenames)
                   ~init:(L.create_environment ())
                   ~f:(fun acc filename ->
                     Format.printf "Loading %s ...@." filename;
                     execute_file filename ~from:acc ~verbose:true))
            in
            toplevel ~from:env))
  ;;

  let main () =
    Misc.Color.setup None;
    Command.run driver
  ;;

  let produce_prelude_environment () =
    Result.ok_exn
      (List.fold_result L.preludes ~init:(L.create_environment ()) ~f:(fun acc filename ->
           execute_file filename ~from:acc ~verbose:false))
  ;;
end
