let read_file : string -> string list = fun fname ->
  let ic = open_in fname in
  let lines = ref [] in
  try
    while true do lines := input_line ic :: !lines done;
    assert false (* Unreachable *)
  with End_of_file ->
  close_in ic; List.rev !lines

let write_file : string -> string list -> unit = fun fname lines ->
  let oc = open_out fname in
  List.iter (fun l -> output_string oc l; output_char oc '\n') lines;
  close_out oc

let width = 78

let sep = Printf.sprintf "(*%s*)" (String.make (width - 4) '*')

let wrap_in_comment license_file =
  let lines = read_file license_file in
  let handle_line i line =
    let len = String.length line in
    if len + 6 >= width then
      Printf.eprintf "Line %i of file \"%s\" is too wide.\n" i license_file;
    let pad = max 0 (width - len - 6) in
    Printf.sprintf "(* %s%s *)" line (String.make pad ' ')
  in
  let lines = List.mapi handle_line lines in
  sep :: lines @ [sep]

let strip_header lines =
  let rec remove_empty lines =
    match lines with
    | "" :: lines -> remove_empty lines
    | _           -> lines
  in
  let rec remove_until_sep lines =
    match lines with
    | line :: lines when line = sep -> remove_empty lines
    | _    :: lines                 -> remove_until_sep lines
    | []                            -> assert false (* Probably an error. *)
  in
  match lines with
  | line :: lines when line = sep -> remove_until_sep lines
  | _                             -> lines

let _ =
  let (license, files) =
    match List.tl (Array.to_list Sys.argv) with
    | "--strip" :: files -> (None         , files)
    | license   :: files -> (Some(license), files)
    | _                  ->
        let prog = Sys.argv.(0) in
        Printf.eprintf "Usage: %s [LICENSE_FILE | --strip] FILE ...\n%!" prog;
        exit 1
  in
  match license with
  | Some(license) ->
      let header = wrap_in_comment license in
      let handle_file file =
        let lines = header @ "" :: strip_header (read_file file) in
        write_file file lines
      in
      List.iter handle_file files
  | None          ->
      let handle_file file =
        let lines = strip_header (read_file file) in
        write_file file lines
      in
      List.iter handle_file files
