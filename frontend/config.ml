(** Discover the installation prefix of the library. *)

open Extra

let pkgname : string = "islaris"

let prefix : Filename.dirpath =
  (* Obtain a normalised path to the executable. *)
  let exe =
    try Filename.realpath "/proc/self/exe" with Invalid_argument(_) ->
      panic "Unable to find an absolute path to the current executable."
  in
  (* Is it in the development repo? Find the ["_build"] directory. *)
  let rec find_build path =
    match Filename.basename path with
    | "_build" -> Some(path)
    | _        ->
    let dir = Filename.dirname path in
    if dir = path then None else find_build dir
  in
  match find_build (Filename.dirname exe) with
  | Some(build) -> Filename.concat build (Filename.concat "install" "default")
  | None        ->
  (* Otherwise try using the current Opam prefix. *)
  try Sys.getenv "OPAM_SWITCH_PREFIX" with Not_found ->
  (* Nothing we can do... *)
  panic "The programs has not been installed under a standard prefix."

let build : string -> Filename.dirpath = fun section ->
  Filename.concat prefix (Filename.concat section pkgname)

let doc   : Filename.dirpath = build "doc"
let etc   : Filename.dirpath = build "etc"
let lib   : Filename.dirpath = build "lib"
let share : Filename.dirpath = build "share"
