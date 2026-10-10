(* rocq-elpi: Coq terms as the object language of elpi                       *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

(* Keep the logical identity in serialized code; physical names belong to the
   current process's loadpath and are used only for IO and diagnostics. *)
let prefix = "coq://"

let has_prefix prefix value =
  let n = String.length prefix in
  String.length value >= n && String.sub value 0 n = prefix

let logical_name filename =
  if has_prefix prefix filename || filename = "(stdin)" then filename else
  let directory = CUnix.canonical_path_name (Filename.dirname filename) in
  let physical = Filename.concat directory (Filename.basename filename) in
  let candidates = Loadpath.get_load_paths () |> List.filter_map (fun path ->
    let root = Filename.concat (Loadpath.physical path) "" in
    if not (has_prefix root physical) then None else
    let relative = String.sub physical (String.length root)
      (String.length physical - String.length root) in
    let logical = Names.DirPath.to_string (Loadpath.logical path) in
    Some (String.length root, logical = "", prefix ^ logical ^ "/" ^ relative)) in
  let candidates = List.sort (fun (length1, empty1, name1) (length2, empty2, name2) ->
    match Int.compare length2 length1 with
    | 0 -> (match Bool.compare empty1 empty2 with
      | 0 -> String.compare name1 name2
      | order -> order)
    | order -> order) candidates in
  match candidates with
  | (_, _, name) :: _ -> name
  | [] -> filename (* Unmapped files have no portable logical identity. *)

let physical_name name =
  if not (has_prefix prefix name) then name else
  let resource = String.sub name (String.length prefix)
    (String.length name - String.length prefix) in
  match String.split_on_char '/' resource with
  | logical :: ((_ :: _) as relative) ->
    let logical = if logical = "" then Names.DirPath.empty else
      Names.DirPath.make (List.rev_map Names.Id.of_string
        (String.split_on_char '.' logical)) in
    let relative = String.concat "/" relative in
    let files = Loadpath.find_with_logical_path logical
      |> List.map (fun path -> Filename.concat (Loadpath.physical path) relative)
      |> List.filter Sys.file_exists
      |> List.sort_uniq String.compare in
    (match files with
    | [filename] -> filename
    | _ -> name) (* Missing/ambiguous sources still have a useful logical name. *)
  | _ -> name
