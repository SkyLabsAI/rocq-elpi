(* rocq-elpi: Coq terms as the object language of elpi                       *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

val logical_name : string -> string
(** Map a file beneath a Rocq loadpath to its stable [coq://] identity.
    Unmapped files are retained unchanged. *)

val physical_name : string -> string
(** Resolve a stored identity using the current loadpath, for diagnostics.
    If its source is unavailable or ambiguous, retain the logical name. *)
