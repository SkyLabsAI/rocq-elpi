From elpi.tests Require Import test_source_locations_file.

Elpi Command test.SourceLocations.
Elpi Accumulate File source_locations.code.
Elpi Accumulate File source_locations.inline.
Elpi Accumulate lp:{{
  main _ :-
    std.assert! (file-value 1) "imported external code",
    std.assert! (inline-value 2) "imported inline code",
    attributes Attributes,
    std.mem Attributes (attribute "elpi.loc" (leaf-loc Loc)),
    loc.fields Loc File _ _ _ _,
    std.assert! (rex.match "^\\./.*test_source_locations\\.v$" File)
      "loc.fields must resolve the current source",
    open_in File Source, close_in Source.
}}.
Elpi test.SourceLocations.
