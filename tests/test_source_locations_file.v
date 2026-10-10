From elpi Require Import elpi.
From elpi.tests Extra Dependency "source_locations.elpi" as source_locations.

Elpi File source_locations.code lp:{{
  accumulate "coq://elpi.tests/source_locations".
}}.

Elpi File source_locations.inline lp:{{
  pred inline-value o:int.
  inline-value 2.
}}.
