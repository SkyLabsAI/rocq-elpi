From elpi Require Import elpi.

(* Regression in restriction of unused universes: no BinderCPS, repeated term,
   explicit universes, or application libraries are needed. *)
Class Algebra (A : Type) := {
  bind : (unit -> A) -> A;
  seed : A
}.
Arguments bind {A _} _.
Arguments seed {A _}.
#[global] Instance algebra_unit : Algebra unit :=
  {| bind f := f tt; seed := tt |}.

Notation "'U' t" := (bind (fun _ : unit => t))
  (at level 10, t at level 200, only parsing).
Notation "'B' t" := (U t : _)
  (at level 10, t at level 200, only parsing).

Elpi Command universe_declare.
Elpi Accumulate lp:{{
  main [trm T] :- coq.env.add-const "result" T _ @transparent! _.
}}.

Timeout 1 Elpi universe_declare
  ((B B B B B B B B B B B B B B B B B B U U U U U U U U seed) : unit).
