From elpi Require Import elpi.

(* Minimization must preserve the universe interface supplied by the caller,
   including binders equal to another level and binders unused in the terms. *)
Elpi Command preserve_universes.
Elpi Accumulate lp:{{
  main [upoly-indt-decl D UD] :-
    std.assert-ok! (coq.typecheck-indt-decl D) "illtyped inductive",
    coq.upoly-decl->attribute UD Attributes,
    Attributes => coq.env.add-indt D _.
  main [upoly-const-decl Name (some Body) Arity UD] :-
    coq.arity->term Arity Type,
    std.assert-ok! (coq.typecheck Body Type) "illtyped definition",
    coq.upoly-decl->attribute UD Attributes,
    Attributes => coq.env.add-const Name Body Type @transparent! _.
}}.

(* Checking the constructor introduces a rigid level equal to v. *)
Elpi preserve_universes #[universes(polymorphic)]
  Inductive Bound@{u v|u<v} : Type@{v} := bound (A : Type@{u}).
Elpi Query lp:{{ coq.locate "Bound" GR, coq.env.univpoly? GR 2 }}.

(* The historical reason for disabling minimization: u equals a global level. *)
Universe fixed.
Elpi preserve_universes #[universes(polymorphic)]
  Inductive GlobalBound@{u v|u<v, u<=fixed, fixed<=u} : Type@{v} :=
  global_bound (A : Type@{u}).
Elpi Query lp:{{ coq.locate "GlobalBound" GR, coq.env.univpoly? GR 2 }}.

(* u is declared, but absent from both the terms and the constraints. *)
Elpi preserve_universes #[universes(polymorphic)]
  Inductive Unused@{u v} : Type@{v} := .
Elpi Query lp:{{ coq.locate "Unused" GR, coq.env.univpoly? GR 2 }}.

Elpi preserve_universes #[universes(polymorphic)]
  Definition constant_bound@{u v|u<v} : Type@{v} := Type@{u}.
Elpi Query lp:{{ coq.locate "constant_bound" GR, coq.env.univpoly? GR 2 }}.

Elpi preserve_universes #[universes(polymorphic)]
  Definition constant_global_bound@{u v|u<v, u<=fixed, fixed<=u}
    : Type@{v} := Type@{u}.
Elpi Query lp:{{ coq.locate "constant_global_bound" GR, coq.env.univpoly? GR 2 }}.

(* A used, inferred level must not become Set: a monomorphic declaration
   globalizes it, and global levels must be strictly above Set. *)
Elpi Query lp:{{
  coq.typecheck {{ nat }} (sort (typ U)) ok,
  coq.env.add-const "used_sort" {{ nat }} (sort (typ U)) @transparent! _,
  coq.univ.global? U.
}}.

(* Chained declarations may reuse universe data from their original terms,
   even after an intervening declaration explicitly clears the local store. *)
Elpi Query lp:{{
  coq.sort.leq (typ U) (typ V),
  coq.sort.leq (typ V) (typ U),
  Body = (fun `A` (sort (typ U)) a\ fun `B` (sort (typ V)) b\ {{ tt }}),
  coq.typecheck Body Ty ok,
  coq.env.add-const "shared_universes" Body Ty @transparent! _,
  coq.univ.global? U, coq.univ.global? V,
  (@dropunivs! => coq.env.add-const "clear_store" {{ tt }} {{ unit }} @transparent! _),
  coq.sort.leq (typ U) (typ V).
}}.
