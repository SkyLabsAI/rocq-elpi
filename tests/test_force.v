From Corelib Require Import Force.
From elpi Require Import elpi.

Definition sensitive_type := 1 + 1 = 2.
Definition blocked_sensitive := __block Type sensitive_type.
Definition run_sensitive := __run nat nat (__block nat (1 + 1)) (fun n => n).
Definition captured_dependent :=
  __block Type (forall x : nat, __unblock (__block Type (x = x))).
Definition captured_multiple :=
  __block Prop (__unblock (__block Prop sensitive_type) /\
                __unblock (__block Prop True)).
Definition captured_local_definition :=
  __block Type (let X := __block Type nat in __unblock X).
Definition captured_nested :=
  __block Type (let T := __unblock (__block Type nat) in
    forall x : T, __unblock (__block Type (x = x))).

Elpi Command copy_force.
Elpi Accumulate lp:{{
  main [str Source, str Target] :-
    coq.locate Source (const GR),
    coq.env.const GR (some Body) Ty,
    copy Body Copy,
    fold-map Copy 0 Mapped 0,
    coq.typecheck Mapped Ty ok,
    coq.env.add-const Target Mapped Ty @transparent! _.
}}.

Elpi copy_force "blocked_sensitive" "blocked_sensitive_copy".
Elpi copy_force "run_sensitive" "run_sensitive_copy".
Elpi copy_force "captured_dependent" "captured_dependent_copy".
Elpi copy_force "captured_multiple" "captured_multiple_copy".
Elpi copy_force "captured_local_definition" "captured_local_definition_copy".
Elpi copy_force "captured_nested" "captured_nested_copy".

(* Check syntax, not just conversion: the block payload and hidden captures
   must survive both Elpi traversals and native readback without normalization. *)
Goal True.
Proof.
  let original := eval unfold blocked_sensitive in blocked_sensitive in
  let copied := eval unfold blocked_sensitive_copy in blocked_sensitive_copy in
  constr_eq original copied.
  let original := eval unfold run_sensitive in run_sensitive in
  let copied := eval unfold run_sensitive_copy in run_sensitive_copy in
  constr_eq original copied.
  let original := eval unfold captured_dependent in captured_dependent in
  let copied := eval unfold captured_dependent_copy in captured_dependent_copy in
  constr_eq original copied.
  let original := eval unfold captured_multiple in captured_multiple in
  let copied := eval unfold captured_multiple_copy in captured_multiple_copy in
  constr_eq original copied.
  let original := eval unfold captured_local_definition in captured_local_definition in
  let copied := eval unfold captured_local_definition_copy in captured_local_definition_copy in
  constr_eq original copied.
  let original := eval unfold captured_nested in captured_nested in
  let copied := eval unfold captured_nested_copy in captured_nested_copy in
  constr_eq original copied.
  exact I.
Qed.
