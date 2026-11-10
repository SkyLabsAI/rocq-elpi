From elpi Require Import elpi.

(** Standalone reduction of the [cpp.spec] universe-restriction regression.
    The spec carrier and its instances are opaque; no C++ or Iris is needed.
    The argument below has no spec notation or explicit holes and is ground
    when [main] receives it. Keep ordinary implicit-instance elaboration:
    replaying a fully explicit printed term does not reproduce the slowdown.

    [add-const] takes about 0.23 s on the affected build versus 0.0004 s on main.
    The seemingly redundant [BinderCPS] casts preserve the elaboration path. *)

Universe quant logic.
Constraint quant < logic.

Variant dummy_prop : Prop := DummyValue.
Definition BinderCPS {T} (kf : unit -> dummy_prop -> T) := dummy_prop -> T.

Section operations.
  Context {PROP spec_car : Type}.
  Class SpecGen := {
    add_pre : PROP -> spec_car -> spec_car;
    add_with : forall {T : Type@{quant}},
      (T -> spec_car) -> unit -> dummy_prop -> spec_car
  }.
  Class WithPost := { start_post : spec_car }.
End operations.
Arguments SpecGen : clear implicits.
Arguments WithPost : clear implicits.
Arguments add_pre {PROP spec_car _} _ _.
Arguments add_with {PROP spec_car _ T} _ _ _.
Arguments start_post {spec_car _}.

Parameter PROP WpSpec : Type@{logic}.
Parameter emp : PROP.
#[global] Declare Instance wp_gen : SpecGen PROP WpSpec.
#[global] Declare Instance wp_post : WithPost WpSpec.

Elpi Command direct_add_const.
Elpi Accumulate lp:{{
  main [trm Body] :-
    coq.env.add-const "direct_spec" Body _ @transparent! _.
}}.

Timeout 3 Elpi direct_add_const
  ((let f0 := fun x0 : unit =>
    let f1 := fun x1 : unit =>
    let f2 := fun x2 : unit =>
    let f3 := fun x3 : unit =>
    let f4 := fun x4 : unit =>
    let f5 := fun x5 : unit =>
    let f6 := fun x6 : unit =>
    let f7 := fun x7 : unit =>
    let f8 := fun x8 : unit =>
    let f9 := fun x9 : unit =>
    let f10 := fun x10 : unit =>
    let f11 := fun x11 : unit =>
    let f12 := fun x12 : unit =>
      add_pre emp (add_pre emp (add_pre emp (add_pre emp
        (add_pre emp (add_pre emp (add_pre emp (add_pre emp start_post)))))))
    in (add_with f12 tt :> BinderCPS (add_with f12)) DummyValue
    in (add_with f11 tt :> BinderCPS (add_with f11)) DummyValue
    in (add_with f10 tt :> BinderCPS (add_with f10)) DummyValue
    in (add_with f9 tt :> BinderCPS (add_with f9)) DummyValue
    in (add_with f8 tt :> BinderCPS (add_with f8)) DummyValue
    in (add_with f7 tt :> BinderCPS (add_with f7)) DummyValue
    in (add_with f6 tt :> BinderCPS (add_with f6)) DummyValue
    in (add_with f5 tt :> BinderCPS (add_with f5)) DummyValue
    in (add_with f4 tt :> BinderCPS (add_with f4)) DummyValue
    in (add_with f3 tt :> BinderCPS (add_with f3)) DummyValue
    in (add_with f2 tt :> BinderCPS (add_with f2)) DummyValue
    in (add_with f1 tt :> BinderCPS (add_with f1)) DummyValue
    in (add_with f0 tt :> BinderCPS (add_with f0)) DummyValue) : WpSpec).
