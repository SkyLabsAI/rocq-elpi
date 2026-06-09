(* -------------------------------------------------------------------------- *)
(*  Tests for the MUTUAL INDUCTIVE HOAS (see mutind.md).                       *)
(*                                                                            *)
(*  STATUS: RED stub.  The constructors `minductive-block` / `minductive` /    *)
(*  `mblock` (and the `mind-block` kind) are DECLARED in elpi/coq-arg-HOAS.elpi *)
(*  but NOT hooked into the OCaml embedding/readback.  So:                      *)
(*                                                                            *)
(*    * HOAS that merely MENTIONS them type-checks (the file compiles);        *)
(*    * any command that PRODUCES or CONSUMES one of them fails at runtime      *)
(*      (the indt-decl readback has no case for them, and the env reader        *)
(*      `coq.env.indt-decl` only ever returns single-component `inductive`      *)
(*      decls -- rocq_elpi_HOAS.ml).                                           *)
(*                                                                            *)
(*  Each [Fail] below documents a command that fails TODAY.  They split in two: *)
(*   (A) "remove [Fail] once implemented" -- read-as-block, build-from-scratch  *)
(*       and round-trip; these SHOULD pass when the feature lands.              *)
(*   (B) "permanent [Fail]" -- the WellFormedness module asserts that MALFORMED *)
(*       blocks are rejected, so those keep failing after implementation too.   *)
(*  The non-[Fail] queries (e.g. the `coq.env.indt` parameter-count check in    *)
(*  NonUniformParam) pass today and must keep passing.                          *)
(*                                                                            *)
(*  Design (Proposal 2), mirroring the shipped `mfix` one constructor at a time:*)
(*    fixpoints (term)            inductives (indt-decl)                        *)
(*    -----------------           ----------------------                        *)
(*    kind mfix-block             kind mind-block                              *)
(*    mfix    : ... -> term       minductive-block : mind-block -> indt-decl   *)
(*    mfix-ty : ... -> mfix-block minductive       : id -> bool -> arity ->    *)
(*                                    (term -> mind-block) -> mind-block        *)
(*    mfix-bo : list term ->      mblock : list (list indc-decl) ->            *)
(*                  mfix-block                       mind-block                 *)
(*                                                                            *)
(*  Binding discipline (the part mutind.md left implicit):                      *)
(*   - `bool` per component: tt = inductive, ff = co-inductive (as `inductive`).*)
(*   - the chain of `minductive` binders introduces each component's self-ref,  *)
(*     in declaration order; ALL of them (plus shared params) are in scope      *)
(*     inside the single terminating `mblock`, whose i-th element is the        *)
(*     constructor list of the i-th component.                                  *)
(*   - parameter handling matches single inductives (coq-arg-HOAS.elpi,         *)
(*     tests/test_arg_HOAS.v `more_nup`): UNIFORM params wrap the whole block   *)
(*     via the `parameter` ("2") variant and are NOT re-applied to self-refs;   *)
(*     only NON-uniform params and INDICES are passed to self-ref occurrences   *)
(*     (`app [Self, idx]`).                                                    *)
(* -------------------------------------------------------------------------- *)

From elpi Require Import elpi.

(* Establish a current Elpi program so the bare `Elpi Query` commands below run *)
(* (coq-elpi requires a selected program; see tests/test_API.v).                *)
Elpi Command mutual_inductive_tests.

(* ========================================================================== *)
(*  1. even & odd : the base case — mutual, no parameters, no indices.        *)
(* ========================================================================== *)
Module EvenOdd.

Inductive even : Set :=
| even_O : even
| even_S : odd -> even
with odd : Set :=
| odd_S : even -> odd.

(* READ as one block: coq.env.indt-decl returns the whole mutual block. *)
Elpi Query lp:{{
  coq.locate "even" (indt I),
  coq.env.indt-decl I D,
  std.assert! (D =
    minductive-block (
      minductive "even" tt (arity (sort _)) (e\
      minductive "odd"  tt (arity (sort _)) (o\
        mblock [
          [ constructor "even_O" (arity e),
            constructor "even_S" (arity (prod _ o (_\ e))) ],
          [ constructor "odd_S"  (arity (prod _ e (_\ o))) ]
        ])))) "even/odd: unexpected mutual HOAS",
  std.assert-ok! (coq.typecheck-indt-decl D) "even/odd decl ill-typed"
}}.

(* Reading any member yields the SAME whole block (component selection is at    *)
(* the gref level, not in the decl).                                            *)
Elpi Query lp:{{
  coq.locate "even" (indt Ie), coq.env.indt-decl Ie De,
  coq.locate "odd"  (indt Io), coq.env.indt-decl Io Do,
  std.assert! (De = Do) "reading even vs odd gave different blocks"
}}.

(* BUILD a mutual block from scratch, typecheck it, and add it. *)
Elpi Query lp:{{
  D =
    minductive-block (
      minductive "eo_even" tt (arity (sort (typ _))) (e\
      minductive "eo_odd"  tt (arity (sort (typ _))) (o\
        mblock [
          [ constructor "eo_O"  (arity e),
            constructor "eo_ES" (arity (prod `x` o (_\ e))) ],
          [ constructor "eo_OS" (arity (prod `x` e (_\ o))) ]
        ]))),
  std.assert-ok! (coq.typecheck-indt-decl D) "scratch even/odd ill-typed",
  coq.env.add-indt D _
}}.
Check eo_ES : eo_odd  -> eo_even.
Check eo_OS : eo_even -> eo_odd.

End EvenOdd.

(* ========================================================================== *)
(*  2. polymorphic trees with list children — mutual + a shared parameter.    *)
(*     `forest A` is the list of children of a `tree A` (forest ~= list tree).*)
(* ========================================================================== *)
Module TreeForest.

Inductive tree (A : Type) : Type :=
| node : A -> forest A -> tree A
with forest (A : Type) : Type :=
| fnil  : forest A
| fcons : tree A -> forest A -> forest A.

(* READ as one block.  The shared UNIFORM `A` wraps the block via `parameter`   *)
(* ("2") and is absorbed by the self-refs (bare `tree`/`forest`).               *)
Elpi Query lp:{{
  coq.locate "tree" (indt I),
  coq.env.indt-decl I D,
  std.assert! (D =
    parameter "A" explicit (sort _) (a\
      minductive-block (
        minductive "tree"   tt (arity (sort _)) (tree\
        minductive "forest" tt (arity (sort _)) (forest\
          mblock [
            [ constructor "node"
                (arity (prod _ a (_\ prod _ forest (_\ tree)))) ],
            [ constructor "fnil"  (arity forest),
              constructor "fcons"
                (arity (prod _ tree (_\ prod _ forest (_\ forest)))) ]
          ]))))) "tree/forest: unexpected polymorphic mutual HOAS",
  std.assert-ok! (coq.typecheck-indt-decl D) "tree/forest decl ill-typed"
}}.

(* BUILD a fresh polymorphic rose-tree / forest pair from scratch. *)
Elpi Query lp:{{
  D =
    parameter "A" explicit (sort (typ _)) (a\
      minductive-block (
        minductive "rt_tree"   tt (arity (sort (typ _))) (tree\
        minductive "rt_forest" tt (arity (sort (typ _))) (forest\
          mblock [
            [ constructor "rt_node"
                (arity (prod `x` a (_\ prod `c` forest (_\ tree)))) ],
            [ constructor "rt_fnil"  (arity forest),
              constructor "rt_fcons"
                (arity (prod `h` tree (_\ prod `t` forest (_\ forest)))) ]
          ])))),
  std.assert-ok! (coq.typecheck-indt-decl D) "scratch tree/forest ill-typed",
  coq.env.add-indt D _
}}.
Check rt_node  : forall A, A -> rt_forest A -> rt_tree A.
Check rt_fcons : forall A, rt_tree A -> rt_forest A -> rt_forest A.

End TreeForest.

(* ========================================================================== *)
(*  3. non-uniform parameter — mutual block sharing a UNIFORM `A` and a        *)
(*     NON-uniform `n` (recursive occurrences instantiate it to 0, not n).    *)
(*     Mutual analogue of the single-inductive `more_nup` test                 *)
(*     (tests/test_arg_HOAS.v).                                               *)
(* ========================================================================== *)
Module NonUniformParam.

Inductive mt (A : Type) (n : nat) : Type :=
| tk : mf A 0 -> mt A n
with mf (A : Type) (n : nat) : Type :=
| fk : mt A 0 -> mf A n.

(* (A) READ as one block.  `A` uniform -> wraps the block via `parameter` ("2") *)
(* and is absorbed by self-refs; `n` non-uniform -> lives INSIDE each component *)
(* arity via `parameter` ("1"), is re-abstracted per constructor, and IS        *)
(* applied to self-ref occurrences (app[mt,n], app[mf,0]).                      *)
Elpi Query lp:{{
  coq.locate "mt" (indt I),
  coq.env.indt-decl I D,
  std.assert! (D =
    parameter "A" explicit (sort _) (a\
      minductive-block (
        minductive "mt" tt (parameter "n" explicit {{ nat }} (_\ arity (sort _))) (mt\
        minductive "mf" tt (parameter "n" explicit {{ nat }} (_\ arity (sort _))) (mf\
          mblock [
            [ constructor "tk"
                (parameter "n" explicit {{ nat }} (n\
                   arity (prod _ (app [mf, {{ 0 }}]) (_\ app [mt, n])))) ],
            [ constructor "fk"
                (parameter "n" explicit {{ nat }} (n\
                   arity (prod _ (app [mt, {{ 0 }}]) (_\ app [mf, n])))) ]
          ]))))) "mt/mf: unexpected non-uniform-parameter HOAS",
  std.assert-ok! (coq.typecheck-indt-decl D) "mt/mf decl ill-typed"
}}.

(* Parameter split: 2 parameters total, exactly 1 uniform.  coq.env.indt now    *)
(* reads the per-component signature of a mutual member.                        *)
(* Signature: coq.env.indt I IsInd NParams NUniformParams Arity Knames Ktypes.  *)
Elpi Query lp:{{
  coq.locate "mt" (indt I),
  coq.env.indt I _ NParams NUniform _ _ _,
  std.assert! (NParams = 2)  "mt should have 2 parameters",
  std.assert! (NUniform = 1) "mt should have exactly 1 uniform parameter"
}}.

End NonUniformParam.

(* ========================================================================== *)
(*  3b. LIMITATION: building a mutual block from HOAS with a NON-UNIFORM        *)
(*      parameter is not yet supported by the writer.  READING such a block     *)
(*      works (see NonUniformParam above, which round-trips mt/mf through        *)
(*      coq.env.indt-decl), but coq.env.add-indt / lp2inductive_entry raises     *)
(*      nYI "non uniform parameters in a mutual inductive built from HOAS".      *)
(*      This [Fail] pins the limitation; remove it once the writer supports      *)
(*      non-uniform parameters in from-HOAS mutual blocks.                       *)
(* ========================================================================== *)
Module NonUniformParamBuildLimitation.

(* The from-scratch analogue of mt/mf: a UNIFORM-free block whose only parameter *)
(* `n` is non-uniform (cross-recursive occurrences instantiate it to 0).         *)
Fail Elpi Query lp:{{
  D =
    minductive-block (
      minductive "nu_a" tt (parameter "n" explicit {{ nat }} (_\ arity (sort (typ _)))) (a\
      minductive "nu_b" tt (parameter "n" explicit {{ nat }} (_\ arity (sort (typ _)))) (b\
        mblock [
          [ constructor "nu_ka"
              (parameter "n" explicit {{ nat }} (n\
                 arity (prod _ (app [b, {{ 0 }}]) (_\ app [a, n])))) ],
          [ constructor "nu_kb"
              (parameter "n" explicit {{ nat }} (n\
                 arity (prod _ (app [a, {{ 0 }}]) (_\ app [b, n])))) ]
        ]))),
  coq.env.add-indt D _
}}.

End NonUniformParamBuildLimitation.

(* ========================================================================== *)
(*  4. indexed mutual inductives — is_even / is_odd : nat -> Prop.            *)
(*     Exercises a non-uniform INDEX in the arity and in constructor types.   *)
(* ========================================================================== *)
Module Indexed.

Inductive ev : nat -> Prop :=
| ev_O : ev 0
| ev_S : forall n, od n -> ev (S n)
with od : nat -> Prop :=
| od_S : forall n, ev n -> od (S n).

(* READ as one block.  Each arity carries the index (nat -> Prop) and           *)
(* constructor types apply the self-refs to index terms.                        *)
Elpi Query lp:{{
  coq.locate "ev" (indt I),
  coq.env.indt-decl I D,
  std.assert! (D =
    minductive-block (
      minductive "ev" tt (arity (prod _ {{ nat }} (_\ sort _))) (ev\
      minductive "od" tt (arity (prod _ {{ nat }} (_\ sort _))) (od\
        mblock [
          [ constructor "ev_O" (arity (app [ev, {{ 0 }}])),
            constructor "ev_S"
              (arity (prod _ {{ nat }} (n\
                      prod _ (app [od, n]) (_\ app [ev, {{ S lp:n }}])))) ],
          [ constructor "od_S"
              (arity (prod _ {{ nat }} (n\
                      prod _ (app [ev, n]) (_\ app [od, {{ S lp:n }}])))) ]
        ])))) "indexed mutual: unexpected HOAS",
  std.assert-ok! (coq.typecheck-indt-decl D) "ev/od decl ill-typed"
}}.

End Indexed.

(* ========================================================================== *)
(*  5. well-formedness — the validation gap flagged in the mutind.md review.   *)
(*     `mblock` must have exactly one constructor-list per `minductive`.       *)
(*     (B) PERMANENT [Fail]: malformed blocks must be REJECTED.  Today they     *)
(*     fail at readback (feature absent); once implemented they must fail at     *)
(*     the arity check.  Either way the command fails, so [Fail] stays.         *)
(* ========================================================================== *)
Module WellFormedness.

(* Two `minductive` binders but only ONE constructor list. *)
Fail Elpi Query lp:{{
  Bad =
    minductive-block (
      minductive "wf_a" tt (arity (sort (typ _))) (a\
      minductive "wf_b" tt (arity (sort (typ _))) (b\
        mblock [
          [ constructor "wf_ka" (arity a) ]      % <-- missing the list for wf_b
        ]))),
  coq.env.add-indt Bad _
}}.

(* One `minductive` binder but TWO constructor lists. *)
Fail Elpi Query lp:{{
  Bad =
    minductive-block (
      minductive "wf_c" tt (arity (sort (typ _))) (c\
        mblock [
          [ constructor "wf_kc" (arity c) ],
          [ ]                                     % <-- one extra, no component
        ])),
  coq.env.add-indt Bad _
}}.

End WellFormedness.
