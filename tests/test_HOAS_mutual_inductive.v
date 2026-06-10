(* -------------------------------------------------------------------------- *)
(*  Tests for the MUTUAL INDUCTIVE HOAS (see mutind.md).                      *)
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
(*  3b. BUILD a mutual block from HOAS with a NON-UNIFORM parameter.            *)
(*      `n` is non-uniform (cross-recursive occurrences instantiate it to 0).  *)
(*      The from-scratch analogue of mt/mf: the writer threads the shared       *)
(*      non-uniform telescope through ctx_params / env_ar_params / relocation.  *)
(* ========================================================================== *)
Module NonUniformParamBuild.

Elpi Query lp:{{
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
  std.assert-ok! (coq.typecheck-indt-decl D) "nu_a/nu_b ill-typed",
  coq.env.add-indt D _
}}.
Check nu_ka : forall n, nu_b 0 -> nu_a n.
Check nu_kb : forall n, nu_a 0 -> nu_b n.

End NonUniformParamBuild.

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
(*  Additional corner cases.  Each declares a mutual (co)inductive in Coq,     *)
(*  READS it as a block, TYPECHECKS the block, and ROUND-TRIPS it through      *)
(*  coq.env.add-indt in a fresh module (exercising reader + writer together),  *)
(*  plus a targeted property check via coq.env.indt where relevant.           *)
(* ========================================================================== *)

(* C1. Mutual CO-INDUCTIVES (parameterized streams): components carry `ff`. *)
Module CoStreams.

CoInductive cs_a (A : Type) : Type :=
| cs_consa : A -> cs_b A -> cs_a A
with cs_b (A : Type) : Type :=
| cs_consb : A -> cs_a A -> cs_b A.

Elpi Query lp:{{
  coq.locate "cs_a" (indt I),
  coq.env.indt I IsInd _ _ _ _ _,
  std.assert! (IsInd = ff) "cs_a should be co-inductive",
  coq.env.indt-decl I D,
  std.assert-ok! (coq.typecheck-indt-decl D) "cs_a/cs_b ill-typed"
}}.

Module RT.
  Elpi Query lp:{{
    coq.locate "cs_a" (indt I), coq.env.indt-decl I D, coq.env.add-indt D _,
    coq.locate "cs_a" (indt J), coq.env.indt J IsInd _ _ _ _ _,
    std.assert! (IsInd = ff) "round-tripped cs_a must stay co-inductive"
  }}.
End RT.

End CoStreams.

(* C2. PARAMETERIZED with TWO uniform parameters. *)
Module TwoParams.

Inductive tp_a (A B : Type) : Type :=
| tp_mka : A -> tp_b A B -> tp_a A B
with tp_b (A B : Type) : Type :=
| tp_mkb : B -> tp_a A B -> tp_b A B.

Elpi Query lp:{{
  coq.locate "tp_a" (indt I),
  coq.env.indt I _ NParams _ _ _ _,
  std.assert! (NParams = 2) "tp_a should have 2 parameters",
  coq.env.indt-decl I D,
  std.assert! (D = parameter "A" _ _ (_\ parameter "B" _ _ (_\ minductive-block _)))
    "tp_a/tp_b: expected two parameters wrapping the block",
  std.assert-ok! (coq.typecheck-indt-decl D) "tp_a/tp_b ill-typed"
}}.

Module RT.
  Elpi Query lp:{{ coq.locate "tp_a" (indt I), coq.env.indt-decl I D, coq.env.add-indt D _ }}.
End RT.

End TwoParams.

(* C3. INDEXED, THREE components (no params): exercises N=3 with indices. *)
Module Indexed3.

Inductive t3a : nat -> Prop :=
| t3a0 : t3a 0
| t3aS : forall n, t3b n -> t3a (S n)
with t3b : nat -> Prop :=
| t3bS : forall n, t3c n -> t3b (S n)
with t3c : nat -> Prop :=
| t3c0 : t3c 0
| t3cS : forall n, t3a n -> t3c (S n).

(* reading any of the three members yields the same 3-component block *)
Elpi Query lp:{{
  coq.locate "t3a" (indt Ia), coq.env.indt-decl Ia Da,
  coq.locate "t3b" (indt Ib), coq.env.indt-decl Ib Db,
  coq.locate "t3c" (indt Ic), coq.env.indt-decl Ic Dc,
  std.assert! (Da = Db) "t3a vs t3b: blocks differ",
  std.assert! (Db = Dc) "t3b vs t3c: blocks differ",
  std.assert! (Da =
    minductive-block (minductive "t3a" tt _ (_\
                      minductive "t3b" tt _ (_\
                      minductive "t3c" tt _ (_\ mblock _))))) "t3: expected 3-component block",
  std.assert-ok! (coq.typecheck-indt-decl Da) "t3 block ill-typed"
}}.

Module RT.
  Elpi Query lp:{{ coq.locate "t3a" (indt I), coq.env.indt-decl I D, coq.env.add-indt D _ }}.
End RT.

End Indexed3.

(* C4. COMBINATION: a uniform PARAMETER and an INDEX (nat) together. *)
Module ParamIndex.

Inductive pit_a (A : Type) : nat -> Type :=
| pit_l : pit_a A 0
| pit_n : forall n, A -> pit_b A n -> pit_a A (S n)
with pit_b (A : Type) : nat -> Type :=
| pit_fnil : pit_b A 0
| pit_fcons : forall n, pit_a A n -> pit_b A n -> pit_b A (S n).

Elpi Query lp:{{
  coq.locate "pit_a" (indt I),
  coq.env.indt I _ NParams _ _ _ _,
  std.assert! (NParams = 1) "pit_a should have exactly 1 (uniform) parameter",
  coq.env.indt-decl I D,
  std.assert-ok! (coq.typecheck-indt-decl D) "pit_a/pit_b ill-typed"
}}.

Module RT.
  Elpi Query lp:{{ coq.locate "pit_a" (indt I), coq.env.indt-decl I D, coq.env.add-indt D _ }}.
End RT.

End ParamIndex.

(* C5. COMBINATION, built from HOAS: parameter `A` (uniform) + index `nat`,    *)
(*     exercising the writer's index handling directly (not via a read).       *)
Module ParamIndexBuild.

Elpi Query lp:{{
  D =
    parameter "A" explicit (sort (typ _)) (a\
      minductive-block (
        minductive "pix_a" tt (arity (prod `n` {{ nat }} (_\ sort (typ _)))) (pa\
        minductive "pix_b" tt (arity (prod `n` {{ nat }} (_\ sort (typ _)))) (pb\
          mblock [
            [ constructor "pix_a0" (arity (app [pa, {{ 0 }}])),
              constructor "pix_aS"
                (arity (prod `n` {{ nat }} (n\
                   prod _ a (_\ prod _ (app [pb, n]) (_\ app [pa, {{ S lp:n }}]))))) ],
            [ constructor "pix_b0" (arity (app [pb, {{ 0 }}])),
              constructor "pix_bS"
                (arity (prod `n` {{ nat }} (n\
                   prod _ (app [pa, n]) (_\ app [pb, {{ S lp:n }}])))) ]
          ])))),
  std.assert-ok! (coq.typecheck-indt-decl D) "pix_a/pix_b ill-typed",
  coq.env.add-indt D _
}}.
Check pix_aS : forall A n, A -> pix_b A n -> pix_a A (S n).
Check pix_bS : forall A n, pix_a A n -> pix_b A (S n).

End ParamIndexBuild.

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
