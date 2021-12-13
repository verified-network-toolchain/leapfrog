Require Coq.Classes.EquivDec.
Require Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.Program.Program.
Require Import Leapfrog.Syntax.
Require Import Leapfrog.FinType.
Require Import Leapfrog.Sum.
Require Import Leapfrog.Notations.

Open Scope p4a.

Ltac prep_equiv :=
  unfold Equivalence.equiv, RelationClasses.complement in *;
  program_simpl; try congruence.

Obligation Tactic := prep_equiv.

Module IncrementalBits.
  Inductive state :=
  | Start
  | Finish.

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | Pref : header
  | Suf : header.

  Definition sz (h: header): nat :=
    match h with
    | Pref
    | Suf => 1
    end.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition states (s: state) : Syntax.state state sz :=
    match s with
    | Start =>
      {| st_op := extract(Pref);
         st_trans := transition select (| EHdr Pref |) {{
          [| exact #b|1 |] ==> inl Finish ;;;
            reject
          }} ;
      |}
    | Finish =>
      {| st_op := extract(Suf);
         st_trans := transition accept |}
    end.

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (destruct s || destruct h; cbv; Lia.lia).

End IncrementalBits.

Module BigBits.
  Inductive state :=
  | Parse.

  Equations state_eq_dec (h1 h2: state) : {h1 = h2} + {h1 <> h2} :=
  { state_eq_dec Parse Parse := left eq_refl }.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | Pref : header
  | Suf : header.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition sz (h: header): nat :=
    match h with
    | Pref
    | Suf => 1
    end.

  Definition states (s: state) : Syntax.state state sz :=
    match s with
    | Parse =>
      {| st_op :=
          extract(Pref) ;;
          extract(Suf);
         st_trans := transition select (| EHdr Pref |) {{
           [| exact #b|1 |] ==> accept ;;;
            @reject state
          }}
      |}
    end.

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (destruct s || destruct h; cbv; Lia.lia).

End BigBits.

Module OneBit.
  Inductive state :=
  | Parse.

  Equations state_eq_dec (h1 h2: state) : {h1 = h2} + {h1 <> h2} :=
  { state_eq_dec Parse Parse := left eq_refl }.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | Pref : header.

  Equations header_eq_dec (h1 h2: header) : {h1 = h2} + {h1 <> h2} :=
  { header_eq_dec Pref Pref := left eq_refl }.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition sz (h: header): nat :=
    match h with
    | Pref => 2
    end.

  Definition states (s: state) : Syntax.state state sz :=
    match s with
    | Parse =>
      {| st_op := extract(Pref);
         st_trans := transition select (| (EHdr (Hdr_sz := sz) Pref)[0 -- 0] |) {{
           [| exact #b|1 |] ==> accept ;;;
            @reject state
         }}
      |}
    end.

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (destruct s || destruct h; cbv; Lia.lia).

End OneBit.

Module IncrementalSeparate.
  Definition aut := Sum.sum IncrementalBits.aut BigBits.aut.
End IncrementalSeparate.

Module SeparateCombined.
  Definition aut := Sum.sum BigBits.aut OneBit.aut.
End SeparateCombined.

Module IncrementalCombined.
  Definition aut := Sum.sum IncrementalBits.aut OneBit.aut.
End IncrementalCombined.


