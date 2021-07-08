Require Coq.Classes.EquivDec.
Require Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.Program.Program.
Require Import Poulet4.P4automata.Syntax.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.Sum.
Require Import Poulet4.P4automata.PreBisimulationSyntax.

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
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [Start; Finish] |}.
  Next Obligation.
    repeat constructor;
      repeat match goal with
             | H: List.In _ [] |- _ => apply List.in_nil in H; exfalso; exact H
             | |- ~ List.In _ [] => apply List.in_nil
             | |- ~ List.In _ (_ :: _) => unfold not; intros
             | H: List.In _ (_::_) |- _ => inversion H; clear H
             | _ => discriminate
             end.
  Qed.
  Next Obligation.
    destruct x; intuition congruence.
  Qed.

  Inductive header :=
  | Pref
  | Suf.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Program Instance header_finite: @Finite header _ header_eq_dec :=
    {| enum := [Pref; Suf] |}.
  Next Obligation.
    repeat constructor;
      repeat match goal with
             | H: List.In _ [] |- _ => apply List.in_nil in H; exfalso; exact H
             | |- ~ List.In _ [] => apply List.in_nil
             | |- ~ List.In _ (_ :: _) => unfold not; intros
             | H: List.In _ (_::_) |- _ => inversion H; clear H
             | _ => discriminate
             end.
  Qed.
  Next Obligation.
    destruct x; intuition congruence.
  Qed.

  Definition states (s: state) :=
    match s with
    | Start =>
      {| st_op := OpExtract 1 (HRVar Pref);
         st_trans := P4A.TSel (CExpr (EHdr (HRVar Pref)))
                              [{| sc_pat := PExact (VBits [true]);
                                  sc_st := inl Finish |}]
                              (inr false) |}
    | Finish =>
      {| st_op := OpExtract 1 (HRVar Suf);
         st_trans := P4A.TGoto _ (inr true) |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End IncrementalBits.

Module BigBits.
  Inductive state :=
  | Parse.
  Global Instance state_eqdec: EquivDec.EqDec state eq.
  vm_compute.
  intros.
  left.
  destruct x; destruct x0; trivial.
  Defined.
  Global Program Instance state_finite: @Finite state _ state_eqdec :=
    {| enum := [Parse] |}.
  Next Obligation.
    repeat constructor;
      repeat match goal with
             | H: List.In _ [] |- _ => apply List.in_nil in H; exfalso; exact H
             | |- ~ List.In _ [] => apply List.in_nil
             | |- ~ List.In _ (_ :: _) => unfold not; intros
             | H: List.In _ (_::_) |- _ => inversion H; clear H
             | _ => discriminate
             end.
  Qed.
  Next Obligation.
    destruct x; intuition congruence.
  Qed.

  Inductive header :=
  | Pref
  | Suf.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Program Instance header_finite: @Finite header _ header_eq_dec :=
    {| enum := [Pref; Suf] |}.
  Next Obligation.
    repeat constructor;
      repeat match goal with
             | H: List.In _ [] |- _ => apply List.in_nil in H; exfalso; exact H
             | |- ~ List.In _ [] => apply List.in_nil
             | |- ~ List.In _ (_ :: _) => unfold not; intros
             | H: List.In _ (_::_) |- _ => inversion H; clear H
             | _ => discriminate
             end.
  Qed.
  Next Obligation.
    destruct x; intuition congruence.
  Qed.

  Definition states (s: state) :=
    match s with
    | Parse =>
      {| st_op := OpSeq
        (OpExtract 1 (HRVar Pref))
        (OpExtract 1 (HRVar Suf));
         st_trans := P4A.TSel (CExpr (EHdr (HRVar Pref)))
                              [{| sc_pat := PExact (VBits [true]);
                                  sc_st := inr true |}]
                              (inr (A := state) false) |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End BigBits.

Module OneBit.
  Inductive state :=
  | Parse.
  Global Instance state_eqdec: EquivDec.EqDec state eq.
  vm_compute.
  intros.
  left.
  destruct x; destruct x0; trivial.
  Defined.
  Global Program Instance state_finite: @Finite state _ state_eqdec :=
    {| enum := [Parse] |}.
  Next Obligation.
    repeat constructor;
      repeat match goal with
             | H: List.In _ [] |- _ => apply List.in_nil in H; exfalso; exact H
             | |- ~ List.In _ [] => apply List.in_nil
             | |- ~ List.In _ (_ :: _) => unfold not; intros
             | H: List.In _ (_::_) |- _ => inversion H; clear H
             | _ => discriminate
             end.
  Qed.
  Next Obligation.
    destruct x; intuition congruence.
  Qed.

  Inductive header :=
  | Pref.

  Global Instance hdr_eqdec: EquivDec.EqDec header eq.
  vm_compute.
  intros.
  left.
  destruct x; destruct x0; trivial.
  Defined.
  Global Program Instance header_finite: @Finite header _ hdr_eqdec :=
    {| enum := [Pref] |}.
  Next Obligation.
    repeat constructor;
      repeat match goal with
             | H: List.In _ [] |- _ => apply List.in_nil in H; exfalso; exact H
             | |- ~ List.In _ [] => apply List.in_nil
             | |- ~ List.In _ (_ :: _) => unfold not; intros
             | H: List.In _ (_::_) |- _ => inversion H; clear H
             | _ => discriminate
             end.
  Qed.
  Next Obligation.
    destruct x; intuition congruence.
  Qed.

  Definition states (s: state) :=
    match s with
    | Parse =>
      {| st_op := (OpExtract 2 (HRVar Pref));
         st_trans := P4A.TSel (CExpr (ESlice (EHdr (HRVar Pref)) 1 0))
                              [{| sc_pat := PExact (VBits [true]);
                                  sc_st := inr true |}]
                              (inr (A := state) false) |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End OneBit.

Module IncrementalSeparate.

  Definition state: Type := Sum.S IncrementalBits.state BigBits.state.
  Global Instance state_eq_dec: EquivDec.EqDec state eq :=
    ltac:(typeclasses eauto).

  Definition header := Sum.H IncrementalBits.header BigBits.header.
  Global Instance header_eq_dec: EquivDec.EqDec header eq :=
    ltac:(typeclasses eauto).
  Global Instance header_finite: @Finite header _ header_eq_dec :=
    ltac:(typeclasses eauto).

  Definition aut := Sum.sum IncrementalBits.aut BigBits.aut.
End IncrementalSeparate.

Module SeparateCombined.
  Definition state: Type := Sum.S BigBits.state OneBit.state.
  Global Instance state_eq_dec: EquivDec.EqDec state eq :=
    ltac:(typeclasses eauto).

  Definition header := Sum.H BigBits.header OneBit.header.
  Global Instance header_eq_dec: EquivDec.EqDec header eq :=
    ltac:(typeclasses eauto).
  Global Instance header_finite: @Finite header _ header_eq_dec :=
    ltac:(typeclasses eauto).

  Definition aut := Sum.sum BigBits.aut OneBit.aut.
End SeparateCombined.

Module IncrementalCombined.
  Definition state: Type := Sum.S IncrementalBits.state OneBit.state.
  Global Instance state_eq_dec: EquivDec.EqDec state eq :=
    ltac:(typeclasses eauto).

  Definition header := Sum.H IncrementalBits.header OneBit.header.
  Global Instance header_eq_dec: EquivDec.EqDec header eq :=
    ltac:(typeclasses eauto).
  Global Instance header_finite: @Finite header _ header_eq_dec :=
    ltac:(typeclasses eauto).

  Definition aut := Sum.sum IncrementalBits.aut OneBit.aut.
End IncrementalCombined.
