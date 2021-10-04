Require Coq.Classes.EquivDec.
Require Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.Program.Program.
Require Import Poulet4.P4automata.Syntax.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.Sum.
Require Import Poulet4.P4automata.Syntax.

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

  Inductive header : nat -> Type :=
  | Pref : header 1
  | Suf : header 1.

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq.
  Proof.
    solve_eqdec.
  Qed.

  Global Instance header_finite: forall n, @Finite (header n) _ (header_eqdec n).
  Proof.
    intros n; solve_indexed_finiteness n [1; 1].
  Qed.

  Global Instance header_eqdec': EquivDec.EqDec {n & header n} eq := Syntax.H'_eq_dec (H_eq_dec:=header_eqdec).

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [ existT _ _ Pref ; existT _ _ Suf] |}.
  Next Obligation.
    repeat constructor;
    unfold "~";
    intros;
    destruct H;
    now inversion H || now inversion H0.
  Qed.
  Next Obligation.
  dependent destruction X; subst;
  repeat (
    match goal with
    | |- ?L \/ ?R => (now left; trivial) || right
    end
  ).
  Qed.

  (*
    These versions of decidable equality do not contain JMeq in their terms.
    For some reason I can't get them to play nice with the other stuff, though...

  Global Instance header_eqdec': EquivDec.EqDec {n & header n} eq.
  Proof.
    unfold EquivDec.EqDec; intros.
    destruct x, y.
    destruct (Nat.eq_dec x x0).
    - subst.
      destruct h, h0.
      + left; congruence.
      + right; intuition; intro.
        apply inj_pair2 in H.
        discriminate.
      + right; intuition; intro.
        apply inj_pair2 in H.
        discriminate.
      + left; congruence.
    - right; congruence.
  Defined.

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq.
  Proof.
    unfold EquivDec.EqDec; intros.
    destruct (header_eqdec' (existT _ n x) (existT _ n y)).
    - apply inj_pair2 in e; now left.
    - right; intro; apply c.
      now rewrite H.
  Defined.

  *)

  Definition states (s: state) :=
    match s with
    | Start =>
      {| st_op := OpExtract (existT _ _ Pref);
         st_trans := TSel (CExpr (EHdr Pref))
                              [{| sc_pat := PExact (VBits 1(tt, true));
                                  sc_st := inl Finish |}]
                              (inr false) |}
    | Finish =>
      {| st_op := OpExtract (existT _ _ Suf);
         st_trans := TGoto _ (inr true) |}
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

  Inductive header : nat -> Type :=
  | Pref : header 1
  | Suf : header 1.

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq.
  Proof.
    solve_eqdec.
  Qed.

  Global Instance header_finite: forall n, @Finite (header n) _ (header_eqdec n).
  Proof.
    intros n; solve_indexed_finiteness n [1; 1].
  Qed.

  Global Instance header_eqdec': EquivDec.EqDec {n & header n} eq := Syntax.H'_eq_dec (H_eq_dec:=header_eqdec).

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [ existT _ _ Pref ; existT _ _ Suf] |}.
  Next Obligation.
    repeat constructor;
    unfold "~";
    intros;
    destruct H;
    now inversion H || now inversion H0.
  Qed.
  Next Obligation.
  dependent destruction X; subst;
  repeat (
    match goal with
    | |- ?L \/ ?R => (now left; trivial) || right
    end
  ).
  Qed.

  Definition states (s: state) :=
    match s with
    | Parse =>
      {| st_op := OpSeq
        (OpExtract (existT _ _ Pref))
        (OpExtract (existT _ _ Suf));
         st_trans := TSel (CExpr (EHdr Pref))
                              [{| sc_pat := PExact (VBits 1 (tt, true));
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

  Inductive header : nat -> Type :=
  | Pref : header 2.

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq.
  Proof.
    solve_eqdec.
  Qed.

  Global Instance header_finite: forall n, @Finite (header n) _ (header_eqdec n).
  Proof.
    intros n; solve_indexed_finiteness n [2].
  Qed.

  Global Instance header_eqdec': EquivDec.EqDec {n & header n} eq := Syntax.H'_eq_dec (H_eq_dec:=header_eqdec).

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [ existT _ _ Pref ] |}.
  Next Obligation.
    repeat constructor;
    unfold "~";
    intros;
    destruct H;
    now inversion H || now inversion H0.
  Qed.
  Next Obligation.
  dependent destruction X; subst;
  repeat (
    match goal with
    | |- ?L \/ ?R => (now left; trivial) || right
    end
  ).
  Qed.

  Definition states (s: state) :=
    match s with
    | Parse =>
      {| st_op := (OpExtract (existT header 2 Pref));
         st_trans := TSel (CExpr (ESlice (n := 2) (EHdr Pref) 0 0))
                              [{| sc_pat := PExact (VBits 1 (tt, true));
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
  Global Instance header_eq_dec: forall n, EquivDec.EqDec (header n) eq :=
    ltac:(typeclasses eauto).

  Global Instance header_finite: forall n, @Finite (header n) _ (header_eq_dec n) :=
    ltac:(typeclasses eauto).
  Global Instance header_eq_dec': EquivDec.EqDec {n & header n} eq :=
    ltac:(typeclasses eauto).

  Global Instance header_finite': @Finite {n & header n} _ header_eq_dec'.
  econstructor.
  - eapply Sum.H_finite.
  - intros.
    simpl.
    destruct x.
    inversion h;
    dependent destruction H;
    dependent destruction h;
    dependent destruction h;
    repeat (
      match goal with
      | |- ?L \/ ?R => (now left; trivial) || right
      end
    ).
  Defined.

  Definition aut := Sum.sum IncrementalBits.aut BigBits.aut.
End IncrementalSeparate.

Module SeparateCombined.
  Definition state: Type := Sum.S BigBits.state OneBit.state.
  Global Instance state_eq_dec: EquivDec.EqDec state eq :=
    ltac:(typeclasses eauto).

  Definition header := Sum.H BigBits.header OneBit.header.
  Global Instance header_eq_dec: forall n, EquivDec.EqDec (header n) eq :=
    ltac:(typeclasses eauto).

  Global Instance header_finite: forall n, @Finite (header n) _ (header_eq_dec n) :=
    ltac:(typeclasses eauto).
  Global Instance header_eq_dec': EquivDec.EqDec {n & header n} eq :=
    ltac:(typeclasses eauto).

  Global Instance header_finite': @Finite {n & header n} _ header_eq_dec'.
  econstructor.
  - eapply Sum.H_finite.
  - intros.
    simpl.
    destruct x.
    inversion h;
    dependent destruction H;
    dependent destruction h;
    dependent destruction h;
    repeat (
      match goal with
      | |- ?L \/ ?R => (now left; trivial) || right
      end
    ).
  Defined.

  Definition aut := Sum.sum BigBits.aut OneBit.aut.
End SeparateCombined.

Module IncrementalCombined.
  Definition state: Type := Sum.S IncrementalBits.state OneBit.state.
  Global Instance state_eq_dec: EquivDec.EqDec state eq :=
    ltac:(typeclasses eauto).

  Definition header := Sum.H IncrementalBits.header OneBit.header.
  Global Instance header_eq_dec: forall n, EquivDec.EqDec (header n) eq :=
    ltac:(typeclasses eauto).

  Global Instance header_finite: forall n, @Finite (header n) _ (header_eq_dec n) :=
    ltac:(typeclasses eauto).
  Global Instance header_eq_dec': EquivDec.EqDec {n & header n} eq :=
    ltac:(typeclasses eauto).

  Global Instance header_finite': @Finite {n & header n} _ header_eq_dec'.
  econstructor.
  - eapply Sum.H_finite.
  - intros.
    simpl.
    destruct x.
    inversion h;
    dependent destruction H;
    dependent destruction h;
    dependent destruction h;
    repeat (
      match goal with
      | |- ?L \/ ?R => (now left; trivial) || right
      end
    ).
  Defined.
End IncrementalCombined.


