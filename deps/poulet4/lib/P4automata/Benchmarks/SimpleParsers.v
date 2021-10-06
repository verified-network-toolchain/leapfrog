Require Coq.Classes.EquivDec.
Require Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.Program.Program.
Require Import Poulet4.P4automata.Syntax.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.Sum.

Ltac prep_equiv :=
  unfold Equivalence.equiv, RelationClasses.complement in *;
  program_simpl; try congruence.

Obligation Tactic := prep_equiv.

Module ParseOne.
  Inductive state :=
  | Start.
  Equations state_eq_dec (l: state) (r: state) : {l = r} + {l <> r} :=  
  { state_eq_dec Start Start := left eq_refl }.

  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [Start] |}.
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
  | Bit : header 1.

  Equations header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y} :=
  {
    header_eqdec_ _ Bit Bit := left eq_refl ;
  }.

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  Proof.
    solve_eqdec'.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [1].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [ existT _ _ Bit] |}.
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
    | Start =>
      {| st_op := OpExtract (existT _ _ Bit);
         st_trans := TSel (CExpr (EHdr Bit))
                              [{| sc_pat := PExact (VBits 1 (tt, true));
                                  sc_st := inr (A := state) true |}]
                              (inr false) |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End ParseOne.

Module ParseZero.
  Inductive state :=
  | Start.
  Equations state_eq_dec (l: state) (r: state) : {l = r} + {l <> r} :=  
  { state_eq_dec Start Start := left eq_refl }.

  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [Start] |}.
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
  | Bit : header 1.

  Equations header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y} :=
  {
    header_eqdec_ _ Bit Bit := left eq_refl ;
  }.

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  Proof.
    solve_eqdec'.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [1].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [ existT _ _ Bit] |}.
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
    | Start =>
      {| st_op := OpExtract (existT _ _ Bit);
         st_trans := TSel (CExpr (EHdr Bit))
                              [{| sc_pat := PExact (VBits 1 (tt, false));
                                  sc_st := inr (A := state) true |}]
                              (inr false) |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End ParseZero.

Module OneZero.
  Definition state: Type := Sum.S ParseOne.state ParseZero.state.
  Global Instance state_eq_dec: EquivDec.EqDec state eq :=
    ltac:(typeclasses eauto).

  Definition header := Sum.H ParseOne.header ParseZero.header.
  Global Instance header_eq_dec': EquivDec.EqDec (H' header) eq.
  Proof.
    eapply Sum.H'_eq_dec; typeclasses eauto.
  Defined.

  Global Instance header_eq_dec: forall n, EquivDec.EqDec (header n) eq.
  Proof.
    typeclasses eauto.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ (header_eq_dec n).
  Proof.
    typeclasses eauto.
  Defined.

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

  Definition aut := Sum.sum ParseOne.aut ParseZero.aut.
End OneZero.
