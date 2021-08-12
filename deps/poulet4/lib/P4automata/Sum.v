Require Coq.Lists.List.
Import List.ListNotations.
Require Coq.Logic.Eqdep_dec.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Program.
Require Import Poulet4.FinType.
Require Import Poulet4.HAList.
Require Poulet4.P4cub.Envn.
Require Poulet4.P4automata.Syntax.

Open Scope list_scope.

Section Sum.
  Set Implicit Arguments.

  (* State identifiers. *)
  Variable (S1: Type).
  Context `{S1_eq_dec: EquivDec.EqDec S1 eq}.
  Context `{S1_finite: @Finite S1 _ S1_eq_dec}.

  Variable (S2: Type).
  Context `{S2_eq_dec: EquivDec.EqDec S2 eq}.
  Context `{S2_finite: @Finite S2 _ S2_eq_dec}.

  (* Header identifiers. *)
  Variable (H1: nat -> Type).
  Context `{H1_eq_dec: forall n, EquivDec.EqDec (H1 n) eq}.
  Definition H1' := Syntax.H' H1.
  Instance H1'_eq_dec: EquivDec.EqDec H1' eq := Syntax.H'_eq_dec (H_eq_dec:=H1_eq_dec).
  Context `{H1_finite: @Finite (Syntax.H' H1) _ H1'_eq_dec}.
  Variable (H2: nat -> Type).
  Context `{H2_eq_dec: forall n, EquivDec.EqDec (H2 n) eq}.
  Definition H2' := Syntax.H' H2.
  Instance H2'_eq_dec: EquivDec.EqDec H2' eq := Syntax.H'_eq_dec (H_eq_dec:=H2_eq_dec).
  Context `{H2_finite: @Finite (Syntax.H' H2) _ H2'_eq_dec}.

  Variable (a1: Syntax.t S1 H1).
  Variable (a2: Syntax.t S2 H2).

  Definition S : Type := S1 + S2.

  Global Instance S_eq_dec: EquivDec.EqDec S eq :=
    ltac:(typeclasses eauto).

  Global Instance S_finite: @Finite S _ S_eq_dec :=
    ltac:(typeclasses eauto).

  Definition H (n: nat) : Type := H1 n + H2 n.

  Definition inl_ (n: nat) : H1 n -> H n := inl.
  Definition inr_ (n: nat) : H2 n -> H n := inr.

  Global Instance H_eq_dec: forall n, EquivDec.EqDec (H n) eq :=
    ltac:(typeclasses eauto).

  Program Definition sum : Syntax.t S H :=
    {| Syntax.t_states s :=
         match s with
         | inl s1 => Syntax.state_fmapSH _ inl inl_ (a1.(Syntax.t_states) s1)
         | inr s2 => Syntax.state_fmapSH _ inr inr_ (a2.(Syntax.t_states) s2)
         end |}.
  Next Obligation.
    destruct a1, a2, s;
      simpl;
      erewrite Syntax.op_fmapH_nonempty; eauto.
  Qed.
  Next Obligation.
    destruct a1, a2, s;
      erewrite Syntax.state_fmapSH_size; eauto.
  Qed.

  Definition inl_sig (h: Syntax.H' H1) : Syntax.H' H :=
    match h with
    | existT _ n h' => existT _ n (inl h')
    end.
  
  Definition inr_sig (h: Syntax.H' H2) : Syntax.H' H :=
    match h with
    | existT _ n h' => existT _ n (inr h')
    end.
  
  Global Program Instance H_finite: @Finite (Syntax.H' H) _ (Syntax.H'_eq_dec (H_eq_dec:=H_eq_dec)) :=
    {| enum := List.map inl_sig (enum (Syntax.H' H1)) ++ List.map inr_sig (enum (Syntax.H' H2)) |}.
  Next Obligation.
    destruct H1_finite, H2_finite.
    apply NoDup_app.
    - apply NoDup_map; auto.
      unfold inl_sig; intros [n x] [m y].
      intro H.
      pose proof H as Hfst.
      inversion H.
      congruence.
    - apply NoDup_map; auto.
      unfold inr_sig; intros [n x] [m y].
      intro H.
      inversion H.
      congruence.
    - unfold not; intros.
      rewrite !List.in_map_iff in *.
      destruct H0 as [[n x'] [Hxeq Hxin]].
      destruct H3 as [[m y'] [Hyeq Hyin]].
      subst.
      inversion Hyeq.
    - unfold not; intros.
      rewrite !List.in_map_iff in *.
      destruct H0 as [[n x'] [Hxeq Hxin]].
      destruct H3 as [[m y'] [Hyeq Hyin]].
      subst.
      inversion Hyeq.
  Qed.
  Next Obligation.
    destruct H1_finite, H2_finite.
    destruct x as [n [x | x]]; pose (existT _ n x) as x'.
    - rewrite List.in_app_iff.
      left.
      rewrite List.in_map_iff.
      exists x'.
      auto.
    - rewrite List.in_app_iff.
      right.
      rewrite List.in_map_iff.
      exists x'.
      auto.
  Qed.

End Sum.
