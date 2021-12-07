Require Coq.Lists.List.
Require Coq.Logic.Eqdep_dec.
Require Import Coq.Classes.EquivDec.
Import List.ListNotations.

Require Import Leapfrog.FinType.
Require Import Leapfrog.HAList.
Require Leapfrog.Syntax.

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
  Variable (H1: Type).
  Variable (sz1 : H1 -> nat).
  Context `{H1_eq_dec: EquivDec.EqDec H1 eq}.
  Context `{H1_finite: @Finite H1 _ H1_eq_dec}.

  Variable (H2: Type).
  Variable (sz2 : H2 -> nat).
  Context `{H2_eq_dec: EquivDec.EqDec H2 eq}.
  Context `{H2_finite: @Finite H2 _ H2_eq_dec}.

  Variable (a1: Syntax.t S1 sz1).
  Variable (a2: Syntax.t S2 sz2).

  Notation S := (S1 + S2)%type.

  Global Instance S_eq_dec: EquivDec.EqDec S eq :=
    ltac:(typeclasses eauto).

  Global Instance S_finite: @Finite S _ S_eq_dec :=
    ltac:(typeclasses eauto).

  Definition H : Type := H1 + H2.

  Definition make_transparent {X: Type} (eq_dec: forall (x0 x1: X), {x0 = x1} + {x0 <> x1}) {l r} (opaque_eq: l = r) : l = r :=
    match eq_dec l r with
    | left transparent_eq => transparent_eq
    | _ => opaque_eq
    end.

  Definition sz (h: H) : nat :=
    match h with
    | inl h => sz1 h
    | inr h => sz2 h
    end.

  Program Definition sum : Syntax.t S sz :=
    {| Syntax.t_states s :=
         match s with
         | inl s1 => Syntax.state_fmapSH sz inl inl _ (a1.(Syntax.t_states) s1)
         | inr s2 => Syntax.state_fmapSH sz inr inr _ (a2.(Syntax.t_states) s2)
         end |}.
  Next Obligation.
    destruct h; simpl.
    - apply a1.
    - apply a2.
  Qed.
  Next Obligation.
    destruct a1, a2, s;
      erewrite Syntax.state_fmapSH_size; eauto.
  Qed.
End Sum.
