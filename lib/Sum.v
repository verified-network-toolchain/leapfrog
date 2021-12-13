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
  Variable (St1: Type).
  Context `{St1_eq_dec: EquivDec.EqDec St1 eq}.
  Context `{St1_finite: @Finite St1 _ St1_eq_dec}.

  Variable (St2: Type).
  Context `{St2_eq_dec: EquivDec.EqDec St2 eq}.
  Context `{St2_finite: @Finite St2 _ St2_eq_dec}.

  (* Header identifiers. *)
  Variable (Hdr1: Type).
  Variable (sz1 : Hdr1 -> nat).
  Context `{Hdr1_eq_dec: EquivDec.EqDec Hdr1 eq}.
  Context `{Hdr1_finite: @Finite Hdr1 _ Hdr1_eq_dec}.

  Variable (Hdr2: Type).
  Variable (sz2 : Hdr2 -> nat).
  Context `{Hdr2_eq_dec: EquivDec.EqDec Hdr2 eq}.
  Context `{Hdr2_finite: @Finite Hdr2 _ Hdr2_eq_dec}.

  Variable (a1: Syntax.t St1 sz1).
  Variable (a2: Syntax.t St2 sz2).

  Notation St := (St1 + St2)%type.

  Global Instance St_eq_dec: EquivDec.EqDec St eq :=
    ltac:(typeclasses eauto).

  Global Instance St_finite: @Finite St _ St_eq_dec :=
    ltac:(typeclasses eauto).

  Definition H : Type := Hdr1 + Hdr2.

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

  Program Definition sum : Syntax.t St sz :=
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
