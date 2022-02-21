Require Import Leapfrog.FinType.
Require Import Leapfrog.P4automaton.
Require Leapfrog.Syntax.

Require Import MirrorSolve.HLists.

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
  Variable (Hdr1_sz : Hdr1 -> nat).
  Context `{Hdr1_eq_dec: EquivDec.EqDec Hdr1 eq}.
  Context `{Hdr1_finite: @Finite Hdr1 _ Hdr1_eq_dec}.

  Variable (Hdr2: Type).
  Variable (Hdr2_sz : Hdr2 -> nat).
  Context `{Hdr2_eq_dec: EquivDec.EqDec Hdr2 eq}.
  Context `{Hdr2_finite: @Finite Hdr2 _ Hdr2_eq_dec}.

  Variable (a1: Syntax.t St1 Hdr1_sz).
  Variable (a2: Syntax.t St2 Hdr2_sz).

  Notation St := (St1 + St2)%type.

  Global Instance St_eq_dec: EquivDec.EqDec St eq :=
    ltac:(typeclasses eauto).

  Global Instance St_finite: @Finite St _ St_eq_dec :=
    ltac:(typeclasses eauto).

  Definition Hdr : Type := Hdr1 + Hdr2.

  Definition make_transparent {X: Type} (eq_dec: forall (x0 x1: X), {x0 = x1} + {x0 <> x1}) {l r} (opaque_eq: l = r) : l = r :=
    match eq_dec l r with
    | left transparent_eq => transparent_eq
    | _ => opaque_eq
    end.

  Definition Hdr_sz (h: Hdr) : nat :=
    match h with
    | inl h => Hdr1_sz h
    | inr h => Hdr2_sz h
    end.

  Program Definition sum : Syntax.t St Hdr_sz :=
    {| Syntax.t_states s :=
         match s with
         | inl s1 => Syntax.state_fmapSH Hdr_sz inl inl _ (a1.(Syntax.t_states) s1)
         | inr s2 => Syntax.state_fmapSH Hdr_sz inr inr _ (a2.(Syntax.t_states) s2)
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

  Definition sum_stores
             (s1: Syntax.store Hdr1 Hdr1_sz)
             (s2: Syntax.store Hdr2 Hdr2_sz) : Syntax.store Hdr Hdr_sz :=
    HList.app (HList.map_inj (fun h => Syntax.v (Hdr_sz h)) inl s1)
              (HList.map_inj (fun h => Syntax.v (Hdr_sz h)) inr s2).

End Sum.
