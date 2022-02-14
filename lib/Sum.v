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
             (s2: Syntax.store Hdr2 Hdr2_sz) : Syntax.store Hdr Hdr_sz.
  Admitted.

  Import P4automaton.

  Require Import Coq.Program.Program.
  Locate "~=".
  Inductive embed_conf1:
    P4automaton.configuration (Syntax.interp a1) ->
    P4automaton.configuration (Syntax.interp sum) ->
    Prop :=
  | EmbedConf1Inl:
    forall q
      st
      (c1: P4automaton.configuration (Syntax.interp a1))
      (c1': P4automaton.configuration (Syntax.interp sum)),
      conf_state c1 = inl q ->
      conf_state c1' = inl (inl q) ->
      conf_buf c1 ~= conf_buf c1' ->
      sum_stores (conf_store c1) st = conf_store c1' ->
      embed_conf1 c1 c1'
  | EmbedConf1Inr:
    forall q
      st
      (c1: P4automaton.configuration (Syntax.interp a1))
      (c1': P4automaton.configuration (Syntax.interp sum)),
      conf_state c1 = inr q ->
      conf_state c1' = inr q ->
      conf_buf c1 ~= conf_buf c1' ->
      sum_stores (conf_store c1) st = conf_store c1' ->
      embed_conf1 c1 c1'.

  Inductive embed_conf2:
    P4automaton.configuration (Syntax.interp a2) ->
    P4automaton.configuration (Syntax.interp sum) ->
    Prop :=
  | EmbedConf2Inl:
    forall q
      st
      (c2: P4automaton.configuration (Syntax.interp a2))
      (c2': P4automaton.configuration (Syntax.interp sum)),
      conf_state c2 = inl q ->
      conf_state c2' = inl (inr q) ->
      conf_buf c2 ~= conf_buf c2' ->
      sum_stores st (conf_store c2) = conf_store c2' ->
      embed_conf2 c2 c2'
  | EmbedConf2Inr:
    forall q
      st
      (c2: P4automaton.configuration (Syntax.interp a2))
      (c2': P4automaton.configuration (Syntax.interp sum)),
      conf_state c2 = inr q ->
      conf_state c2' = inr q ->
      conf_buf c2 ~= conf_buf c2' ->
      sum_stores st (conf_store c2) = conf_store c2' ->
      embed_conf2 c2 c2'.

  Inductive split_bisim (R: P4automaton.configuration (Syntax.interp sum) ->
                            P4automaton.configuration (Syntax.interp sum) ->
                            Prop)
    : P4automaton.configuration (Syntax.interp a1) ->
      P4automaton.configuration (Syntax.interp a2) ->
      Prop :=
  | MkBisim: forall c1 c2 c1' c2',
      embed_conf1 c1 c1' ->
      embed_conf2 c2 c2' ->
      R c1' c2' ->
      split_bisim R c1 c2.

  Lemma embed_accepting1:
    forall c1 c1',
      embed_conf1 c1 c1' ->
      accepting c1 <-> accepting c1'.
  Proof.
    unfold accepting.
    destruct c1, c1'.
    split; intros.
    - inversion H; subst; simpl in *; congruence.
    - inversion H; subst; simpl in *; congruence.
  Qed.

  Lemma embed_accepting2:
    forall c2 c2',
      embed_conf2 c2 c2' ->
      accepting c2 <-> accepting c2'.
  Proof.
    unfold accepting.
    destruct c2, c2'.
    split; intros.
    - inversion H; subst; simpl in *; congruence.
    - inversion H; subst; simpl in *; congruence.
  Qed.
  
  Require Leapfrog.Bisimulations.Semantic.
  Lemma split_is_bisim:
    forall R,
      Semantic.bisimulation R ->
      Semantic.bisimulation (split_bisim R).
  Proof.
    unfold Semantic.bisimulation.
    intros.
    split.
    - inversion H0; subst.
      apply H in H3.
      destruct H3.
      erewrite embed_accepting1 by eauto.
      erewrite embed_accepting2 by eauto.
      auto.
    - admit.
  Admitted.

  Lemma sum_thing:
    forall (q1: St1) (q2: St2),
      P4automaton.lang_equiv_state
        (a1 := Syntax.interp sum)
        (a2 := Syntax.interp sum)
        (inl q1)
        (inr q2) ->
      P4automaton.lang_equiv_state
        (a1 := Syntax.interp a1)
        (a2 := Syntax.interp a2)
        q1
        q2.
  Proof.
    unfold P4automaton.lang_equiv_state.
    intros.
    apply Bisimulations.Semantic.bisimilar_iff_lang_equiv.
    setoid_rewrite Bisimulations.Semantic.bisimilar_iff_lang_equiv in H.
    unfold Semantic.bisimilar.
    simpl in s1, s2.
    pose (sum_stores s1 s2) as s0.
    specialize (H s0 s0).
    destruct H as [R [Hbisim Hrel]].
    exists (split_bisim R).
    split.
    - auto using split_is_bisim.
    - econstructor; eauto.
      + econstructor; simpl; eauto.
        unfold s0.
        reflexivity.
      + econstructor; simpl; eauto.
        unfold s0.
        reflexivity.
  Qed.
  
End Sum.
