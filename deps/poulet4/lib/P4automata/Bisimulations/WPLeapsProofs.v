Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Equality.
Import List.ListNotations.

Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.Relations.
Require Import Poulet4.P4automata.WPProofs.
Require Import Poulet4.P4automata.Bisimulations.Leaps.
Require Import Poulet4.P4automata.Bisimulations.AlgorithmicLeaps.
Require Import Poulet4.P4automata.Bisimulations.AlgorithmicLeapsProofs.
Require Import Poulet4.P4automata.Bisimulations.WPLeaps.
Require Import Poulet4.P4automata.Reachability.

Section WPLeapsProofs.

  (* State identifiers. *)
  Variable (S1: Type).
  Context `{S1_eq_dec: EquivDec.EqDec S1 eq}.
  Context `{S1_finite: @Finite S1 _ S1_eq_dec}.

  Variable (S2: Type).
  Context `{S2_eq_dec: EquivDec.EqDec S2 eq}.
  Context `{S2_finite: @Finite S2 _ S2_eq_dec}.

  Notation S := ((S1 + S2)%type).

  (* Header identifiers. *)
  Variable (H: nat -> Type).
  Context `{H_eq_dec: forall n, EquivDec.EqDec (H n) eq}.
  Context `{H'_eq_dec: EquivDec.EqDec (P4A.H' H) eq}.
  Context `{H_finite: @Finite (Syntax.H' H) _ H'_eq_dec}.

  Variable (a: P4A.t S H).
  Variable (r: list (state_template a * state_template a)).

  Notation conf := (configuration (P4A.interp a)).

  Variable (top: rel conf).
  Variable (top_closed: forall x y b, top x y -> top (step x b) (step y b)).

  Notation "⟦ x ⟧" := (interp_crel a top x).
  Notation "⦇ x ⦈" := (interp_conf_rel a x).
  Notation "R ⊨ q1 q2" := (⟦R⟧ q1 q2) (at level 40).
  Notation "R ⊨ S" := (interp_entailment a top {| e_prem := R; e_concl := S |}) (at level 40).
  Notation δ := step.

  Lemma interp_crel_app:
    forall R1 R2 q1 q2,
      interp_crel a top (R1 ++ R2) q1 q2 <->
      interp_crel a top R1 q1 q2 /\
      interp_crel a top R2 q1 q2.
  Proof.
    intros.
    induction R1; cbn; intuition.
    induction R2; intuition.
  Qed.

  Lemma pre_bisimulation_implies_interp_crel:
    forall R T q1 q2,
      pre_bisimulation a (WP.wp r) top R T q1 q2 ->
      top q1 q2 ->
      interp_crel a top (T ++ R) q1 q2.
  Proof.
    intros.
    induction H0.
    - rewrite app_nil_l.
      apply H0; simpl; auto.
    - destruct H0; [|contradiction].
      specialize (IHpre_bisimulation H1).
      repeat rewrite interp_crel_app in *.
      rewrite interp_crel_cons in *.
      intuition.
    - destruct H0; [contradiction|].
      specialize (IHpre_bisimulation H1).
      repeat rewrite interp_crel_app in *.
      rewrite interp_crel_cons in *.
      intuition.
  Qed.

  Lemma interp_rels_vs_interp_crel:
    forall q1 q2 R,
      interp_rels top (map (interp_conf_rel a) R) q1 q2 <->
      interp_crel a top R q1 q2.
  Proof.
    induction R; intuition.
  Qed.

  Lemma pre_bisimulation_embed:
    forall R T q1 q2,
      pre_bisimulation a (WP.wp r) top R T q1 q2 ->
      AlgorithmicLeaps.pre_bisimulation
        (P4A.interp a)
        top
        (map (interp_conf_rel a) R)
        (map (interp_conf_rel a) T)
        q1 q2.
  Proof.
    intros.
    induction H0.
    - apply AlgorithmicLeaps.PreBisimulationClose.
      now rewrite interp_rels_vs_interp_crel.
    - apply AlgorithmicLeaps.PreBisimulationSkip.
      + intros.
        destruct H0; [|contradiction].
        rewrite interp_rels_vs_interp_crel in H3.
        now apply i.
      + apply IHpre_bisimulation.
    - eapply AlgorithmicLeaps.PreBisimulationExtend.
      + intro.
        destruct H0; [contradiction|].
        apply n.
        unfold interp_entailment; simpl; intros.
        apply H4.
        now rewrite interp_rels_vs_interp_crel.
      + fold (map (interp_conf_rel a) T).
        rewrite map_cons, map_app in IHpre_bisimulation.
        exact IHpre_bisimulation.
      + intros.
        rewrite interp_rels_vs_interp_crel in H4.
        eapply wp_safe; auto.
        rewrite <- H2.
        exact H4.
  Qed.

  Lemma interp_rels_intersect_top:
    forall q1 q2 R,
      interp_rels top R q1 q2 <->
      (top ⊓ interp_rels top R) q1 q2.
  Proof.
    induction R; cbn; intuition.
  Qed.

  Lemma init_vs_accepting:
    forall (q1 q2: conf) s1 s2,
      ⟦mk_init _ _ _ _ (length (valid_state_pairs a)) s1 s2⟧ q1 q2 ->
      top q1 q2 ->
      (accepting q1 <-> accepting q2).
  Proof.
  Admitted.

  Lemma wp_leaps_implies_bisim_leaps:
    forall q1 q2 s1 s2,
      let init := mk_init _ _ _ _ (length (valid_state_pairs a)) s1 s2 in
      pre_bisimulation a (WP.wp r) top [] init q1 q2 ->
      top q1 q2 ->
      bisimilar_with_leaps (P4A.interp a) q1 q2.
  Proof.
    intros.
    apply AlgorithmicLeapsProofs.algorithmic_leaps_implies_bisimilar_leaps
    with (R := []) (T := map (interp_conf_rel a) init) (top := top).
    - simpl interp_rels at 1.
      unfold coaccepting; intros.
      erewrite init_vs_accepting.
      + reflexivity.
      + rewrite <- interp_rels_vs_interp_crel, interp_rels_intersect_top.
        exact H2.
      + destruct H2; apply H2.
    - simpl interp_rels at 1.
      unfold follow_closed; intros.
      clear H2; induction bs using rev_ind.
      + autorewrite with follow; intuition.
      + repeat rewrite follow_append.
        apply top_closed.
        apply IHbs.
    - replace [] with (map (interp_conf_rel a) []) by reflexivity.
      now apply pre_bisimulation_embed.
  Qed.

End WPLeapsProofs.
