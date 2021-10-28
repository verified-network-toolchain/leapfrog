Require Import Coq.Lists.List.
Import List.ListNotations.

Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.Relations.
Require Import Poulet4.P4automata.WPProofs.
Require Import Poulet4.P4automata.Bisimulations.Leaps.
Require Import Poulet4.P4automata.Bisimulations.LeapsProofs.
Require Import Poulet4.P4automata.Bisimulations.AlgorithmicLeaps.
Require Import Poulet4.P4automata.Bisimulations.AlgorithmicLeapsProofs.
Require Import Poulet4.P4automata.Bisimulations.WPLeaps.
Require Import Poulet4.P4automata.Reachability.
Require Import Poulet4.P4automata.Syntax.
Require Import Poulet4.Utils.

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

  Variable (s1: S1).
  Variable (s2: S2).
  Definition r := reachable_states a (length (valid_state_pairs a)) s1 s2.

  Notation conf := (configuration (P4A.interp a)).

  Definition top q1 q2 := In (conf_to_state_template q1, conf_to_state_template q2) r.

  Notation "⟦ x ⟧" := (interp_crel a top x).
  Notation "⦇ x ⦈" := (interp_conf_rel a x).
  Notation "R ⊨ q1 q2" := (⟦R⟧ q1 q2) (at level 40).
  Notation "R ⊨ S" := (interp_entailment a top {| e_prem := R; e_concl := S |}) (at level 40).
  Notation δ := step.

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
    - now apply AlgorithmicLeaps.PreBisimulationClose.
    - apply AlgorithmicLeaps.PreBisimulationSkip.
      + intros.
        destruct H0; [|contradiction].
        now apply i.
      + apply IHpre_bisimulation.
    - eapply AlgorithmicLeaps.PreBisimulationExtend.
      + intro.
        destruct H0; [contradiction|].
        apply n.
        unfold interp_entailment; simpl; intros.
        now apply H4.
      + fold (map (interp_conf_rel a) T).
        rewrite map_cons, map_app in IHpre_bisimulation.
        exact IHpre_bisimulation.
      + intros.
        eapply wp_safe; auto.
        rewrite <- H2.
        exact H4.
  Qed.

  Lemma not_equally_accepting_correct q1 q2:
    not_equally_accepting S1 S2 H a (conf_to_state_template q1,
                                     conf_to_state_template q2) = false ->
    accepting q1 <-> accepting q2.
  Proof.
    unfold not_equally_accepting, accepting; simpl; intros.
    destruct (conf_state q1), (conf_state q2);
    try destruct b; try destruct b0;
    split; intros; congruence.
  Qed.

  Lemma mk_init_accepting:
    forall (q1 q2: conf),
      ⟦mk_init _ _ _ _ (length (valid_state_pairs a)) s1 s2⟧ q1 q2 ->
      (accepting q1 <-> accepting q2).
  Proof.
    intros.
    apply not_equally_accepting_correct, Bool.not_true_iff_false; intro.
    apply interp_crel_nodup, interp_crel_quantify in H0; destruct H0.
    specialize (H2 (mk_rel _ _ _ _ (conf_to_state_template q1,
                                    conf_to_state_template q2))).
    modus_ponens H2; [ apply in_map, filter_In; intuition |].
    unfold interp_conf_rel in H2; simpl interp_store_rel in H2.
    modus_ponens H2; [ vm_compute; intuition |].
    simpl bval in H2; now specialize (H2 tt).
  Qed.

  Lemma top_closed q1 q2 bs:
    length bs = reads_left (conf_to_state_template q1,
                            conf_to_state_template q2) ->
    top q1 q2 ->
    top (follow q1 bs) (follow q2 bs).
  Proof.
    unfold top, r, reachable_states; intros.
    eapply reachable_states_closed.
    - intros; destruct H2; try contradiction; subst.
      unfold valid_state_pair, valid_state_template; simpl.
      split; apply Syntax.t_has_extract.
    - exact H1.
    - unfold reachable_step.
      apply nodup_In; simpl.
      rewrite app_nil_r, in_app_iff; left.
      unfold reachable_pair_step, reachable_pair_step'.
      apply in_prod; rewrite <- H0; simpl.
      + eapply advance_correct; try typeclasses eauto; rewrite H0.
        * intros; apply reads_left_upper_bound with (s := s); auto.
        * apply reads_left_lower_bound.
      + eapply advance_correct; try typeclasses eauto; rewrite H0;
        setoid_rewrite reads_left_commutative.
        * intros; apply reads_left_upper_bound with (s := s); auto.
        * apply reads_left_lower_bound.
  Qed.

  Lemma wp_leaps_implies_bisim_leaps:
    forall q1 q2,
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
      erewrite mk_init_accepting.
      + reflexivity.
      + unfold interp_crel; rewrite interp_rels_intersect_top.
        exact H2.
    - simpl interp_rels at 1.
      unfold follow_closed; intros.
      apply top_closed.
      + rewrite H2.
        unfold leap_size, reads_left; simpl.
        unfold configuration_room_left; simpl.
        destruct (conf_state q0), (conf_state q3);
        now autorewrite with size'.
      + intuition.
    - replace [] with (map (interp_conf_rel a) []) by reflexivity.
      now apply pre_bisimulation_embed.
  Qed.

End WPLeapsProofs.
