Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Lists.List.
Import List.ListNotations.

Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.Relations.
Require Poulet4.P4automata.Bisimulations.SemanticCoinductive.
Module BC := Poulet4.P4automata.Bisimulations.SemanticCoinductive.
Require Import Poulet4.P4automata.Bisimulations.Algorithmic.

Section AlgorithmicProofs.
  Variable (a: p4automaton).
  Notation conf := (configuration a).
  Variable (top: rel conf).
  Variable (top_closed: forall x y b, top x y -> top (step x b) (step y b)).

  Notation "⟦ x ⟧" := (interp_rels top x).
  Notation "R ⊨ S" := (forall (q1 q2: conf),
                          ⟦R⟧ q1 q2 ->
                          S q1 q2: Prop)
                        (at level 40).

  Lemma interp_rels_top:
    forall R x y,
      ⟦R⟧ x y ->
      top x y.
  Proof.
    induction R.
    - simpl in *.
      eauto.
    - simpl in *.
      firstorder.
  Qed.

  Lemma fold_right_conj:
    forall A (r: rel A) (R: list (rel A)) x y,
      fold_right relation_conjunction r R x y <->
      r x y /\ fold_right relation_conjunction rel_true R x y.
  Proof.
    induction R; intros; simpl.
    - unfold rel_true.
      tauto.
    - split; cbn; intuition.
  Qed.

  Lemma interp_rels_app:
    forall R S x y,
      ⟦R ++ S⟧ x y <->
      ⟦R⟧ x y /\
      ⟦S⟧ x y.
  Proof.
    intros.
    split; intros.
    - assert (top x y) by (apply fold_right_conj in H; tauto).
      split.
      + apply in_interp_rels; auto.
        intros.
        eapply interp_rels_in; eauto with datatypes.
      + apply in_interp_rels; auto.
        intros.
        eapply interp_rels_in; eauto with datatypes.
    - destruct H.
      assert (top x y) by (apply fold_right_conj in H; tauto).
      apply in_interp_rels; auto.
      intros.
      apply in_app_or in H2;
        destruct H2;
        eapply interp_rels_in in H2;
        eauto with datatypes.
  Qed.

  Lemma sem_pre_implies_sem_bisim' :
    forall R T,
      (forall q1 q2, ⟦R ++ T⟧ q1 q2 -> accepting q1 <-> accepting q2) ->
      (forall q1 q2, ⟦R ++ T⟧ q1 q2 -> forall b, ⟦R⟧ (step q1 b) (step q2 b)) ->
      forall q1 q2,
        pre_bisimulation a top R T q1 q2 ->
        BC.bisimilar a q1 q2
  .
  Proof.
    idtac.
    intros.
    induction H1.
    - revert q1 q2 H1.
      cofix CH; intros.
      apply BC.Bisimilar.
      + apply H.
        rewrite app_nil_r.
        apply H1.
      + intros.
        apply CH.
        apply H0.
        rewrite app_nil_r.
        apply H1.
    - apply IHpre_bisimulation.
      + intros.
        apply H.
        rewrite interp_rels_app in *.
        cbn.
        intuition.
        destruct H1; simpl in H2; [|contradiction].
        auto.
      + intros.
        apply H0.
        rewrite interp_rels_app in *.
        cbn.
        intuition.
        destruct H1; simpl in H2; [|contradiction].
        auto.
    - apply IHpre_bisimulation.
      + intros.
        apply H.
        rewrite !interp_rels_app in *.
        cbn in *.
        intuition.
      + intros.
        rewrite !interp_rels_app in *.
        simpl.
        cbn.
        intuition.
        eapply H0.
        rewrite !interp_rels_app in *.
        cbn in *.
        intuition.
  Qed.

  Lemma sem_pre_implies_sem_bisim :
    forall T,
      (forall q1 q2, ⟦T⟧ q1 q2 -> accepting q1 <-> accepting q2) ->
      forall q1 q2,
        pre_bisimulation a top [] T q1 q2 ->
        BC.bisimilar a q1 q2.
  Proof.
    intros.
    eapply sem_pre_implies_sem_bisim' with (R:=[]) (T:=T); eauto.
    intros.
    apply top_closed.
    eauto using interp_rels_top.
  Qed.

End AlgorithmicProofs.
