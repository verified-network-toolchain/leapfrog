Require Import Coq.Lists.List.

Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.FinType.
Require Import Poulet4.Relations.

Section Semantic.
  Variable (a: p4automaton).
  Notation conf := (configuration a).

  Definition bisimulation (R: rel conf) :=
    forall q1 q2,
      R q1 q2 ->
      (accepting q1 <-> accepting q2) /\
      forall b, R (step q1 b) (step q2 b).

  Definition bisimilar q1 q2 :=
    exists R, bisimulation R /\ R q1 q2.

  Lemma bisimilar_implies_equiv :
    forall (c1 c2: conf),
      bisimilar c1 c2 ->
      lang_equiv c1 c2.
  Proof.
    intros.
    unfold lang_equiv.
    intros; revert c1 c2 H.
    induction input; intros.
    - unfold accepted.
      simpl.
      unfold bisimilar in H.
      destruct H as [R [? ?]].
      now apply H in H0.
    - unfold accepted.
      autorewrite with follow.
      apply IHinput.
      unfold bisimilar in H.
      destruct H as [R [? ?]].
      exists R.
      apply H in H0.
      easy.
  Qed.

  Lemma lang_equiv_is_bisimulation :
      bisimulation lang_equiv
  .
  Proof.
    unfold bisimulation; intros.
    split.
    - apply (H nil).
    - intros.
      unfold lang_equiv in *.
      intros.
      specialize (H (b :: input)).
      apply H.
  Qed.

  Lemma equiv_implies_bisimilar:
    forall c1 c2: conf,
      lang_equiv c1 c2 -> bisimilar c1 c2.
  Proof.
    intros.
    exists lang_equiv.
    split; try easy.
    apply lang_equiv_is_bisimulation.
  Qed.

  Theorem bisimilar_iff_lang_equiv:
    forall c1 c2: conf,
      lang_equiv c1 c2 <-> bisimilar c1 c2.
  Proof.
    split.
    - apply equiv_implies_bisimilar.
    - apply bisimilar_implies_equiv.
  Qed.

End Semantic.
