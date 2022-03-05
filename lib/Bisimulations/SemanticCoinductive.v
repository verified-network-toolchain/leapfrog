Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Compare_dec.
Import List.ListNotations.

Require Import Leapfrog.P4automaton.
Require Import Leapfrog.FinType.
Require Import Leapfrog.ConfRel.
Require Import Leapfrog.Relations.
Require Leapfrog.Bisimulations.Semantic.
Module BS := Leapfrog.Bisimulations.Semantic.

Section SemanticCoinductive.
  Variable (a: p4automaton).
  Notation conf := (configuration a).
  CoInductive bisimilar : rel conf :=
  | Bisimilar:
      forall q1 q2,
        (accepting q1 <-> accepting q2) ->
        (forall b, bisimilar (step q1 b) (step q2 b)) ->
        bisimilar q1 q2
  .

  Lemma bisimilar_coalg_implies_sem_bisim:
    forall q1 q2,
      bisimilar q1 q2 ->
      BS.bisimilar q1 q2.
  Proof.
    intros.
    exists bisimilar.
    split.
    - unfold BS.bisimulation.
      intros.
      inversion H0; firstorder.
    - tauto.
  Qed.

  Lemma sem_bisim_implies_bisimilar_coalg:
    forall q1 q2,
      BS.bisimilar q1 q2 ->
      bisimilar q1 q2.
  Proof.
    cofix C.
    intros.
    constructor.
    - unfold BS.bisimilar, BS.bisimulation in *.
      firstorder.
    - intros.
      eapply C.
      unfold BS.bisimilar, BS.bisimulation in *.
      firstorder.
  Qed.

End SemanticCoinductive.
