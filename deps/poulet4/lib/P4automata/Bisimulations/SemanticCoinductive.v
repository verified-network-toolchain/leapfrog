Require Import Coq.micromega.Lia.
Require Import Compare_dec.
Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Equality.
Import List.ListNotations.

Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.Relations.
Require Poulet4.P4automata.Reachability.
Require Poulet4.P4cub.Utiliser.
Require Poulet4.P4automata.Bisimulations.Semantic.
Module BS := Poulet4.P4automata.Bisimulations.Semantic.

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
      BS.bisimilar a q1 q2.
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
      BS.bisimilar a q1 q2 ->
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
