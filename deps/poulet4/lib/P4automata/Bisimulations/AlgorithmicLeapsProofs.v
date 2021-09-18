Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Equality.
Import List.ListNotations.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.Relations.
Require Poulet4.P4automata.Bisimulations.Leaps.
Require Import Poulet4.P4automata.Bisimulations.AlgorithmicLeaps.

Section AlgorithmicLeaps.
  Variable (a: p4automaton).
  Notation conf := (configuration a).
  Variable (top: rel conf).
  Variable (top_closed: forall x y b, top x y -> top (step x b) (step y b)).

  Notation "⟦ x ⟧" := (interp_rels top x).
  Notation "R ⊨ S" := (forall q1 q2,
                          ⟦R⟧ q1 q2 ->
                          S q1 q2)
                        (at level 40).

  Lemma algorithmic_leaps_implies_bisimilar_leaps:
    forall R T q1 q2,
      pre_bisimulation a top R T q1 q2 ->
      Leaps.bisimilar_with_leaps a q1 q2.
  Proof.
    intros.
  Abort.
  
End AlgorithmicLeaps.
