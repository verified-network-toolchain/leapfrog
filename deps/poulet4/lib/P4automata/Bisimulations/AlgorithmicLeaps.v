Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Equality.
Import List.ListNotations.

Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.Relations.

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

  Reserved Notation "R ⇝ S" (at level 10).
  Inductive pre_bisimulation : rels conf -> rels conf -> rel conf :=
  | PreBisimulationClose:
      forall R q1 q2,
        ⟦R⟧ q1 q2 ->
        R ⇝ [] q1 q2
  | PreBisimulationSkip:
      forall R T (C: relation conf) q1 q2,
        R ⊨ C ->
        R ⇝ T q1 q2 ->
        R ⇝ (C :: T) q1 q2
  | PreBisimulationExtend:
      forall (R T: rels conf) (C: rel conf) (W: rels conf) q1 q2,
        ~(R ⊨ C) ->
        (C :: R) ⇝ (W ++ T) q1 q2 ->
        (forall q1 q2,
            ⟦W⟧ q1 q2 ->
            (forall bs,
                length bs = Nat.min
                              (configuration_room_left q1)
                              (configuration_room_left q2) ->
                C (follow q1 bs) (follow q2 bs))) ->
        R ⇝ (C :: T) q1 q2
  where "R ⇝ S" := (pre_bisimulation R S).

End AlgorithmicLeaps.
