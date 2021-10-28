Require Import Coq.micromega.Lia.
Require Import Compare_dec.
Require Import Coq.Lists.List.
Import List.ListNotations.

Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.Relations.

Section Algorithmic.
  Variable (a: p4automaton).
  Notation conf := (configuration a).
  Variable (top: rel conf).
  Variable (top_closed: forall x y b, top x y -> top (step x b) (step y b)).

  Notation "⟦ x ⟧" := (interp_rels top x).
  Notation "R ⊨ S" := (forall (q1 q2: conf),
                          ⟦R⟧ q1 q2 ->
                          S q1 q2: Prop)
                        (at level 40).

  Reserved Notation "R ⇝ S" (at level 10).
  Inductive pre_bisimulation : rels conf -> rels conf -> rel conf :=
  | PreBisimulationClose:
      forall R q1 q2,
        ⟦R⟧ q1 q2 ->
        R ⇝ [] q1 q2
  | PreBisimulationSkip:
      forall R T (C: relation conf) q1 q2 (H: {R ⊨ C} + {~(R ⊨ C)}),
        match H with
        | left _ => True
        | _ => False
        end ->
        R ⇝ T q1 q2 ->
        R ⇝ (C :: T) q1 q2
  | PreBisimulationExtend:
      forall (R T: rels conf) C W q1 q2 (H: {R ⊨ C} + {~(R ⊨ C)}),
        match H with
        | right _ => True
        | _ => False
        end ->
        (C :: R) ⇝ (W ++ T) q1 q2 ->
        (forall q1 q2, ⟦W⟧ q1 q2 -> (forall bit, C (step q1 bit) (step q2 bit))) ->
        R ⇝ (C :: T) q1 q2
  where "R ⇝ S" := (pre_bisimulation R S).
End Algorithmic.
