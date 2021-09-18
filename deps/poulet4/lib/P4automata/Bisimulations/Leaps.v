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
Require Poulet4.P4automata.WPSymLeap.
Require Poulet4.P4automata.Reachability.
Require Poulet4.P4cub.Utiliser.
Require Poulet4.P4automata.Bisimulations.Upto.
Require Poulet4.P4automata.Bisimulations.Semantic.
Module BS := Poulet4.P4automata.Bisimulations.Semantic.

Section Leaps.
  Variable (a: p4automaton).
  Notation conf := (configuration a).

  Inductive close_interpolate (R: rel conf) : rel conf :=
    | InterpolateBase:
        forall c1 c2,
          R c1 c2 -> close_interpolate _ c1 c2
    | InterpolateStep
        (c1 c2: conf)
        (s1 s2: states a)
        (b: bool)
        (H1: configuration_has_room c1)
        (H2: configuration_has_room c2):
        conf_state c1 = inl s1 ->
        conf_state c2 = inl s2 ->
        close_interpolate R c1 c2 ->
        (forall buf,
            length buf = min
              (configuration_room_left c1)
              (configuration_room_left c2) ->
            R (follow c1 buf) (follow c2 buf)) ->
        close_interpolate R (step c1 b) (step c2 b)
  .

  Definition bisimulation_with_leaps
             (R: rel conf)
    :=
      forall c1 c2,
        R c1 c2 ->
        (accepting c1 <-> accepting c2) /\
        forall buf,
          length buf = min
            (configuration_room_left c1)
            (configuration_room_left c2) ->
          R (follow c1 buf) (follow c2 buf)
  .

  Definition bisimilar_with_leaps (c1 c2: conf) :=
    exists R,
      R c1 c2 /\ bisimulation_with_leaps R
  .
End Leaps.
