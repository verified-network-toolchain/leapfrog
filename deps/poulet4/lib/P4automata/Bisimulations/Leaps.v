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
Require Poulet4.P4automata.Bisimulations.Upto.
Require Poulet4.P4automata.Bisimulations.Semantic.
Module BS := Poulet4.P4automata.Bisimulations.Semantic.

Section Leaps.
  Variable (a: p4automaton).
  Notation conf := (configuration a).

  Definition leap_size (q1 q2: conf) : nat :=
    match conf_state q1, conf_state q2 with
    | inl s1, inl s2 => min (configuration_room_left q1) (configuration_room_left q2)
    | inl s1, inr _ => configuration_room_left q1
    | inr _, inl s2 => configuration_room_left q2
    | inr _, inr _ => 1
    end.

  Inductive close_interpolate (R: rel conf) : rel conf :=
    | InterpolateBase:
        forall q1 q2,
          R q1 q2 -> close_interpolate _ q1 q2
    | InterpolateStep
        (q1 q2: conf)
        (b: bool):
        close_interpolate R q1 q2 ->
        (forall buf,
            length buf = leap_size q1 q2 ->
            R (follow q1 buf) (follow q2 buf)) ->
        close_interpolate R (step q1 b) (step q2 b).

  CoInductive bisimilar_with_leaps: rel conf :=
  | Bisimilar:
      forall q1 q2,
        (accepting q1 <-> accepting q2) ->
        (forall buf,
          length buf = leap_size q1 q2 ->
          bisimilar_with_leaps (follow q1 buf) (follow q2 buf)) ->
        bisimilar_with_leaps q1 q2.

End Leaps.
