Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Compare_dec.
Import List.ListNotations.

Require Import Leapfrog.P4automaton.
Require Import Leapfrog.FinType.
Require Import Leapfrog.ConfRel.
Require Import Leapfrog.Relations.
Require Leapfrog.Bisimulations.Semantic.
Module BS := Leapfrog.Bisimulations.Semantic.

Section Leaps.
  Variable (a: p4automaton).
  Notation conf := (configuration a).

  (* Minimal number of steps to be taken from a pair of states before a
     state-to-state transition can be triggered, i.e., when one of the buffers
     is filled up. *)
  Definition leap_size (q1 q2: conf) : nat :=
    match conf_state q1, conf_state q2 with
    | inl s1, inl s2 => min (configuration_room_left q1) (configuration_room_left q2)
    | inl s1, inr _ => configuration_room_left q1
    | inr _, inl s2 => configuration_room_left q2
    | inr _, inr _ => 1
    end.

  (* Closure operation on bisimulations which is the basis which lets us
     instantiate "bisimulation up-to interpolation", an intermediate step
     relating bisimulations to bisimulations with leaps. *)
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

  (* Co-inductive definition of bisimilarity with leaps, later shown to be
     equivalent to the up-to based definition given above. *)
  CoInductive bisimilar_with_leaps: rel conf :=
  | Bisimilar:
      forall q1 q2,
        (accepting q1 <-> accepting q2) ->
        (forall buf,
          length buf = leap_size q1 q2 ->
          bisimilar_with_leaps (follow q1 buf) (follow q2 buf)) ->
        bisimilar_with_leaps q1 q2.

End Leaps.
