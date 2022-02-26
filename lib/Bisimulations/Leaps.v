Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Compare_dec.
Import List.ListNotations.

Require Import Leapfrog.P4automaton.
Require Import Leapfrog.FinType.
Require Import Leapfrog.ConfRel.
Require Import Leapfrog.Relations.
Require Leapfrog.Bisimulations.Semantic.

Require Import Coq.Numbers.BinNums.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.

Module BS := Leapfrog.Bisimulations.Semantic.


Section Leaps.
  Variable (a: p4automaton).
  Notation conf := (configuration a).

  Definition leap_size (q1 q2: conf) : N :=
    match conf_state q1, conf_state q2 with
    | inl s1, inl s2 => N.min (configuration_room_left q1) (configuration_room_left q2)
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
            (N.of_nat (length buf)) = leap_size q1 q2 ->
            R (follow q1 buf) (follow q2 buf)) ->
        close_interpolate R (step q1 b) (step q2 b).

  CoInductive bisimilar_with_leaps: rel conf :=
  | Bisimilar:
      forall q1 q2,
        (accepting q1 <-> accepting q2) ->
        (forall buf,
          (N.of_nat (length buf)) = leap_size q1 q2 ->
          bisimilar_with_leaps (follow q1 buf) (follow q2 buf)) ->
        bisimilar_with_leaps q1 q2.

End Leaps.
