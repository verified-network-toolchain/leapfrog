Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Compare_dec.
Import List.ListNotations.

Require Import Leapfrog.P4automaton.
Require Import Leapfrog.FinType.
Require Import Leapfrog.ConfRel.
Require Import Leapfrog.Relations.
Require Leapfrog.Bisimulations.Semantic.
Module BS := Leapfrog.Bisimulations.Semantic.

Section Upto.
  Variable (a: p4automaton).
  Notation conf := (configuration a).
  Definition bisimulation_upto
             (f: rel conf -> rel conf)
             (R: rel conf)
    :=
      forall c1 c2,
        R c1 c2 ->
        (accepting c1 <-> accepting c2) /\
        forall b, f R (step c1 b) (step c2 b)
  .

  Definition bisimilar_upto
             (f: rel conf -> rel conf)
             (c1 c2: conf)
    :=
      exists R, bisimulation_upto f R /\ R c1 c2
  .

  Definition closure_extends
             (close: rel conf -> rel conf)
    :=
      forall (R: rel conf) c1 c2,
        R c1 c2 -> close R c1 c2
  .

  Definition closure_preserves_accept
             (close: rel conf -> rel conf)
    :=
      forall (R: rel conf),
        (forall c1 c2, R c1 c2 -> accepting c1 <-> accepting c2) ->
        (forall c1 c2, close R c1 c2 -> accepting c1 <-> accepting c2)
  .

  Definition closure_preserves_transition
             (close: rel conf -> rel conf)
    :=
      forall (R: rel conf),
        (forall c1 c2, R c1 c2 ->
                  forall b, close R (step c1 b) (step c2 b)) ->
        (forall c1 c2, close R c1 c2 ->
                  forall b, close R (step c1 b) (step c2 b))
  .

  Definition closure_mono
             (close: rel conf -> rel conf)
    :=
      forall (R R': rel conf),
        (forall c1 c2, R c1 c2 -> R' c1 c2) ->
        (forall c1 c2, close R c1 c2 -> close R' c1 c2)
  .

  Class SoundClosure
        (f: rel conf -> rel conf)
    := {
    closure_sound_extends: closure_extends f;
    closure_sound_preserves_accept: closure_preserves_accept f;
    closure_sound_preserves_transition: closure_preserves_transition f;
    closure_sound_mono: closure_mono f;
      }.
End Upto.
