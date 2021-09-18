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
Require Poulet4.P4automata.Bisimulations.Semantic.
Module BS := Poulet4.P4automata.Bisimulations.Semantic.
Require Import Poulet4.P4automata.Bisimulations.Upto.

Section UptoProofs.
  Variable (a: p4automaton).
  Notation conf := (configuration a).

  Lemma bisimilar_implies_bisimilar_upto
        (f: rel conf -> rel conf)
    :
      SoundClosure a f ->
      forall c1 c2,
        BS.bisimilar a c1 c2 ->
        bisimilar_upto a f c1 c2
  .
  Proof.
    intros.
    destruct H0 as [R [? ?]].
    exists R; split; auto.
    intros c1' c2' ?; split.
    - now apply H0.
    - intros.
      now apply H, H0.
  Qed.

  Lemma bisimilar_upto_implies_bisimilar
        (f: rel conf -> rel conf)
    :
      SoundClosure a f ->
      forall c1 c2,
        bisimilar_upto a f c1 c2 ->
        BS.bisimilar a c1 c2
  .
  Proof.
    intros.
    destruct H0 as [R [? ?]].
    exists (f R); split.
    - intros c1' c2' ?; split.
      + revert c1' c2' H2.
        now apply H, H0.
      + revert c1' c2' H2.
        now apply H, H0.
    - now apply closure_sound_extends.
  Qed.

  (* Sanity check: the identity function is a valid closure. *)
  Definition close_id (R: rel conf) := R.

  Program Instance close_id_sound
    : SoundClosure a close_id
  .
  Solve Obligations with firstorder.
End UptoProofs.
