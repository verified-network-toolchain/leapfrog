Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.SimpleSplit.
Require Import ZArith List Bool.

From Hammer Require Import Tactics.
From Hammer Require Import Hammer.

Definition possibly_unsound_init_rel
  : crel (Simple.state + Split.state) (Sum.H Simple.header Split.header)
  :=
    (mk_init 100 SimpleSplit.aut Simple.Start Split.StSplit1). 

Lemma prebisim_simple_split_sym_small_init_leap:
  pre_bisimulation SimpleSplit.aut
                   (WPSymLeap.wp (H:=SimpleSplit.header))
                   (separated _ _ _ SimpleSplit.aut)
                   nil
                   possibly_unsound_init_rel
                   (inl (inl Simple.Start), [], [])
                   (inl (inr Split.StSplit1), [], []).
Proof.
  set (r := possibly_unsound_init_rel).
  cbv in r.
  subst r.
  time repeat (idtac "..."; time solve_bisim).
  repeat (unfold interp_conf_rel, interp_conf_state, interp_state_template || cbn).
  intuition eauto;
    firstorder (try congruence);
    sauto limit:5000.
Qed.

