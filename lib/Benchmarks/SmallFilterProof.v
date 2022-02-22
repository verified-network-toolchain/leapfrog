Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.SmallFilter.
Require Leapfrog.SumProofs.

Lemma small_filter_equiv:
  lang_equiv_state
    (P4A.interp IncrementalBits.aut)
    (P4A.interp BigBits.aut)
    IncrementalBits.Start
    BigBits.Parse.
Proof.
  solve_lang_equiv_state_axiom IncrementalBits.state_eqdec BigBits.state_eqdec.
Time Qed.
Print Assumptions small_filter_equiv.
