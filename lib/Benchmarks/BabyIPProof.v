Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.BabyIP.

Lemma babyip_equiv:
  lang_equiv_state
    (P4A.interp BabyIP1.aut)
    (P4A.interp BabyIP2.aut)
    BabyIP1.Start
    BabyIP2.Start.
Proof.
  solve_lang_equiv_state_admit BabyIP1.state_eqdec BabyIP2.state_eqdec false.
Time Admitted.
Print Assumptions babyip_equiv.
