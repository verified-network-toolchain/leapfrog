Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.MPLSVectorized.


Lemma mpls_equiv:
  lang_equiv_state
    (P4A.interp Plain.aut)
    (P4A.interp Unrolled.aut)
    Plain.ParseMPLS
    Unrolled.ParseMPLS.
Proof.
  solve_lang_equiv_state Plain.state_eqdec Unrolled.state_eqdec.
Time Qed.

