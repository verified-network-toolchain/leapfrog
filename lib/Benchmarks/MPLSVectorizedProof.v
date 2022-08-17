Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.MPLSVectorized.

Declare ML Module "mirrorsolve".
SetSMTSolver "z3".
SetSMTLang "BV".

Lemma mpls_equiv:
  lang_equiv_state
    (P4A.interp Plain.aut)
    (P4A.interp Unrolled.aut)
    Plain.ParseMPLS
    Unrolled.ParseMPLS.
Proof.
  solve_lang_equiv_state_axiom Plain.state_eqdec Unrolled.state_eqdec false.
Time Qed.

