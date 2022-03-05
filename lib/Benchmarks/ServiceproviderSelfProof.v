Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.ServiceProvider.

Require Import Coq.Arith.PeanoNat.

Declare ML Module "mirrorsolve".

SetSMTSolver "cvc4".

Lemma serviceprovider_self_equiv:
  lang_equiv_state
    (P4A.interp Plain.aut)
    (P4A.interp Plain.aut)
    Plain.ParseEth
    Plain.ParseEth.
Proof.
  solve_lang_equiv_state_admit Plain.state_eqdec Plain.state_eqdec true.
Time Admitted.
