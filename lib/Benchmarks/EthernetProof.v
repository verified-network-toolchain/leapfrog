Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.Ethernet.

Declare ML Module "mirrorsolve".
SetSMTSolver "cvc4".


Lemma ethernet_equiv:
  lang_equiv_state
    (P4A.interp Reference.aut)
    (P4A.interp Combined.aut)
    Reference.SPref
    Combined.Parse.
Proof.
  solve_lang_equiv_state_axiom Reference.state_eqdec Combined.state_eqdec false.
Qed.
