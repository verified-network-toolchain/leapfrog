Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.SelfComparison.

Declare ML Module "mirrorsolve".
SetSMTSolver "cvc4".

Module Positive.

  ClearEnvCtors.

  Lemma equiv_read_undef:
    lang_equiv_state
        (P4A.interp ReadUndef.aut)
        (P4A.interp ReadUndef.aut)
        ReadUndef.ParseEth
        ReadUndef.ParseEth.
  Proof.
    solve_lang_equiv_state.
  Time Qed.
End Positive.

Module Negative.

  ClearEnvCtors.
  Lemma equiv_read_undef:
    lang_equiv_state
        (P4A.interp ReadUndef.aut)
        (P4A.interp ReadUndef.aut)
        ReadUndef.ParseEth
        ReadUndef.ParseEth.
  Proof.
    Fail solve_lang_equiv_state.
  Time Qed.
End Negative.
