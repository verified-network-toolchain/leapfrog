Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.SelfComparison.

Declare ML Module "mirrorsolve".
SetSMTSolver "cvc4".
SetSMTLang "BV".

Module Positive.
  Lemma equiv_read_undef:
    lang_equiv_state
        (P4A.interp ReadUndef.aut)
        (P4A.interp ReadUndef.aut)
        ReadUndef.ParseEth
        ReadUndef.ParseEth.
  Proof.
    solve_lang_equiv_state_axiom ReadUndef.state_eqdec ReadUndef.state_eqdec false.
  Time Qed.
End Positive.

Module Negative.
  Lemma equiv_read_undef:
    lang_equiv_state
        (P4A.interp ReadUndefIncorrect.aut)
        (P4A.interp ReadUndefIncorrect.aut)
        ReadUndefIncorrect.ParseEth
        ReadUndefIncorrect.ParseEth.
  Proof.
    Fail solve_lang_equiv_state_axiom ReadUndefIncorrect.state_eqdec ReadUndefIncorrect.state_eqdec false.
  Time Abort.
End Negative.
