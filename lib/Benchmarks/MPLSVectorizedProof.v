Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.MPLSVectorized.

Lemma mpls_equiv:
  lang_equiv_state
    (P4A.interp Plain.aut)
    (P4A.interp Unrolled.aut)
    Plain.ParseMPLS
    Unrolled.ParseMPLS.
Proof.

  time "mpls no hc" solve_lang_equiv_state_axiom Plain.state_eqdec Unrolled.state_eqdec false.
  (* time "mpls hc" solve_lang_equiv_state_axiom Plain.state_eqdec Unrolled.state_eqdec true. *)

Time Qed.

