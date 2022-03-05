Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.Edge.


Declare ML Module "mirrorsolve".

Notation H := (Plain.header + Plain.header).
Notation A := (Sum.sum Plain.aut Plain.aut).
Notation conf := (P4automaton.configuration (P4A.interp A)).
Notation start_left := (Plain.ParseEth0).
Notation start_right := (Plain.ParseEth0).

Lemma edge_self_equiv:
  lang_equiv_state
    (P4A.interp Plain.aut)
    (P4A.interp Plain.aut)
    Plain.ParseEth0
    Plain.ParseEth0.
Proof.
  solve_lang_equiv_state_admit Plain.state_eqdec Plain.state_eqdec true.
Time Admitted.
