Require Import Poulet4.P4automata.Examples.ProofHeader.
Require Import Poulet4.P4automata.Examples.MPLSVectorized.

Lemma prebisim_mpls_vect_unroll:
  pre_bisimulation MPLSVectUnroll.aut
                   (WPSymLeap.wp (H:=_))
                   (separated _ _ _ _)
                   nil
                   (mk_init 10 MPLSVectUnroll.aut MPLSPlain.ParseMPLS MPLSInline.ParseMPLS)
                   (inl (inl MPLSPlain.ParseMPLS), [], [])
                   (inl (inr MPLSInline.ParseMPLS), [], []).
Proof.
  set (rel0 := mk_init 10 MPLSVectUnroll.aut MPLSPlain.ParseMPLS MPLSInline.ParseMPLS).
  cbv in rel0.
  subst rel0.
  time (repeat (time solve_bisim)).
  cbv in *.
  intuition (try congruence).
Time Qed.
