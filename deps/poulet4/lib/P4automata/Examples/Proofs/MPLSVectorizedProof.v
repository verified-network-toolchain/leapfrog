Require Import Poulet4.P4automata.Examples.ProofHeader.
Require Import Poulet4.P4automata.Examples.MPLSVectorized.

Lemma prebisim_mpls_unroll:
  pre_bisimulation MPLSVect.aut
                   (WPSymLeap.wp (H:=_))
                   (separated _ _ _ MPLSVect.aut)
                   nil
                   (mk_init 10 MPLSVect.aut MPLSPlain.ParseMPLS MPLSUnroll.ParseMPLS0)
                   (inl (inl MPLSPlain.ParseMPLS), [], [])
                   (inl (inr MPLSUnroll.ParseMPLS0), [], []).
Proof.
  set (rel0 := mk_init 10 MPLSVect.aut MPLSPlain.ParseMPLS MPLSUnroll.ParseMPLS0).
  cbv in rel0.
  subst rel0.
  fail 1.
  time (repeat solve_bisim_plain).
  cbv in *.
  intuition (try congruence).
Time Qed. 

