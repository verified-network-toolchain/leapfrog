Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.MPLSVectorizedSmall.

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
  time (repeat (time solve_bisim)).
  cbv in *.
  intuition (try congruence).
Time Qed.


