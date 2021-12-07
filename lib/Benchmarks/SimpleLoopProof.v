Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.SimpleLoop.

Lemma prebisim_loop_unroll:
  pre_bisimulation comb_aut
                   (WPSymLeap.wp (H:=_))
                   (separated _ _ _ _)
                   nil
                   (mk_init 10 comb_aut Loop.Start LoopUnroll.Start)
                   (inl (inl Loop.Start), [], [])
                   (inl (inr LoopUnroll.Start), [], []).
Proof.
  set (rel0 := mk_init 10 comb_aut Loop.Start LoopUnroll.Start).
  cbv in rel0.
  subst rel0.
  unfold comb_aut.
  time (repeat solve_bisim).
  cbv in *.
  intuition (try congruence).
Time Qed.
