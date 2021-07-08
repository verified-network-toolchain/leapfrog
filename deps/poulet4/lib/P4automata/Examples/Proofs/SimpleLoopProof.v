Require Import Poulet4.P4automata.Examples.ProofHeader.
Require Import Poulet4.P4automata.Examples.SimpleLoop.

Lemma prebisim_loop_unroll:
  pre_bisimulation (Sum.sum Loop.aut Loop.aut)
                   (WPSymLeap.wp (H:=_))
                   nil
                   (mk_init 10 (Sum.sum Loop.aut Loop.aut) Loop.Start Loop.Start)
                   (inl (inl Loop.Start), [], [])
                   (inl (inr Loop.Start), [], []).
Proof.
  set (rel0 := mk_init 10 (Sum.sum Loop.aut Loop.aut) Loop.Start Loop.Start).
  cbv in rel0.
  subst rel0.
  time (repeat (time solve_bisim_plain)).
  cbv in *.
  intuition (try congruence).
Time Qed.
