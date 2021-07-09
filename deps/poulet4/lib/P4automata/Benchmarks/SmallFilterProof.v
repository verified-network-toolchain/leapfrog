Require Import Poulet4.P4automata.Examples.ProofHeader.
Require Import Poulet4.P4automata.Examples.SmallFilter.
From Hammer Require Import Tactics.

Lemma prebisim_incremental_sep:
  pre_bisimulation IncrementalSeparate.aut
                   (WPSymLeap.wp (H:=IncrementalSeparate.header))
                   (separated _ _ _ IncrementalSeparate.aut)
                   nil
                   (mk_init 10 IncrementalSeparate.aut IncrementalBits.Start BigBits.Parse)
                   (inl (inl IncrementalBits.Start), [], [])
                   (inl (inr BigBits.Parse), [], []).
Proof.
  set (r := (mk_init 10 IncrementalSeparate.aut IncrementalBits.Start BigBits.Parse)).
  cbv in r.
  subst r.
  time (repeat (solve_bisim)).

  repeat (unfold interp_conf_rel, interp_conf_state, interp_state_template || cbn).
  intuition eauto;
  firstorder (try congruence);
  sauto limit:5000.

  Unshelve.
  all: (exact nil).
  
Time Qed.
