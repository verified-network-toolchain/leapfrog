Require Import Poulet4.P4automata.Examples.ProofHeader.
Require Import Poulet4.P4automata.Examples.SmallFilter.
From Hammer Require Import Tactics.


Notation H := (IncrementalBits.header + BigBits.header).
Notation A := IncrementalSeparate.aut.
Notation conf := (P4automaton.configuration (P4A.interp A)).
Definition r_states :=
  Eval cbv in (Reachability.reachable_states IncrementalSeparate.aut 10 IncrementalBits.Start BigBits.Parse).

Lemma prebisim_incremental_sep:
  pre_bisimulation IncrementalSeparate.aut
                   (WPSymLeap.wp r_states (H:=IncrementalSeparate.header))
                   (Reachability.reachable_pair r_states)
                   nil
                   (mk_init _ _ _ IncrementalSeparate.aut 10 IncrementalBits.Start BigBits.Parse)
                   (inl (inl IncrementalBits.Start), [], [])
                   (inl (inr BigBits.Parse), [], []).
Proof.
  set (r := (mk_init _ _ _ IncrementalSeparate.aut 10 IncrementalBits.Start BigBits.Parse)).
  cbv in r.
  subst r.
  solve_bisim.
  solve_bisim.
  solve_bisim.
  solve_bisim.
  solve_bisim.
  solve_bisim.
  solve_bisim.
  cbv.
  sauto.
  Unshelve.
  exact nil.
  exact nil.
  exact nil.
Qed.
