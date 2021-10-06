Require Import Poulet4.P4automata.Benchmarks.ProofHeader.
Require Import Poulet4.P4automata.Benchmarks.SmallFilter.


Notation H := (IncrementalBits.header + BigBits.header).
Notation A := IncrementalSeparate.aut.
Notation conf := (P4automaton.configuration (P4A.interp A)).

Definition r_states :=
  Eval vm_compute in (Reachability.reachable_states
                        IncrementalSeparate.aut
                        200
                        IncrementalBits.Start
                        BigBits.Parse).

Definition top : Relations.rel conf := fun _ _ => True.
Definition top' : Relations.rel (state_template A) := fun _ _ => True.

Declare ML Module "mirrorsolve".

RegisterEnvCtors (IncrementalBits.Pref, FirstOrderConfRelSimplified.Bits 1)  (IncrementalBits.Suf, FirstOrderConfRelSimplified.Bits 1) (BigBits.Pref, FirstOrderConfRelSimplified.Bits 1) (BigBits.Suf, FirstOrderConfRelSimplified.Bits 1).

Lemma prebisim_incremental_sep:
  pre_bisimulation A
                   (wp r_states)
                   top
                   []
                   [BCEmp, ⟨ inr false, 0 ⟩ ⟨ inr true, 0 ⟩ ⊢ bfalse;
                    BCEmp, ⟨ inr true, 0 ⟩ ⟨ inr false, 0 ⟩ ⊢ bfalse]
                   {| cr_st := {|
                        cs_st1 := {|
                          st_state := inl (inl (IncrementalBits.Start));
                          st_buf_len := 0;
                        |};
                        cs_st2 := {|
                          st_state := inl (inr (BigBits.Parse));
                          st_buf_len := 0;
                        |};
                      |};
                      cr_ctx := BCEmp;
                      cr_rel := btrue;
                   |}.
Proof.
  time "build phase" repeat (time "single step" run_bisim top top' r_states).
  time "close phase" close_bisim top'.
Time Admitted.
