Require Import Poulet4.P4automata.Benchmarks.ProofHeader.
Require Import Poulet4.P4automata.Benchmarks.SimpleParsers.

Notation H := (TwoOnesChunk.header + TwoOnesBucket.header).
Notation A := (Sum.sum TwoOnesChunk.aut TwoOnesBucket.aut).
Notation conf := (P4automaton.configuration (P4A.interp A)).
Definition r_states :=
  Eval vm_compute in (Reachability.reachable_states
                        A
                        10
                        TwoOnesChunk.Start
                        TwoOnesBucket.Start).

Definition top : Relations.rel conf := fun _ _ => True.
Definition top' : Relations.rel (state_template A) := fun _ _ => True.

Declare ML Module "mirrorsolve".

RegisterEnvCtors
  (TwoOnesChunk.Bits, FirstOrderConfRelSimplified.Bits 2)
  (TwoOnesBucket.Bits, FirstOrderConfRelSimplified.Bits 2)
  (TwoOnesBucket.Val, FirstOrderConfRelSimplified.Bits 1).

Lemma prebisim_babyip:
  forall q1 q2,
    interp_conf_rel' {| cr_st := {|
                        cs_st1 := {|
                          st_state := inl (inl (TwoOnesChunk.Start));
                          st_buf_len := 0;
                        |};
                        cs_st2 := {|
                          st_state := inl (inr (TwoOnesBucket.Start));
                          st_buf_len := 0;
                        |};
                      |};
                      cr_ctx := BCEmp;
                      cr_rel := btrue;
                   |} q1 q2 ->
  pre_bisimulation A
                   (wp r_states)
                   top
                   []
                   (mk_init _ _ _ A 10 TwoOnesChunk.Start TwoOnesBucket.Start)
                   q1 q2.
Proof.
  idtac "running small bucket bisimulation".

  intros.
  set (rel0 := (mk_init _ _ _ A 10 TwoOnesChunk.Start TwoOnesBucket.Start)).
  vm_compute in rel0.
  subst rel0.

  time "build phase" repeat (time "single step" run_bisim top top' r_states).
  time "close phase" close_bisim top'.
Time Admitted.
