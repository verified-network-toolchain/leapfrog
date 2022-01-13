Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.Edge.

Require Import Coq.Arith.PeanoNat.

Require Import Leapfrog.Utils.FunctionalFP.


Declare ML Module "mirrorsolve".

Notation H := (Plain.header + Optimized.header).
Notation A := (Sum.sum Plain.aut Optimized.aut).
Notation conf := (P4automaton.configuration (P4A.interp A)).
Notation start_left := (Plain.ParseEth0).
Notation start_right := (Optimized.State_0).

Definition r_states : {r : Reachability.state_pairs A & Reachability.reachable_states_wit start_left start_right r}.
  econstructor.
  unfold Reachability.reachable_states_wit.
  match goal with 
  | |- fp_wit _ _ _ ?R => set (baz := R)
  end.
  solve_fp_wit.
  subst baz.
  eapply FPDone.
  exact eq_refl.
Defined.


SetSMTSolver "cvc4".

Definition top : Relations.rel conf := fun _ _ => True.
Definition top' : Relations.rel (state_template A) := fun _ _ => True.

Lemma prebisim_babyip:
  forall q1 q2,
    interp_conf_rel' {| cr_st := {|
                        cs_st1 := {|
                          st_state := inl (inl start_left);
                          st_buf_len := 0;
                        |};
                        cs_st2 := {|
                          st_state := inl (inr start_right);
                          st_buf_len := 0;
                        |};
                      |};
                      cr_ctx := BCEmp;
                      cr_rel := btrue;
                  |} q1 q2 ->
  pre_bisimulation A
                  (wp (projT1 r_states))
                  top
                  []
                  (mk_init _ _ _ _ A start_left start_right)
                  q1 q2.
Proof.
  idtac "running edge translation validation".

  intros.

  pose proof (Reachability.reachable_states_wit_conv (projT2 r_states)) as Hr.

  unfold mk_init.
  rewrite Hr.
  clear Hr.
  
  set (rel0 := (List.nodup _) (mk_partition _ _ _ _ _ _)).
  vm_compute in rel0.
  subst rel0.
  

  time "build phase" repeat (time "single step" run_bisim top top' (projT1 r_states)).

  print_rel_len.
  (* run_bisim top top' r_states. *)
  time "close phase" close_bisim top'.
Time Admitted.
