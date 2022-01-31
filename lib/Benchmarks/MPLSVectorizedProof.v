Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.MPLSVectorized.

Require Import Coq.Arith.PeanoNat.

Require Import Leapfrog.Utils.FunctionalFP.


Notation A := MPLSVect.aut.
Notation conf := (P4automaton.configuration (P4A.interp A)).
Notation start_left :=  Plain.ParseMPLS.
Notation start_right := Unrolled.ParseMPLS.

Definition r_states : {r : Reachability.state_pairs A & Reachability.reachable_states_wit start_left start_right r}.
  econstructor.
  unfold Reachability.reachable_states_wit.
  solve_fp_wit.
Defined.

Lemma init_states_wf:
  Reachability.valid_state_pair (Reachability.build_state_pair A start_left start_right).
Proof.
  vm_compute; Lia.lia.
Qed.

Definition top : Relations.rel conf :=
  fun q1 q2 => List.In (conf_to_state_template q1, conf_to_state_template q2) (projT1 r_states).

Definition top' : Relations.rel (state_template A) :=
  fun q1 q2 => List.In (q1, q2) (projT1 r_states).

Declare ML Module "mirrorsolve".

Lemma prebisim_mpls_unroll:
  forall q1 q2,
    interp_conf_rel' {| cr_st := {|
                        cs_st1 := {|
                          st_state := inl (inl (start_left));
                          st_buf_len := 0;
                        |};
                        cs_st2 := {|
                          st_state := inl (inr (start_right));
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
  intros.

  pose proof (Reachability.reachable_states_wit_conv init_states_wf (projT2 r_states)) as Hr.

  unfold mk_init.
  rewrite Hr.
  clear Hr.

  set (foo := (List.nodup (conf_rel_eq_dec (a:=A)) (mk_partition _ _ _ _ _ _))).
  vm_compute in foo.
  subst foo.

  (* time "build phase" repeat (time "single step" run_bisim' top top' r_states interp_compile_simplify). *)
  time "build phase" repeat (time "single step" run_bisim top top' (projT1 r_states)).
  time "close phase" close_bisim top'.
Time Admitted.

