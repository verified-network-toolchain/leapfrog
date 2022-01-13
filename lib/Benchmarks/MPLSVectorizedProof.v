Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.MPLSVectorized.

Require Import Coq.Arith.PeanoNat.


Notation A := MPLSVect.aut.
Notation conf := (P4automaton.configuration (P4A.interp A)).
Notation start_left :=  Plain.ParseMPLS.
Notation start_right := Unrolled.ParseMPLS.

(* Eval vm_compute in (length (Reachability.valid_state_templates A)). *)

Definition r_states : Reachability.state_pairs A.
  evar (r: Reachability.state_pairs A).
  assert (Reachability.reachable_states_wit _ start_left start_right r).



Definition r_states := (Reachability.reachable_states
                        A
                        start_left
                        start_right).

                

Definition top : Relations.rel conf := fun _ _ => True.
Definition top' : Relations.rel (state_template A) := fun _ _ => True.

Declare ML Module "mirrorsolve".

Lemma interp_compile_simplify: 
  forall prem concl, 
    interp_fm
    (compile_valu (a := A) (VEmp _ _))
    (compile_fm
      (FirstOrderConfRelSimplified.simplify_eq_zero_fm
          (FirstOrderConfRelSimplified.simplify_concat_zero_fm
            (compile_simplified_entailment
                (simplify_entailment
                  {|
                    e_prem := prem;
                    e_concl :=
                      concl
                  |}))))) 
      -> interp_entailment A top ({| e_prem := prem; e_concl := concl |}).
Proof.
  intros.
  eapply simplify_entailment_correct with (i := top');
  eapply compile_simplified_entailment_correct; simpl; intros;
  eapply FirstOrderConfRelSimplified.simplify_concat_zero_fm_corr;
  eapply FirstOrderConfRelSimplified.simplify_eq_zero_fm_corr;
  eapply CompileFirstOrderConfRelSimplified.compile_simplified_fm_bv_correct.
  auto.
Qed.

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
                    (wp r_states)
                    top
                    []
                    (mk_init _ _ _ A r_depth start_left start_right)
                    q1 q2.
Proof.
  intros.

  set (rel0 := (mk_init _ _ _ _ _ _ _)).
  vm_compute in rel0.
  subst rel0.

  (* time "build phase" repeat (time "single step" run_bisim' top top' r_states interp_compile_simplify). *)
  time "build phase" repeat (time "single step" run_bisim top top' r_states).
  time "close phase" close_bisim top'.
Time Admitted.

