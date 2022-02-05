Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.Memory.

Require Import Coq.Arith.PeanoNat.

Require Import Leapfrog.Utils.FunctionalFP.

Notation A := Wide16Self.aut.
Notation conf := (P4automaton.configuration (P4A.interp A)).
Notation start_left :=  MemoryWide16.start.
Notation start_right := MemoryWide16.start.

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

Fixpoint in_checker {A} (A_eq: forall (x y: A), ({x = y} + {x <> y})%type) (x: A) (xs : list A) : bool :=
  match xs with
  | nil => false
  | x' :: xs' => 
    if A_eq x' x then true else in_checker A_eq x xs'
  end.

Lemma in_checker_conv : 
  forall A A_eq x xs, 
    (@in_checker A A_eq x xs = true) -> List.In x xs.
Proof.
  intros.
  induction xs; [inversion H|].
  
  simpl in_checker in H.
  destruct (A_eq _ _).
  - econstructor; assumption.
  - eapply or_intror.
    eapply IHxs.
    assumption.
Qed.

Definition state_temp_prod_eqdec : forall (x y: state_template A * state_template A), {x = y} + {x <> y} :=
  fun x y => EquivDec.prod_eqdec _ _ x y.

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
  (* time "close phase" close_bisim' top'. *)
  time "close phase" close_bisim top'.
  (* eapply PreBisimulationClose;
  match goal with
  | H: interp_conf_rel' ?C ?q1 ?q2|- interp_crel _ ?top ?P ?q1 ?q2 =>
    let H0 := fresh "H0" in
    assert (H0: interp_entailment' top {| e_prem := P; e_concl := C |}) by (
      eapply simplify_entailment_correct' with (i := top');
      eapply compile_simplified_entailment_correct';

      simpl; intros;
      eapply FirstOrderConfRelSimplified.simplify_eq_zero_fm_corr;
      eapply CompileFirstOrderConfRelSimplified.compile_simplified_fm_bv_correct;

      crunch_foterm;
      match goal with
      | |- ?X => time "smt check pos" check_interp_pos X; admit
      end
    );
    eapply H0
  end.

  1: {
    (* admit. *)
    apply in_checker_conv with (A_eq := state_temp_prod_eqdec).
    vm_compute in H.
    
    destruct q1, q2.
    unfold conf_to_state_template, P4automaton.conf_buf_len, P4automaton.conf_state.
  
    repeat match goal with 
    | H: _ /\ _ |- _ => destruct H
    end.
    repeat match goal with 
    | H: _ = _ |- _ => erewrite <- H
    end.
    exact eq_refl.
  }
  

  destruct q1, q2;
  vm_compute in H;
  repeat match goal with 
  | H: _ /\ _ |- _ => destruct H
  end.

  (* split; [admit | admit]. *)


  split; [ vm_compute; (repeat split || assumption) | (intros; exact I)]. *)
  

Time Admitted.

