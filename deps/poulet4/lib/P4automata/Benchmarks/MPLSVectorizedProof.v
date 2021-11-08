Require Import Poulet4.P4automata.Benchmarks.ProofHeader.
Require Import Poulet4.P4automata.Benchmarks.MPLSVectorized.

Require Import Coq.Arith.PeanoNat.



Module PlainInline.

  Notation A := MPLSPlainInline.aut.
  Notation conf := (P4automaton.configuration (P4A.interp A)).
  Notation start_left :=  MPLSPlain.ParseMPLS.
  Notation start_right := MPLSInline.ParseMPLS.


Fixpoint reachable_states_len' (r: Reachability.state_pairs A) (fuel: nat) :=
  match fuel with 
  | 0 => None 
  | S x => 
    let nxt := Reachability.reachable_step r in 
    let nxt_len := length nxt in 
    if Nat.eq_dec (length nxt) (length r) then Some nxt_len
    else 
      reachable_states_len' nxt x
  end.

  Definition r_depth : nat.
  refine (
  let s := ({| st_state := inl (inl start_left); st_buf_len := 0 |},
            {| st_state := inl (inr start_right); st_buf_len := 0 |}) in
  let r := reachable_states_len' [s] 1000 in 
  _).
  vm_compute in r.
  match goal with 
  | _ := Some ?x |- _ => exact x
  end.
  Defined.



  Definition r_states :=
    Eval vm_compute in (Reachability.reachable_states
                          A
                          r_depth
                          MPLSPlain.ParseMPLS
                          MPLSInline.ParseMPLS).

  Definition top : Relations.rel conf := fun _ _ => True.
  Definition top' : Relations.rel (state_template A) := fun _ _ => True.

  Declare ML Module "mirrorsolve".

  ClearEnvCtors.

  RegisterEnvCtors
    (MPLSPlain.HdrMPLS, FirstOrderConfRelSimplified.Bits 32)
    (MPLSPlain.HdrUDP, FirstOrderConfRelSimplified.Bits 32)
    (MPLSInline.HdrMPLS0, FirstOrderConfRelSimplified.Bits 32)
    (MPLSInline.HdrMPLS1, FirstOrderConfRelSimplified.Bits 32)
    (MPLSInline.HdrUDP, FirstOrderConfRelSimplified.Bits 32).

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
    
    time "build phase" repeat (time "single step" run_bisim top top' r_states).
    time "close phase" close_bisim top'.
  Time Admitted.
End PlainInline.


Module PlainUnroll.

  Notation A := MPLSVect.aut.
  Notation conf := (P4automaton.configuration (P4A.interp A)).
  Notation start_left :=  MPLSPlain.ParseMPLS.
  Notation start_right := MPLSUnroll.ParseMPLS0.

  Definition r_depth := 3.

  Definition r_states :=
    Eval vm_compute in (Reachability.reachable_states
                          A
                          r_depth
                          MPLSPlain.ParseMPLS
                          MPLSUnroll.ParseMPLS0).

  Definition top : Relations.rel conf := fun _ _ => True.
  Definition top' : Relations.rel (state_template A) := fun _ _ => True.

  Declare ML Module "mirrorsolve".

  ClearEnvCtors.

  RegisterEnvCtors
    (MPLSPlain.HdrMPLS, FirstOrderConfRelSimplified.Bits 32)
    (MPLSPlain.HdrUDP, FirstOrderConfRelSimplified.Bits 32)
    (MPLSUnroll.HdrMPLS0, FirstOrderConfRelSimplified.Bits 32)
    (MPLSUnroll.HdrMPLS1, FirstOrderConfRelSimplified.Bits 32)
    (MPLSUnroll.HdrUDP, FirstOrderConfRelSimplified.Bits 32).

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

    time "build phase" repeat (time "single step" run_bisim top top' r_states).
    time "close phase" close_bisim top'.
  Time Admitted.
End PlainUnroll.

Module VectUnroll.

  Notation A := MPLSVectUnroll.aut.
  Notation conf := (P4automaton.configuration (P4A.interp A)).
  Notation start_left := MPLSPlain.ParseMPLS.
  Notation start_right := MPLSInline.ParseMPLS.

  

  Definition r_states :=
    Eval vm_compute in (Reachability.reachable_states
                          A
                          200
                          MPLSPlain.ParseMPLS
                          MPLSInline.ParseMPLS).

  

  Definition top : Relations.rel conf := fun _ _ => True.
  Definition top' : Relations.rel (state_template A) := fun _ _ => True.

  ClearEnvCtors.

  RegisterEnvCtors
    (MPLSPlain.HdrMPLS, FirstOrderConfRelSimplified.Bits 32)
    (MPLSPlain.HdrUDP, FirstOrderConfRelSimplified.Bits 32)
    (MPLSInline.HdrMPLS0, FirstOrderConfRelSimplified.Bits 32)
    (MPLSInline.HdrMPLS1, FirstOrderConfRelSimplified.Bits 32)
    (MPLSInline.HdrUDP, FirstOrderConfRelSimplified.Bits 32).

  Lemma prebisim_mpls_inline:
    forall q1 q2,
      interp_conf_rel' {| cr_st := {|
                          cs_st1 := {|
                            st_state := inl (inl (MPLSPlain.ParseMPLS));
                            st_buf_len := 0;
                          |};
                          cs_st2 := {|
                            st_state := inl (inr (MPLSInline.ParseMPLS));
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
                     (mk_init _ _ _ A 200 MPLSPlain.ParseMPLS MPLSInline.ParseMPLS)
                     q1 q2.
  Proof.
    intros.

    set (rel0 := (mk_init _ _ _ _ _ _ _)).
    vm_compute in rel0.
    subst rel0.

    time "build phase" repeat (time "single step" run_bisim top top' r_states).
    time "close phase" close_bisim top'.
  Time Admitted.
End VectUnroll.

Module UnrollInline.

  Notation A := MPLSUnrollInline.aut.
  Notation conf := (P4automaton.configuration (P4A.interp A)).

  Definition r_states :=
    Eval vm_compute in (Reachability.reachable_states
                          A
                          200
                          MPLSUnroll.ParseMPLS0
                          MPLSInline.ParseMPLS).

  Definition top : Relations.rel conf := fun _ _ => True.
  Definition top' : Relations.rel (state_template A) := fun _ _ => True.

  ClearEnvCtors.

  RegisterEnvCtors
    (MPLSUnroll.HdrMPLS0, FirstOrderConfRelSimplified.Bits 32)
    (MPLSUnroll.HdrMPLS1, FirstOrderConfRelSimplified.Bits 32)
    (MPLSUnroll.HdrUDP, FirstOrderConfRelSimplified.Bits 32)
    (MPLSInline.HdrMPLS0, FirstOrderConfRelSimplified.Bits 32)
    (MPLSInline.HdrMPLS1, FirstOrderConfRelSimplified.Bits 32)
    (MPLSInline.HdrUDP, FirstOrderConfRelSimplified.Bits 32).

  Lemma prebisim_mpls_inline:
    forall q1 q2,
      interp_conf_rel' {| cr_st := {|
                          cs_st1 := {|
                            st_state := inl (inl (MPLSUnroll.ParseMPLS0));
                            st_buf_len := 0;
                          |};
                          cs_st2 := {|
                            st_state := inl (inr (MPLSInline.ParseMPLS));
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
                     (mk_init _ _ _ A 200 MPLSUnroll.ParseMPLS0 MPLSInline.ParseMPLS)
                     q1 q2.
  Proof.
    intros.

    set (rel0 := (mk_init _ _ _ _ _ _ _)).
    vm_compute in rel0.
    subst rel0.

    time "build phase" repeat (time "single step" run_bisim top top' r_states).
    time "close phase" close_bisim top'.
  Time Admitted.

  Definition r_states' :=
    Eval vm_compute in (Reachability.reachable_states
                          A
                          200
                          MPLSUnroll.ParseMPLS1
                          MPLSInline.ParseMPLS).
  Goal
    forall q1 q2,
      interp_conf_rel' {| cr_st := {|
                          cs_st1 := {|
                            st_state := inl (inl (MPLSUnroll.ParseMPLS1));
                            st_buf_len := 0;
                          |};
                          cs_st2 := {|
                            st_state := inl (inr (MPLSInline.ParseMPLS));
                            st_buf_len := 0;
                          |};
                        |};
                        cr_ctx := BCEmp;
                        cr_rel := btrue;
                     |} q1 q2 ->
    pre_bisimulation A
                     (wp r_states)
                     top
                     (mk_init _ _ _ A 200 MPLSUnroll.ParseMPLS1 MPLSInline.ParseMPLS)
                     [BCEmp, ⟨ inr false, 0 ⟩ ⟨ inr true, 0 ⟩ ⊢ bfalse;
                      BCEmp, ⟨ inr true, 0 ⟩ ⟨ inr false, 0 ⟩ ⊢ bfalse]
                     q1 q2.
  Proof.
    set (a := A) in *.
    intros.

    set (rel0 := (mk_init _ _ _ _ _ _ _)).
    vm_compute in rel0.
    subst rel0.

    time "build phase" repeat (time "single step" run_bisim top top' r_states').
    time "close phase" close_bisim top'.
  Time Admitted.
End UnrollInline.
