Require Import Poulet4.P4automata.Benchmarks.ProofHeader.
Require Import Poulet4.P4automata.Benchmarks.MPLSVectorized.



Module PlainUnroll.

  Notation A := MPLSVect.aut.
  Notation conf := (P4automaton.configuration (P4A.interp A)).

  Definition r_states :=
    Eval vm_compute in (Reachability.reachable_states
                          A
                          200
                          MPLSPlain.ParseMPLS
                          MPLSUnroll.ParseMPLS0).

  Definition top : Relations.rel conf := fun _ _ => True.
  Definition top' : Relations.rel (state_template A) := fun _ _ => True.

  Declare ML Module "mirrorsolve".

  ClearEnvCtors.

  RegisterEnvCtors 
    (MPLSPlain.HdrMPLS0, FirstOrderConfRelSimplified.Bits 32) 
    (MPLSPlain.HdrMPLS1, FirstOrderConfRelSimplified.Bits 32)  
    (MPLSPlain.HdrUDP, FirstOrderConfRelSimplified.Bits 32)   
    (MPLSUnroll.HdrMPLS0, FirstOrderConfRelSimplified.Bits 32) 
    (MPLSUnroll.HdrMPLS1, FirstOrderConfRelSimplified.Bits 32)  
    (MPLSUnroll.HdrUDP, FirstOrderConfRelSimplified.Bits 32).

  Lemma prebisim_mpls_unroll:
    pre_bisimulation A
                    (wp r_states)
                    top
                    []
                    [BCEmp, ⟨ inr false, 0 ⟩ ⟨ inr true, 0 ⟩ ⊢ bfalse;
                      BCEmp, ⟨ inr true, 0 ⟩ ⟨ inr false, 0 ⟩ ⊢ bfalse]
                    {| cr_st := {|
                          cs_st1 := {|
                            st_state := inl (inl (MPLSPlain.ParseMPLS));
                            st_buf_len := 0;
                          |};
                          cs_st2 := {|
                            st_state := inl (inr (MPLSUnroll.ParseMPLS0));
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
End PlainUnroll.

Module VectUnroll.

  Notation A := MPLSVectUnroll.aut.
  Notation conf := (P4automaton.configuration (P4A.interp A)).

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
    (MPLSPlain.HdrMPLS0, FirstOrderConfRelSimplified.Bits 32) 
    (MPLSPlain.HdrMPLS1, FirstOrderConfRelSimplified.Bits 32)  
    (MPLSPlain.HdrUDP, FirstOrderConfRelSimplified.Bits 32)   
    (MPLSInline.HdrMPLS0, FirstOrderConfRelSimplified.Bits 32) 
    (MPLSInline.HdrMPLS1, FirstOrderConfRelSimplified.Bits 32)  
    (MPLSInline.HdrUDP, FirstOrderConfRelSimplified.Bits 32).

  Lemma prebisim_mpls_inline:
    pre_bisimulation A
                    (wp r_states)
                    top
                    []
                    [BCEmp, ⟨ inr false, 0 ⟩ ⟨ inr true, 0 ⟩ ⊢ bfalse;
                      BCEmp, ⟨ inr true, 0 ⟩ ⟨ inr false, 0 ⟩ ⊢ bfalse]
                    {| cr_st := {|
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
                    |}.
  Proof.
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
    pre_bisimulation A
                    (wp r_states)
                    top
                    []
                    [BCEmp, ⟨ inr false, 0 ⟩ ⟨ inr true, 0 ⟩ ⊢ bfalse;
                      BCEmp, ⟨ inr true, 0 ⟩ ⟨ inr false, 0 ⟩ ⊢ bfalse]
                    {| cr_st := {|
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
                    |}.
  Proof.
    time "build phase" repeat (time "single step" run_bisim top top' r_states).
    time "close phase" close_bisim top'.
  Time Admitted. 

  Definition r_states' :=
    Eval vm_compute in (Reachability.reachable_states
                          A
                          200
                          MPLSUnroll.ParseMPLS1
                          MPLSInline.ParseMPLS).
  Goal pre_bisimulation A
      (wp r_states')
      top
      []
      [BCEmp, ⟨ inr false, 0 ⟩ ⟨ inr true, 0 ⟩ ⊢ bfalse;
        BCEmp, ⟨ inr true, 0 ⟩ ⟨ inr false, 0 ⟩ ⊢ bfalse]
      {| cr_st := {|
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
      |}.
  Proof.
    set (a := A) in *.
    time "build phase" repeat (time "single step" run_bisim top top' r_states').
    close_bisim top'.
  Time Admitted.
End UnrollInline.