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

  RegisterPrim (@TVar (sig A) (CEmp _) (Bits 0)) "p4a.core.var".
  RegisterPrim (@TFun (sig A) (CEmp _) [] (Bits 0)) "p4a.core.fun".

  RegisterPrim (@VHere (sig A) (CEmp _) (Bits 0)) "p4a.core.vhere".
  RegisterPrim (@VThere (sig A) (CEmp _) (Bits 0) (Bits 0)) "p4a.core.vthere".


  RegisterPrim (@FEq (sig A) (CEmp _) (Bits 0)) "p4a.core.eq".
  RegisterPrim (@FTrue (sig A) (CEmp _)) "p4a.core.tt".
  RegisterPrim (@FFalse (sig A) (CEmp _)) "p4a.core.ff".
  RegisterPrim (@FRel (sig A) (CEmp _)) "p4a.core.rel".
  RegisterPrim (@FNeg (sig A) (CEmp _)) "p4a.core.neg".
  RegisterPrim (@FOr (sig A) (CEmp _)) "p4a.core.or".
  RegisterPrim (@FAnd (sig A) (CEmp _)) "p4a.core.and".
  RegisterPrim (@FForall (sig A) (CEmp _)) "p4a.core.forall".

  RegisterPrim (@FImpl (sig A) (CEmp _)) "p4a.core.impl".

  RegisterPrim (@CEmp (sig A)) "p4a.core.cnil".
  RegisterPrim (@CSnoc (sig A)) "p4a.core.csnoc".

  RegisterPrim (@inl nat bool) "coq.core.inl".
  RegisterPrim (@inr nat bool) "coq.core.inr".

  RegisterPrim FirstOrderConfRelSimplified.Bits "p4a.sorts.bits".
  RegisterPrim FirstOrderConfRelSimplified.Store "p4a.sorts.store".

  RegisterPrim FirstOrderConfRelSimplified.BitsLit "p4a.funs.bitslit".
  RegisterPrim FirstOrderConfRelSimplified.Concat "p4a.funs.concat".
  RegisterPrim FirstOrderConfRelSimplified.Slice "p4a.funs.slice".
  RegisterPrim FirstOrderConfRelSimplified.Lookup "p4a.funs.lookup".

  RegisterPrim (@HList.HNil nat (fun _ => bool)) "p4a.core.hnil".
  RegisterPrim (@HList.HCons nat (fun _ => bool)) "p4a.core.hcons".

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