Require Import Poulet4.P4automata.Benchmarks.ProofHeader.
Require Import Poulet4.P4automata.Benchmarks.SimpleParsers.

Notation A := OneZero.aut.
Notation conf := (P4automaton.configuration (P4A.interp A)).

Definition r_states :=
  Eval vm_compute in (Reachability.reachable_states
                        OneZero.aut
                        200
                        ParseOne.Start
                        ParseZero.Start).

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

RegisterEnvCtors 
  (ParseOne.Bit, FirstOrderConfRelSimplified.Bits 1)  
  (ParseZero.Bit, FirstOrderConfRelSimplified.Bits 1).

(* These parsers are different, this proof should fail *)
Lemma prebisim_negative:
  pre_bisimulation A
                   (wp r_states)
                   top
                   []
                   [BCEmp, ⟨ inr false, 0 ⟩ ⟨ inr true, 0 ⟩ ⊢ bfalse;
                    BCEmp, ⟨ inr true, 0 ⟩ ⟨ inr false, 0 ⟩ ⊢ bfalse]
                   {| cr_st := {|
                        cs_st1 := {|
                          st_state := inl (inl (ParseOne.Start));
                          st_buf_len := 0;
                        |};
                        cs_st2 := {|
                          st_state := inl (inr (ParseZero.Start));
                          st_buf_len := 0;
                        |};
                      |};
                      cr_ctx := BCEmp;
                      cr_rel := btrue;
                   |}.
Proof.

  time "build phase" repeat (time "single step" run_bisim top top' r_states).

  apply PreBisimulationClose.
  
  cbn.
  unfold interp_entailment'.
  simpl.
  unfold top, interp_crel, interp_conf_rel'.
  simpl.
  unfold interp_conf_state.
  simpl.
  unfold interp_state_template.
  simpl.
  intros.
  repeat match goal with 
  | H: _ /\ _ |- _ => destruct H
  end.
  specialize (H1 tt).
  autorewrite with interp_store_rel in H1.
  cbn.
  unfold interp_conf_rel.
  simpl.
  unfold interp_conf_state.
  simpl.
  unfold interp_state_template.
  simpl.
  split; [|split]. 

  all: 
    intros;
    repeat match goal with 
    | H: _ /\ _ |- _ => destruct H
    end.
  (* yikes, both of the goals here are contradictory... *)
  - exfalso; congruence.
  - exfalso; congruence.
  - trivial.

Time Admitted.
