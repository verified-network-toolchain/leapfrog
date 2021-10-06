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

  run_bisim top top' r_states.
  (* First cheat: manually push concat with empty buffer on the left by fiat. *)
  replace (BEConcat
                   (BEBuf (Sum.H ParseOne.header ParseZero.header)
                      (BCSnoc BCEmp 1) Left)
                   (BEVar (Sum.H ParseOne.header ParseZero.header)
                      (BVarTop BCEmp 1))) with (BEVar (Sum.H ParseOne.header ParseZero.header)
                      (BVarTop BCEmp 1)) by admit.
  replace (BEConcat
                   (BEBuf (Sum.H ParseOne.header ParseZero.header)
                      (BCSnoc BCEmp 1) Right)
                   (BEVar (Sum.H ParseOne.header ParseZero.header)
                      (BVarTop BCEmp 1))) with (BEVar (Sum.H ParseOne.header ParseZero.header)
                      (BVarTop BCEmp 1)) by admit.
  (* Second cheat: massage constraint to what I think we should get when we phrase conf_rels positively. *)
  replace ((BREq
           (BESlice
              (BEVar (Sum.H ParseOne.header ParseZero.header)
                 (BVarTop BCEmp 1)) 0 0)
           (BELit (Sum.H ParseOne.header ParseZero.header)
              (BCSnoc BCEmp 1) [true]) ⇒ bfalse)
        ⇒ (BREq
             (BESlice
                (BEVar (Sum.H ParseOne.header ParseZero.header)
                   (BVarTop BCEmp 1)) 0 0)
             (BELit (Sum.H ParseOne.header ParseZero.header)
                (BCSnoc BCEmp 1) [false]) ⇒ bfalse)) with
          (((BREq
           (BESlice
              (BEVar (Sum.H ParseOne.header ParseZero.header)
                 (BVarTop BCEmp 1)) 0 0)
           (BELit (Sum.H ParseOne.header ParseZero.header)
              (BCSnoc BCEmp 1) [true]) ⇒ bfalse)
        ⇒ BREq
             (BESlice
                (BEVar (Sum.H ParseOne.header ParseZero.header)
                   (BVarTop BCEmp 1)) 0 0)
             (BELit (Sum.H ParseOne.header ParseZero.header)
                (BCSnoc BCEmp 1) [false])) ⇒ bfalse) by admit.
  (* Now the constraint is cleared to the other side. *)
  run_bisim top top' r_states.
  (* These two steps also skip a constraint that should move to the other side,
     but the one we have is enough to make closure fail. *)
  run_bisim top top' r_states.
  run_bisim top top' r_states.
  Fail close_bisim top'.
Time Admitted.
