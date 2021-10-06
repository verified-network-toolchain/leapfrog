Require Import Poulet4.P4automata.Benchmarks.ProofHeader.
Require Import Poulet4.P4automata.Benchmarks.BabyIP.

Notation H := (BabyIP1.header + BabyIP2.header).
Notation A := BabyIP.aut.
Notation conf := (P4automaton.configuration (P4A.interp A)).
Definition r_states :=
  Eval vm_compute in (Reachability.reachable_states
                        BabyIP.aut
                        200
                        BabyIP1.Start
                        BabyIP2.Start).

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
  (BabyIP1.HdrIP, FirstOrderConfRelSimplified.Bits 20)
  (BabyIP1.HdrUDP, FirstOrderConfRelSimplified.Bits 20)
  (BabyIP1.HdrTCP, FirstOrderConfRelSimplified.Bits 28)
  (BabyIP2.HdrCombi, FirstOrderConfRelSimplified.Bits 40)
  (BabyIP2.HdrSeq, FirstOrderConfRelSimplified.Bits 8).

Lemma prebisim_babyip:
  pre_bisimulation
    A
    (WP.wp r_states)
    top
    []
    (mk_init _ _ _ A 10 BabyIP1.Start BabyIP2.Start)
    {| cr_st := {|
        cs_st1 := {|
          st_state := inl (inl (BabyIP1.Start));
          st_buf_len := 0;
        |};
        cs_st2 := {|
          st_state := inl (inr (BabyIP2.Start));
          st_buf_len := 0;
        |};
      |};
      cr_ctx := BCEmp;
      cr_rel := btrue;
   |}.
Proof.
  idtac "running babyip bisimulation".
  set (rel0 := (mk_init _ _ _ BabyIP.aut 10 BabyIP1.Start BabyIP2.Start)).
  cbv in rel0.
  subst rel0.

  time "build phase" repeat (time "single step" run_bisim top top' r_states).
  time "close phase" close_bisim top'.
Time Admitted.
