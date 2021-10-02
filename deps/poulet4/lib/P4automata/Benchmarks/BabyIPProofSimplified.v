Require Import Poulet4.P4automata.Benchmarks.ProofHeader.
Require Import Poulet4.P4automata.Benchmarks.BabyIP.
Require Import Poulet4.P4automata.CompileConfRel.
Require Import Poulet4.P4automata.FirstOrder.
Require Import Poulet4.P4automata.FirstOrderConfRel.
Require Import Coq.Program.Equality.
Require Import Poulet4.P4automata.CompileConfRelSimplified.
Require Import Poulet4.P4automata.CompileFirstOrderConfRelSimplified.

Require Import Poulet4.P4automata.Sum.

From Hammer Require Import Tactics.

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


Ltac extend_bisim :=
  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: ~interp_entailment A i ({| e_prem := R; e_concl := C |}));
    [ idtac |
    pose (t := WP.wp r_states C);
    eapply PreBisimulationExtend with (H0 := right H) (W := t);
    [ tauto | trivial |];
    vm_compute in t;
    simpl (_ ++ _);
    clear t]
  end.

Ltac skip_bisim :=
  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: interp_entailment A i ({| e_prem := R; e_concl := C |}));
    eapply PreBisimulationSkip with (H0:=left H);
    [ exact I | ];
    clear H
  end.

Ltac extend_bisim' HN :=
  match goal with
  | |- pre_bisimulation ?a _ _ _ (?C :: _) _ _ =>
    pose (t := WP.wp r_states C);
    eapply PreBisimulationExtend with (H0 := right HN) (W := t);
    [ tauto | trivial |];
    vm_compute in t;
    simpl (_ ++ _);
    clear t;
    clear HN
  end.

Ltac skip_bisim' H :=
  eapply PreBisimulationSkip with (H0:=left H);
  [ exact I | ];
  clear H.

Ltac size_script :=
  unfold Syntax.interp;
  autorewrite with size';
  vm_compute;
  repeat constructor.

Lemma forall_exists_demorgan: forall X P,
  (exists (x: X), ~P x) -> ~forall (x: X), P x.
Proof.
  intros.
  intro.
  destruct H.
  specialize (H0 x).
  contradiction.
Qed.

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

RegisterPrim (@inl BabyIP1.state bool) "coq.core.inl".
RegisterPrim (@inr BabyIP1.state bool) "coq.core.inr".


RegisterPrim FirstOrderConfRelSimplified.Bits "p4a.sorts.bits".
RegisterPrim FirstOrderConfRelSimplified.Store "p4a.sorts.store".

RegisterPrim FirstOrderConfRelSimplified.BitsLit "p4a.funs.bitslit".
RegisterPrim FirstOrderConfRelSimplified.Concat "p4a.funs.concat".
RegisterPrim FirstOrderConfRelSimplified.Slice "p4a.funs.slice".
RegisterPrim FirstOrderConfRelSimplified.Lookup "p4a.funs.lookup".

RegisterPrim (@HList.HNil nat (fun _ => bool)) "p4a.core.hnil".
RegisterPrim (@HList.HCons nat (fun _ => bool)) "p4a.core.hcons".

RegisterEnvCtors (BabyIP1.HdrIP, FirstOrderConfRelSimplified.Bits 20)  (BabyIP1.HdrUDP, FirstOrderConfRelSimplified.Bits 20) (BabyIP1.HdrTCP, FirstOrderConfRelSimplified.Bits 28) (BabyIP2.HdrCombi, FirstOrderConfRelSimplified.Bits 40) (BabyIP2.HdrSeq, FirstOrderConfRelSimplified.Bits 8).

Ltac crunch_foterm :=
  match goal with
  | |- interp_fm _ ?g =>
    let temp := fresh "temp" in set (temp := g);
    vm_compute in temp;
    subst temp
  end.

Ltac crunch_foterm' :=
  repeat (
    simpl ||
    simpl_eqs ||
    unfold compile_fm, compile_config, compile_conf_rel, quantify_all, quantify, compile_simplified_entailment, compile_simplified_entailment, compile_simplified_conf_rel, outer_ctx, se_st, se_prems ||
    unfold e_concl, e_prem, simplify_crel, simplify_conf_rel, cr_ctx, compile_bctx, cr_st, cs_st1, cs_st2, st_state, st_buf_len, reindex_tm, compile_store_ctx, FinType.enum, compile_store_ctx_partial ||
    unfold be_sort, be_size, var_store1, var_store2, app_ctx ||
    autorewrite with compile_store_rel ||
    autorewrite with quantify' ||
    autorewrite with compile_bit_expr ||
    autorewrite with weaken_var
  ).

Ltac verify_interp :=
  match goal with
  | |- pre_bisimulation ?a ?wp _ ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: interp_entailment A top ({| e_prem := R; e_concl := C |}));
    [
      eapply simplify_entailment_correct with (i := fun _ _ => True);
      eapply compile_simplified_entailment_correct;
      [ typeclasses eauto | typeclasses eauto | ];

      time "reduce goal" crunch_foterm;

      match goal with
      | |- ?X => time "smt check neg" check_interp_neg X
      | |- ?X => time "smt check pos" check_interp_pos X; admit
      end
    |]
  end;
  let n:= numgoals in
  tryif ( guard n = 2) then
    match goal with
    | |- interp_fm _ _ => admit
    | H : interp_entailment _ _ _ |- pre_bisimulation _ _ _ ?R (?C :: _) _ _ =>
      clear H;
      let HN := fresh "HN" in
      assert (HN: ~ (interp_entailment A top ({| e_prem := R; e_concl := C |}))) by admit
    end
  else idtac.

Ltac run_bisim :=
  verify_interp;
  match goal with
  | HN: ~ (interp_entailment _ _ _ ) |- _ =>
    idtac "extending"; extend_bisim' HN; clear HN
  | H: interp_entailment _ _ _  |- _ =>
    idtac "skipping"; skip_bisim' H; clear H
  end.

Lemma prebisim_babyip:
  pre_bisimulation
    A
    (WP.wp r_states)
    top
    []
    (mk_init _ _ _ A 10 BabyIP1.Start BabyIP2.Start)
    (P4automaton.MkConfiguration
      (Syntax.interp A)
      (inl (inl BabyIP1.Start))
      0
      tt
      ltac:(eapply cap')
      nil)
    (P4automaton.MkConfiguration
      (Syntax.interp BabyIP.aut)
      (inl (inr BabyIP2.Start))
      0
      tt
      ltac:(eapply cap')
      nil).
Proof.
  idtac "running babyip bisimulation".
  set (rel0 := (mk_init _ _ _ BabyIP.aut 10 BabyIP1.Start BabyIP2.Start)).
  cbv in rel0.
  subst rel0.
  time "overall loop" (repeat time "bisim step" run_bisim).

  apply PreBisimulationClose.


  unfold interp_crel.

  unfold List.map.
Admitted.
