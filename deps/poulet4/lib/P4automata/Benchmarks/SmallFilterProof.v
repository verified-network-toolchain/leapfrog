Require Import Poulet4.P4automata.Benchmarks.ProofHeader.
Require Import Poulet4.P4automata.Benchmarks.SmallFilter.

Require Import Poulet4.P4automata.CompileConfRel.
Require Import Poulet4.P4automata.FirstOrder.
Require Import Poulet4.P4automata.FirstOrderConfRel.
Require Import Poulet4.P4automata.CompileConfRelSimplified.
Require Import Poulet4.P4automata.CompileFirstOrderConfRelSimplified.

Require Import Poulet4.P4automata.WP.
Require Import Coq.Program.Equality.


Notation H := (IncrementalBits.header + BigBits.header).
Notation A := IncrementalSeparate.aut.
Notation conf := (P4automaton.configuration (P4A.interp A)).

Definition r_states :=
  Eval vm_compute in (Reachability.reachable_states
                        IncrementalSeparate.aut
                        200
                        IncrementalBits.Start
                        BigBits.Parse).

Definition top : Relations.rel conf := fun _ _ => True.
Definition top' : Relations.rel (state_template A) := fun _ _ => True.


Ltac extend_bisim :=
  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ =>
    let H := fresh "H" in
    assert (H: ~interp_entailment A i ({| e_prem := R; e_concl := C |}));
    [ idtac |
    pose (t := WP.wp r_states C);
    apply PreBisimulationExtend with (H0 := right H) (W := t);
    [ trivial | tauto |];
    vm_compute in t;
    simpl (_ ++ _);
    clear t]
  end.

Ltac skip_bisim :=
  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ =>
    let H := fresh "H" in
    assert (H: interp_entailment A i ({| e_prem := R; e_concl := C |}));
    apply PreBisimulationSkip with (H0:=left H);
    [ exact I | ];
    clear H
  end.

Ltac extend_bisim' HN :=
  match goal with
  | |- pre_bisimulation ?a _ _ _ (?C :: _) _ =>
    pose (t := WP.wp r_states C);
    apply PreBisimulationExtend with (H0 := right HN) (W := t);
    [ tauto | trivial |];
    vm_compute in t;
    simpl (_ ++ _);
    clear t;
    clear HN
  end.

Ltac skip_bisim' H :=
  apply PreBisimulationSkip with (H0:=left H);
  [ exact I | ];
  clear H.

Ltac size_script :=
  unfold Syntax.interp;
  autorewrite with size';
  vm_compute;
  repeat constructor.


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

RegisterEnvCtors (IncrementalBits.Pref, FirstOrderConfRelSimplified.Bits 1)  (IncrementalBits.Suf, FirstOrderConfRelSimplified.Bits 1) (BigBits.Pref, FirstOrderConfRelSimplified.Bits 1) (BigBits.Suf, FirstOrderConfRelSimplified.Bits 1).

Ltac crunch_foterm :=
  match goal with
  | |- interp_fm _ ?g =>
    let temp := fresh "temp" in set (temp := g);
    vm_compute in temp;
    subst temp
  end.

Ltac verify_interp :=
  match goal with
  | |- pre_bisimulation ?a ?wp _ ?R (?C :: _) _ =>
    let H := fresh "H" in
    assert (H: interp_entailment A top ({| e_prem := R; e_concl := C |}));
    [
      eapply simplify_entailment_correct with (i := top');
      eapply compile_simplified_entailment_correct;
      [ typeclasses eauto | typeclasses eauto | typeclasses eauto |];

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
    | H : interp_entailment _ _ _ |- pre_bisimulation _ _ _ ?R (?C :: _) _ =>
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


Require Import Poulet4.Relations.

Lemma prebisim_incremental_sep:
  pre_bisimulation A
                   (wp r_states)
                   top
                   []
                   (mk_init _ _ _ A 10 IncrementalBits.Start BigBits.Parse)
                   {| cr_st := {|
                        cs_st1 := {|
                          st_state := inl (inl (IncrementalBits.Start));
                          st_buf_len := 0;
                        |};
                        cs_st2 := {|
                          st_state := inl (inr (BigBits.Parse));
                          st_buf_len := 0;
                        |};
                      |};
                      cr_ctx := BCEmp;
                      cr_rel := btrue;
                   |}.
Proof.
  set (rel0 := (mk_init _ _ _ A 10 IncrementalBits.Start BigBits.Parse)).
  cbv in rel0.
  subst rel0.

  do 5 run_bisim.
  
  (* huh, the next run_bisim call fails and also the final part of the entailment is funky *)


Admitted.
