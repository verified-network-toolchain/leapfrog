Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Leapfrog.FinType.
Require Import Leapfrog.ConfRel.
Require Import Leapfrog.P4automaton.
Require Import MirrorSolve.FirstOrder.
Require Import MirrorSolve.HLists.
Require Import Leapfrog.Ntuple.

Import ListNotations.
Import HListNotations.
Local Open Scope program_scope.

Require Import Coq.Numbers.BinNums.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.

Set Universe Polymorphism.

Section AutModel.
  Set Implicit Arguments.
  (* State identifiers. *)
  Variable (St: Type).
  Context `{St_eq_dec: EquivDec.EqDec St eq}.
  Context `{St_finite: @Finite St _ St_eq_dec}.

  (* Header identifiers. *)
  Variable (Hdr: Type).
  Context `{Hdr_eq_dec: EquivDec.EqDec Hdr eq}.
  Context `{Hdr_finite: @Finite Hdr _ Hdr_eq_dec}.
  Variable (Hdr_sz: Hdr -> N).

  Variable (a: P4A.t St Hdr_sz).

  Inductive sorts: Type :=
  | Bits (n: N)
  | Store.
  Derive NoConfusion for sorts.

  Inductive funs: arity sorts -> sorts -> Type :=
  | BitsLit: forall n, n_tuple bool n -> funs [] (Bits n)
  | Concat: forall n m, funs [Bits n; Bits m] (Bits (n + m))
  | Slice: forall n hi lo, funs [Bits n] (Bits (N.min (1 + hi) n - lo))
  | Lookup: forall h, funs [Store] (Bits (Hdr_sz h)).

  Inductive rels: arity sorts -> Type :=.

  Definition sig: signature :=
    {| sig_sorts := sorts;
       sig_funs := funs;
       sig_rels := rels |}.

  Definition fm ctx := fm sig ctx.
  Definition tm ctx := tm sig ctx.

  Definition mod_sorts (s: sig_sorts sig) : Type :=
    match s with
    | Bits n => n_tuple bool n
    | Store => store (P4A.interp a)
    end.

  Obligation Tactic := idtac.
  Equations mod_fns
             params ret
             (f: sig_funs sig params ret)
             (args: HList.t mod_sorts params)
    : mod_sorts ret :=
    { mod_fns (BitsLit xs) hnil := xs;
      mod_fns (Concat n m) (xs ::: ys ::: hnil) :=
        n_tuple_concat xs ys;
      mod_fns (Slice n hi lo) (xs ::: hnil) :=
        n_tuple_slice hi lo xs;
      mod_fns (Lookup k) (store ::: hnil) :=
        match P4A.find Hdr Hdr_sz k store with
        | P4A.VBits v => v
        end
    }.

  Definition mod_rels params
    (args: sig_rels sig params)
    (env: HList.t mod_sorts params) : Prop :=
    match args with
    end.

  Program Definition fm_model : model sig := {|
    FirstOrder.mod_sorts := mod_sorts;
    FirstOrder.mod_fns := mod_fns;
    FirstOrder.mod_rels := mod_rels;
  |}.

  Definition store_wf val :=
    forall a n, P4A.find Hdr Hdr_sz a val = P4A.VBits n -> n_tup_wf n.

  Inductive val_wf: forall s, mod_sorts s -> Prop :=
    | ValWellFormedBits: forall n (t: n_tuple bool n), n_tup_wf t -> val_wf (Bits _) t
    | ValWellFormedStore: forall st, store_wf st -> val_wf Store st.

  Hint Constructors val_wf.

  Ltac inv_v_wf H := 
    refine (match H with 
    | ValWellFormedBits _ => _
    | _ => _
    end); try exact idProp.

  Fixpoint tm_wf {c srt} (t: tm c srt) : Prop :=
    match t with
    | TVar v => True
    | @TFun _ c' args ret f hl =>
      let rec := HList.all (fun srt => @tm_wf c' srt) hl in 
      let fun_wf := 
        match f with 
        | BitsLit vs => n_tup_wf vs
        | _ => True
        end in 
      rec /\ fun_wf
    end.
  
  Fixpoint check_tm_wf {c srt} (t: tm c srt) : bool :=
    match t with
    | TVar v => true
    | @TFun _ c' args ret f hl =>
      let rec : bool := 
        (fix hlworker l (hl: HList.t _ l) {struct hl} : bool := 
          match hl with 
          | hnil => true
          | t ::: hl' => andb (check_tm_wf t) (hlworker _ hl') 
          end
        ) _ hl in 
      let fun_wf := 
        match f with 
        | @BitsLit n vs => Nat.eqb (length vs) (N.to_nat n)
        | _ => true
        end in 
      andb rec fun_wf
    end.

  Require Import Coq.Program.Program.
  Require Import Coq.Arith.EqNat.

  Lemma check_tm_wf_corr : 
    forall c srt (t: tm c srt), 
      check_tm_wf t = true <-> tm_wf t.
  Proof.
    induction t using tm_ind'.
    - simpl.
      split; trivial.
    - 
      destruct srt; 
      repeat match goal with 
      | H: HList.t _ _ |- _ => dependent destruction H
      end;
      simpl in *.
      + 
        pose proof @Bool.Is_true_eq_left (Nat.eqb (length n0) (N.to_nat n)).
        unfold n_tup_wf.
        assert (len_pf n0 (N.to_nat n) <-> length n0 = (N.to_nat n)) by shelve.
        
        erewrite H1. 
        assert (length n0 = N.to_nat n <-> Nat.eqb (length n0) (N.to_nat n) = true) by shelve.
        
        erewrite H2.
        split; intros; intuition eauto.
      + intuition eauto.
        * admit.
        * admit.
        * erewrite H7. 
          erewrite H3.
          simpl.
          trivial.
      + intuition eauto.
        * eapply H.
          admit.
        * erewrite H3.
          exact eq_refl.
      + intuition eauto.
        * eapply H.
          admit.
        * erewrite H3.
          exact eq_refl.
  Admitted.

  Fixpoint valu_wf {c} (vs: valu _ fm_model c) : Prop :=
    match vs with 
    | VEmp _ _ => True
    | VSnoc _ _ srt _ v inner  => 
      val_wf srt v /\ valu_wf inner
    end.

  Fixpoint fm_wf {ctx} (e: fm ctx) : Prop := 
    match e with 
    | FTrue => True
    | FFalse => True
    | (FEq e1 e2) => tm_wf e1 /\ tm_wf e2
    | (FRel _ _ _) => True
    | (FNeg _ f) => fm_wf f
    | (FOr _ f1 f2) => fm_wf f1 /\ fm_wf f2
    | (FAnd _ f1 f2) => fm_wf f1 /\ fm_wf f2
    | (FImpl f1 f2) => fm_wf f1 /\ fm_wf f2
    | (FForall _ f) => fm_wf f
    end.

  Fixpoint check_fm_wf {ctx} (e: fm ctx) : bool := 
    match e with 
    | FTrue => true
    | FFalse => true
    | (FEq e1 e2) => Bool.eqb (check_tm_wf e1) (check_tm_wf e2)
    | (FRel _ _ _) => true
    | (FNeg _ f) => check_fm_wf f
    | (FOr _ f1 f2) => Bool.eqb (check_fm_wf f1) (check_fm_wf f2)
    | (FAnd _ f1 f2) => Bool.eqb (check_fm_wf f1) (check_fm_wf f2)
    | (FImpl f1 f2) => Bool.eqb (check_fm_wf f1) (check_fm_wf f2)
    | (FForall _ f) => check_fm_wf f
    end.

  Lemma check_fm_wf_corr: 
    forall c (e: fm c), 
      check_fm_wf e = true <-> fm_wf e.
  Proof.
    dependent induction e;
    simpl in *;
    intuition eauto.
    (* todo: write a tactic for discharging these... *)
    all: admit.
  Admitted.



  (* Lemma interp_valu_wf : 
    forall c vs s t, valu_wf vs -> val_wf s (interp_tm (c := c) vs t).
  Admitted.

  Hint Immediate interp_valu_wf. *)

  Require Import Coq.Program.Tactics.
  Require Import Coq.Program.Equality.

  Lemma valu_find_wf : 
    forall c srt (vs: valu _ _ c) v,
      valu_wf vs -> 
      val_wf srt (find _ fm_model v vs).
  Proof.
    intros.
    dependent induction vs;
    dependent destruction v;
    autorewrite with find;
    simpl in *;
    intuition eauto.
  Qed.

  Lemma valu_p4afind_wf:  
    forall c (vs: valu _ _ c) (t : tm c Store) h,
      valu_wf vs ->
      tm_wf t ->
      match
        P4A.find Hdr Hdr_sz h (interp_tm (m := fm_model) vs t)
      with
      | P4A.VBits v => n_tup_wf v
      end.
  Proof.
  Admitted.
    
  Lemma tm_interp_wf : 
    forall c (v: valu _ _ c) srt (t: tm c srt), 
      valu_wf v ->
      tm_wf t -> 
      val_wf srt (interp_tm (m := fm_model) v t).
  Proof. 
    dependent induction t using tm_ind'; intros;
    autorewrite with interp_tm; try now (
      eapply valu_find_wf; auto
    ).

    Opaque N.add.

    destruct srt eqn:?;
    repeat match goal with 
    | H: HList.t _ (_ :: _) |- _ => 
      dependent destruction H
    | H: HList.t _ nil |- _ => 
      dependent destruction H
    end; 
    simpl in *;
    autorewrite with mod_fns;
    intuition eauto.
    - subst.
      econstructor.
      eapply NtupleProofs.n_tup_cat_wf; intuition eauto.
      + specialize (H2 _ H0 H3).
        inv_v_wf H2.
        eauto.
      + specialize (H1 _ H0 H).
        inv_v_wf H1.
        eauto.

    - econstructor.
      eapply NtupleProofs.n_tup_slice_wf;
      intuition eauto.
      specialize (H2 _ H0 H1).
      inv_v_wf H2.
      eauto.
    - pose proof valu_p4afind_wf _ _ h H0 H1.
      destruct (P4A.find _ _ _ _).
      intuition eauto.
  Qed.





  Obligation Tactic := intros.
  Equations simplify_concat_zero {ctx srt} (e: tm ctx srt) : tm ctx srt :=
    { simplify_concat_zero (TFun sig (Concat 0 m) (_ ::: y ::: hnil)) :=
        simplify_concat_zero y;
      simplify_concat_zero (TFun sig (Concat n m) (x ::: y ::: hnil)) :=
        TFun sig (Concat n m)
                 (simplify_concat_zero x :::
                  simplify_concat_zero y ::: hnil);
      simplify_concat_zero (TFun sig (Slice n hi lo) (x ::: hnil)) :=
        TFun sig (Slice n hi lo) (simplify_concat_zero x ::: hnil);
      simplify_concat_zero (TFun sig f args) :=
        TFun sig f args;
      simplify_concat_zero (TVar x) := TVar x;
    }.

  

  

  Import Coq.Program.Equality.

  Lemma interp_zero_tm:
     forall c (t: tm c (Bits 0)) v,

       interp_tm (m := fm_model) v t = n_tuple_emp.
  Proof.
    dependent induction t using tm_ind'; intros;
    autorewrite with interp_tm.
    - induction v0;
      dependent destruction v;
      autorewrite with find.
      + simpl in *.
  Admitted.

  Lemma simplify_concat_zero_corr :
    forall ctx srt (t : tm ctx srt) v,
      interp_tm (m := fm_model) v t = interp_tm v (simplify_concat_zero (ctx := ctx) t).
  Proof.
  Admitted.
    (* intros.
    dependent induction t using tm_ind'.
    - now autorewrite with simplify_concat_zero.
    - destruct srt;
      repeat dependent destruction hl.
      + now autorewrite with simplify_concat_zero.
      + destruct n.
        * autorewrite with simplify_concat_zero.
          autorewrite with interp_tm; simpl.
          autorewrite with mod_fns.
          destruct (interp_tm v t).
          rewrite concat_emp'.
          apply H.
        * autorewrite with simplify_concat_zero.
          autorewrite with interp_tm; simpl.
          autorewrite with mod_fns.
          f_equal; apply H.
      + autorewrite with simplify_concat_zero.
        autorewrite with interp_tm; simpl.
        do 2 f_equal.
        apply H.
      + now autorewrite with simplify_concat_zero.
  Qed. *)

  Equations simplify_concat_zero_fm {ctx} (e: fm ctx) : fm ctx := {
    simplify_concat_zero_fm FTrue := FTrue;
    simplify_concat_zero_fm FFalse := FFalse;
    simplify_concat_zero_fm (FEq e1 e2) := FEq (simplify_concat_zero e1) (simplify_concat_zero e2);
    simplify_concat_zero_fm (FNeg f) := FNeg _ (simplify_concat_zero_fm f);
    simplify_concat_zero_fm (FOr f1 f2) := FOr _ (simplify_concat_zero_fm f1) (simplify_concat_zero_fm f2);
    simplify_concat_zero_fm (FAnd f1 f2) := FAnd _ (simplify_concat_zero_fm f1) (simplify_concat_zero_fm f2);
    simplify_concat_zero_fm (FImpl f1 f2) := FImpl (simplify_concat_zero_fm f1) (simplify_concat_zero_fm f2);
    simplify_concat_zero_fm (FForall f) := FForall _ (simplify_concat_zero_fm f);
  }.

  Lemma simplify_concat_zero_fm_corr:
    forall ctx (f: fm ctx) valu,
      interp_fm_wf (m := fm_model) (wf := val_wf) valu f <-> interp_fm_wf (m := fm_model) (wf := val_wf) valu (simplify_concat_zero_fm f)
  .
  Proof.
  Admitted.
    (* intros.
    induction f; autorewrite with simplify_concat_zero_fm;
    (try now split; intros; auto);
    autorewrite with interp_fm;
    repeat erewrite <- simplify_concat_zero_corr;
    (try now split; intros; auto).
    - split; unfold "~"; intros; apply H; eapply IHf; auto.
    - erewrite IHf1. erewrite IHf2. split; intros; auto.
    - erewrite IHf1. erewrite IHf2. split; intros; auto.
    - erewrite IHf1. erewrite IHf2. split; intros; auto.
    - setoid_rewrite IHf. split; intros; auto.
  Qed. *)

  Equations simplify_eq_zero_fm {ctx} (e: fm ctx) : fm ctx := {
    simplify_eq_zero_fm FTrue := FTrue;
    simplify_eq_zero_fm FFalse := FFalse;
    simplify_eq_zero_fm (FEq e1 e2) := _;
    simplify_eq_zero_fm (FNeg f) := FNeg _ (simplify_eq_zero_fm f);
    simplify_eq_zero_fm (FOr f1 f2) := FOr _ (simplify_eq_zero_fm f1) (simplify_eq_zero_fm f2);
    simplify_eq_zero_fm (FAnd f1 f2) := FAnd _ (simplify_eq_zero_fm f1) (simplify_eq_zero_fm f2);
    simplify_eq_zero_fm (FImpl f1 f2) := FImpl (simplify_eq_zero_fm f1) (simplify_eq_zero_fm f2);
    simplify_eq_zero_fm (FForall f) := FForall _ (simplify_eq_zero_fm f);
  }.
  Next Obligation.
  destruct e0 eqn:?.
  - destruct n.
    + exact FTrue.
    + exact (FEq e1 e2).
  - exact (FEq e1 e2).
  Defined.

  Lemma simplify_eq_zero_fm_corr:
    forall ctx (f: fm ctx) valu,
      interp_fm_wf (m := fm_model) (wf := val_wf) valu f <-> interp_fm_wf (m := fm_model) (wf := val_wf) valu (simplify_eq_zero_fm f).
  Proof.
  Admitted.
    (* intros.
    induction f; autorewrite with simplify_eq_zero_fm;
    (try now split; intros; auto);
    autorewrite with interp_fm;
    (try now split; intros; auto).
    - unfold simplify_eq_zero_fm_obligations_obligation_1.
      destruct s.
      + destruct n.
        * repeat erewrite interp_zero_tm; split; intros; autorewrite with interp_fm; autorewrite with interp_fm; auto.
        * autorewrite with interp_fm; split; intros; auto.
      + autorewrite with interp_fm; split; intros; auto.
    - split; unfold "~"; intros; apply H; eapply IHf; auto.
    - erewrite IHf1. erewrite IHf2. split; intros; auto.
    - erewrite IHf1. erewrite IHf2. split; intros; auto.
    - erewrite IHf1. erewrite IHf2. split; intros; auto.
    - setoid_rewrite IHf. split; intros; auto.
  Qed. *)


  (* It feels like this should be an instance of map_subst, but I can't get
     that to go through so here's a direct proof. *)
  Lemma interp_tm_rect:
    forall n1 n2 (c: ctx sig) valu (e: tm c (Bits n1)) (Heq: n1 = n2),
      eq_rect n1 (n_tuple bool) (interp_tm (m := fm_model) valu e) n2 Heq =
      interp_tm valu (eq_rect n1 (tm c ∘ Bits) e n2 Heq).
  Proof.
    intros; now rewrite <- Heq.
  Qed.

  Lemma simplify_eq_zero_wf : 
    forall c (f: fm c), 
      fm_wf f -> 
      fm_wf (simplify_eq_zero_fm f).
  Proof.
    dependent induction f;
    intuition eauto;
    autorewrite with simplify_eq_zero_fm;
    simpl in *;
    intuition eauto.
    unfold simplify_eq_zero_fm_obligations_obligation_1.
    destruct s;
    simpl in *;
    intuition eauto.
    destruct n; 
    simpl in *;
    intuition eauto.
  Qed.

  Lemma simplify_concat_zero_wf:
    forall c (f: fm c),
      fm_wf f -> 
      fm_wf (simplify_concat_zero_fm f).
  Proof.
    dependent induction f;
    intuition eauto;
    autorewrite with simplify_concat_zero_fm;
    autorewrite with simplify_concat_zero;
    simpl in *;
    try now intuition eauto.
    split.
    - dependent induction t using tm_ind';
      intuition eauto.
      destruct srt;
      repeat match goal with 
      | H : HList.t _ _ |- _ => 
        dependent destruction H
      end;
      autorewrite with simplify_concat_zero;
      simpl in *;
      intuition.
      destruct n;
      autorewrite with simplify_concat_zero; 
      simpl;
      intuition.
    - dependent induction t0 using tm_ind';
      intuition eauto.
      destruct srt;
      repeat match goal with 
      | H : HList.t _ _ |- _ => 
        dependent destruction H
      end;
      autorewrite with simplify_concat_zero;
      simpl in *;
      intuition.
      destruct n;
      autorewrite with simplify_concat_zero; 
      simpl;
      intuition.
  Qed.

End AutModel.

Register TVar as p4a.core.var.
Register TFun as p4a.core.fun.

Register VHere as p4a.core.vhere.
Register VThere as p4a.core.vthere.


Register FEq as p4a.core.eq.
Register FTrue as p4a.core.tt.
Register FFalse as p4a.core.ff.
Register FRel as p4a.core.rel.
Register FNeg as p4a.core.neg.
Register FOr as p4a.core.or.
Register FAnd as p4a.core.and.
Register FForall as p4a.core.forall.

Register FImpl as p4a.core.impl.

Register CEmp as p4a.core.cnil.
Register CSnoc as p4a.core.csnoc.

Register FirstOrderConfRelSimplified.Store as p4a.sorts.store.

Register FirstOrderConfRelSimplified.Lookup as p4a.funs.lookup.

Register HList.HNil as p4a.core.hnil.
Register HList.HCons as p4a.core.hcons.

(* Register Ntuple.mk_n_tup as p4a.core.mk_n_tuple. *)
