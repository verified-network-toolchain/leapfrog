Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4automata.FirstOrder.
Require Import Poulet4.P4automata.Ntuple.

Import ListNotations.
Import HListNotations.
Local Open Scope program_scope.

Section AutModel.
  Set Implicit Arguments.
  (* State identifiers. *)
  Variable (S: Type).
  Context `{S_eq_dec: EquivDec.EqDec S eq}.
  Context `{S_finite: @Finite S _ S_eq_dec}.

  (* Header identifiers. *)
  Variable (H: nat -> Type).
  Context `{H'_eq_dec: EquivDec.EqDec (P4A.H' H) eq}.
  Context `{H_finite: @Finite (Syntax.H' H) _ H'_eq_dec}.

  Variable (a: P4A.t S H).

  Inductive sorts: Type :=
  | Bits (n: nat)
  | Store.
  Derive NoConfusion for sorts.

  Inductive funs: arity sorts -> sorts -> Type :=
  | BitsLit: forall n, n_tuple bool n -> funs [] (Bits n)
  | Concat: forall n m, funs [Bits n; Bits m] (Bits (n + m))
  | Slice: forall n hi lo, funs [Bits n] (Bits (Nat.min (1 + hi) n - lo))
  | Lookup: forall n, H n -> funs [Store] (Bits n).
  Arguments Lookup n k : clear implicits.

  Inductive rels: arity sorts -> Type :=.

  Definition sig: signature :=
    {| sig_sorts := sorts;
       sig_funs := funs;
       sig_rels := rels |}.

  Definition fm ctx := FirstOrder.fm sig ctx.
  Definition tm ctx := FirstOrder.tm sig ctx.

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
    { mod_fns (BitsLit n xs) hnil := xs;
      mod_fns (Concat n m) (xs ::: ys ::: hnil) :=
        n_tuple_concat xs ys;
      mod_fns (Slice n hi lo) (xs ::: hnil) :=
        n_tuple_slice hi lo xs;
      mod_fns (Lookup n k) (store ::: hnil) :=
        match P4A.find H k store with
        | P4A.VBits _ v => v
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

  Obligation Tactic := intros.
  Equations simplify_concat_zero {ctx srt} (e: tm ctx srt) : tm ctx srt :=
    { simplify_concat_zero (TFun sig (Concat 0 m) (_ ::: x ::: hnil)) :=
        simplify_concat_zero x;
      simplify_concat_zero (TFun sig (Concat (Datatypes.S n) m) (x ::: y ::: hnil)) :=
        TFun sig (Concat (Datatypes.S n) m)
                 (simplify_concat_zero x :::
                  simplify_concat_zero y ::: hnil);
      simplify_concat_zero (TFun sig (Slice n hi lo) (x ::: hnil)) :=
        TFun sig (Slice n hi lo) (simplify_concat_zero x ::: hnil);
      simplify_concat_zero (TFun sig f args) :=
        TFun sig f args;
      simplify_concat_zero (TVar x) := TVar x;
    }.

  Import Coq.Program.Equality.

  Lemma concat_emp' :
    forall n (t: n_tuple bool n), n_tuple_concat (tt: n_tuple _ 0) t = t.
  Proof.
    intros.
    apply JMeq_eq.
    eapply concat_emp.
  Qed.

  Lemma interp_zero_tm:
     forall c (t: tm c (Bits 0)) v,
       interp_tm (m := fm_model) v t = tt
  .
  Proof.
    intros; now destruct (interp_tm v t).
  Qed.


  Lemma simplify_concat_zero_corr :
    forall ctx srt (t : tm ctx srt) v,
      interp_tm (m := fm_model) v t = interp_tm v (simplify_concat_zero (ctx := ctx) t).
  Proof.
    intros.
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
          apply H0.
        * autorewrite with simplify_concat_zero.
          autorewrite with interp_tm; simpl.
          autorewrite with mod_fns.
          f_equal; apply H0.
      + autorewrite with simplify_concat_zero.
        autorewrite with interp_tm; simpl.
        do 2 f_equal.
        apply H0.
      + now autorewrite with simplify_concat_zero.
  Qed.

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
      interp_fm valu f <-> interp_fm (m := fm_model) valu (simplify_concat_zero_fm f)
  .
  Proof.
    intros.
    induction f; autorewrite with simplify_concat_zero_fm;
    (try now split; intros; auto);
    autorewrite with interp_fm;
    repeat erewrite <- simplify_concat_zero_corr;
    (try now split; intros; auto).
    - split; unfold "~"; intros; apply H0; eapply IHf; auto.
    - erewrite IHf1. erewrite IHf2. split; intros; auto.
    - erewrite IHf1. erewrite IHf2. split; intros; auto.
    - erewrite IHf1. erewrite IHf2. split; intros; auto.
    - setoid_rewrite IHf. split; intros; auto.
  Qed.

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
      interp_fm valu f <-> interp_fm (m := fm_model) valu (simplify_eq_zero_fm f).
  Proof.
    intros.
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
    - split; unfold "~"; intros; apply H0; eapply IHf; auto.
    - erewrite IHf1. erewrite IHf2. split; intros; auto.
    - erewrite IHf1. erewrite IHf2. split; intros; auto.
    - erewrite IHf1. erewrite IHf2. split; intros; auto.
    - setoid_rewrite IHf. split; intros; auto.
  Qed.


  (* It feels like this should be an instance of map_subst, but I can't get
     that to go through so here's a direct proof. *)
  Lemma interp_tm_rect:
    forall n1 n2 (c: ctx sig) valu (e: tm c (Bits n1)) (Heq: n1 = n2),
      eq_rect n1 (n_tuple bool) (interp_tm (m := fm_model) valu e) n2 Heq =
      interp_tm valu (eq_rect n1 (tm c ∘ Bits) e n2 Heq).
  Proof.
    intros; now rewrite <- Heq.
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

(* Register FirstOrderConfRelSimplified.Bits as p4a.sorts.bits. *)
Register FirstOrderConfRelSimplified.Store as p4a.sorts.store.

(* Register FirstOrderConfRelSimplified.BitsLit as p4a.funs.bitslit. *)
(* Register FirstOrderConfRelSimplified.Concat as p4a.funs.concat. *)
(* Register FirstOrderConfRelSimplified.Slice as p4a.funs.slice. *)
Register FirstOrderConfRelSimplified.Lookup as p4a.funs.lookup.

Register HList.HNil as p4a.core.hnil.
Register HList.HCons as p4a.core.hcons.
