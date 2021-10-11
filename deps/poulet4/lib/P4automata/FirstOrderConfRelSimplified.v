Require Import Coq.Lists.List.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4automata.FirstOrder.
Require Import Poulet4.P4automata.Ntuple.

Import ListNotations.
Import HListNotations.

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
    { simplify_concat_zero (TFun _ (Concat 0 m) (_ ::: x ::: _)) := simplify_concat_zero _;
      simplify_concat_zero (TFun _ (Concat (Datatypes.S n) m) args) := TFun _ _ _;
      simplify_concat_zero (TFun _ (BitsLit n xs) args) := TFun _ _ args;
      simplify_concat_zero (TFun _ (Slice n hi lo) args) := TFun _ _ _;
      simplify_concat_zero (TFun _ (Lookup n k) args) := TFun _ _ args;
      simplify_concat_zero (TVar x) := TVar x;
    }.
  Next Obligation.
  exact (BitsLit n xs).
  Defined.
  Next Obligation.
  simpl.
  exact x.
  Defined.
  Next Obligation.
  exact [Bits (Datatypes.S n); Bits m].
  Defined.
  Next Obligation.
  unfold simplify_concat_zero_obligations_obligation_3.
  simpl.
  exact (Concat (Datatypes.S n) m).
  Defined.
  Next Obligation.
  unfold simplify_concat_zero_obligations_obligation_3.
  simpl.
  inversion args.
  inversion X0.
  exact (simplify_concat_zero _ _ X ::: simplify_concat_zero _ _ X1 ::: hnil).
  Defined.
  Next Obligation.
  exact [Bits n].
  Defined.
  Next Obligation.
  simpl.
  unfold simplify_concat_zero_obligations_obligation_6.
  exact (Slice n hi lo).
  Defined.
  Next Obligation.
  unfold simplify_concat_zero_obligations_obligation_6, simplify_concat_zero_obligations_obligation_7.
  inversion args.
  exact ((simplify_concat_zero _ _ X) ::: X0).
  Defined.
  Next Obligation.
  exact (Lookup n k). 
  Defined.
  



  Import Coq.Program.Equality. 

  Lemma interp_zero_tm : 
    forall ctx (t: tm ctx (Bits 0)) v,
      interp_tm (m := fm_model) v t = tt.
  Proof.
  Admitted.

  Lemma concat_emp' : 
    forall n (t: n_tuple bool n), n_tuple_concat (tt: n_tuple _ 0) t = t.
  Proof.
    (* eapply concat_emp. *)
  Admitted.

  Lemma simplify_concat_zero_corr :
    forall ctx srt (t : tm ctx srt) v,
      interp_tm (m := fm_model) v t = interp_tm v (simplify_concat_zero (ctx := ctx) t).
  Proof.

    pose proof (tm_ind' sig). 
    specialize (H0 (fun c srt (t : tm c srt) => forall v, interp_tm (m := fm_model) v t = interp_tm v (simplify_concat_zero (ctx := c) t))).
    apply H0; clear H0; intros.
    - autorewrite with simplify_concat_zero.
      trivial.
    - destruct srt;
      autorewrite with simplify_concat_zero.
      + unfold simplify_concat_zero_obligations_obligation_1.
        trivial.
      + dependent destruction hl.
        dependent destruction hl.
        dependent destruction hl.
        simpl in H0.
        destruct H0 as [? [? _]].

        destruct n.
        * autorewrite with simplify_concat_zero.
          unfold simplify_concat_zero_obligations_obligation_2.
          erewrite <- H1.
          autorewrite with interp_tm.
          simpl.
          autorewrite with mod_fns.

          pose proof concat_emp.
          erewrite interp_zero_tm.
          erewrite concat_emp'.
          trivial.
        * autorewrite with simplify_concat_zero.
          unfold simplify_concat_zero_obligations_obligation_4.
          unfold simplify_concat_zero_obligations_obligation_5.
          unfold eq_rect_r.
          simpl.
          autorewrite with interp_tm.
          unfold interp_tms.
          unfold simplify_concat_zero_obligations_obligation_3.
        
          erewrite H0.
          erewrite H1.
          trivial.
      + unfold simplify_concat_zero_obligations_obligation_7, simplify_concat_zero_obligations_obligation_8.
        simpl.
        dependent destruction hl.
        dependent destruction hl.
        unfold eq_rect_r.
        simpl in *.
        destruct H0 as [? _].
        autorewrite with interp_tm.
        simpl.
        erewrite <- H0.
        trivial.
      + unfold simplify_concat_zero_obligations_obligation_9; trivial. 
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
    destruct f; autorewrite with simplify_concat_zero_fm;
    (try now split; intros; auto);
    autorewrite with interp_fm;
    repeat erewrite <- simplify_concat_zero_corr;
    (try now split; intros; auto).

  Admitted.

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

Register FirstOrderConfRelSimplified.Bits as p4a.sorts.bits.
Register FirstOrderConfRelSimplified.Store as p4a.sorts.store.

Register FirstOrderConfRelSimplified.BitsLit as p4a.funs.bitslit.
Register FirstOrderConfRelSimplified.Concat as p4a.funs.concat.
Register FirstOrderConfRelSimplified.Slice as p4a.funs.slice.
Register FirstOrderConfRelSimplified.Lookup as p4a.funs.lookup.

Register HList.HNil as p4a.core.hnil.
Register HList.HCons as p4a.core.hcons.