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
      simplify_concat_zero (TFun _ (Slice n hi lo) args) := TFun _ _ args;
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
  exact (Slice n hi lo).
  Defined.
  Next Obligation.
  exact (Lookup n k).
  Defined.

  Lemma simplify_concat_zero_corr :
    forall ctx v srt (t : tm ctx srt),
      interp_tm (m := fm_model) v t = interp_tm v (simplify_concat_zero (ctx := ctx) t).
  Proof.
    intros.
    induction t. (* this doesn't actually give an IHOP? *)
    (* also promising: tm_ind *)
    - autorewrite with simplify_concat_zero.
      trivial.
    - induction s; cbn; autorewrite with simplify_concat_zero; trivial.
      (* need an IHOP for this goal... *)
      admit.
  Admitted.

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
  Admitted.

End AutModel.