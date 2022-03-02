Require Import Coq.Lists.List.
Require Import Leapfrog.FinType.
Require Import Leapfrog.ConfRel.
Require Import Leapfrog.P4automaton.
Require Import MirrorSolve.FirstOrder.
Require Import MirrorSolve.HLists.
Require Import Leapfrog.Ntuple.


Require Import Coq.Numbers.BinNums.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.

Import ListNotations.
Import HListNotations.

Section FirstOrderBitVec.
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
  | Bits (n: N).

  Inductive funs: arity sorts -> sorts -> Type :=
  | BitsLit: forall n, n_tuple bool n -> funs [] (Bits n)
  | Concat: forall n m, funs [Bits n; Bits m] (Bits (n + m))
  | Slice: forall n hi lo, funs [Bits n] (Bits (N.min (1 + hi) n - lo)).

  Inductive rels: arity sorts -> Type :=.

  Definition sig: signature :=
    {| sig_sorts := sorts;
       sig_funs := funs;
       sig_rels := rels |}.

  (* Locate FirstOrder.fm. *)

  Definition fm ctx := fm sig ctx.
  Definition tm ctx := tm sig ctx.

  Definition mod_sorts (s: sig_sorts sig) : Type :=
    match s with
    | Bits n => n_tuple bool n
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
        n_tuple_slice hi lo xs
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

  Definition val_wf (srt: sorts): mod_sorts srt -> Prop :=
    match srt as srt' return mod_sorts srt' -> Prop with 
    | Bits n => fun v => @n_tup_wf _ n v
    end.


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
  
  
  Require Import Coq.Program.Tactics.
  Require Import Coq.Program.Equality.

  Lemma valu_find_wf : 
    forall c srt (vs: valu _ _ c) v,
      valu_wf (m := fm_model) val_wf vs -> 
      val_wf srt (find _ fm_model v vs).
  Proof.
    intros.
    dependent induction vs;
    dependent destruction v;
    autorewrite with find;
    simpl in *;
    intuition eauto.
  Qed.

  Lemma tm_interp_wf : 
    forall c (v: valu _ _ c) srt (t: tm c srt), 
      valu_wf (m := fm_model) val_wf v ->
      tm_wf t -> 
      val_wf srt (interp_tm (m := fm_model) v t).
  Proof. 
    dependent induction t using tm_ind'; intros;
    autorewrite with interp_tm; try now (
      eapply valu_find_wf; auto
    ).

    destruct srt eqn:?;
    repeat match goal with 
    | H: HList.t _ (_ :: _) |- _ => 
      dependent destruction H
    | H: HList.t _ nil |- _ => 
      dependent destruction H
    end; [ | | set (foo := (N.min (1 + hi) n - lo)%N) in *];
    simpl;
    [| | subst foo];
    autorewrite with mod_fns;
    simpl in *;
    intuition eauto.
    - eapply NtupleProofs.n_tup_cat_wf; 
      intuition eauto.
    - eapply NtupleProofs.n_tup_slice_wf;
      intuition eauto.
  Qed.
End FirstOrderBitVec.


