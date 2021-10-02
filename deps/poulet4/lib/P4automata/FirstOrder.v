From Equations Require Import Equations.
Require Import Coq.Program.Equality.

Set Universe Polymorphism.

(* CPDT style heterogeneous lists. *)
Module HList.
  Set Implicit Arguments.
  Section HList.
    Variable A: Type.
    Variable B: A -> Type.
    Inductive t : list A -> Type :=
    | HNil: t nil
    | HCons: forall a rest,
        B a ->
        t rest ->
        t (a :: rest).
  End HList.
  Derive NoConfusion Signature for t.

  Fixpoint mapl {A B} (f: forall a: A, B a) (l: list A): HList.t B l :=
    match l with
    | nil => HNil _
    | cons a l => HCons _ (f a) (mapl f l)
    end.

  Fixpoint map {A B C l} (f: forall a: A, B a -> C a) (hl: t B l): t C l :=
    match hl with
    | HNil _ => HNil _
    | HCons a x hl => HCons _ (f a x) (map f hl)
    end.
End HList.

Module HListNotations.
  Notation "x ::: xs" := (HList.HCons _ x xs) (at level 60, right associativity).
  Notation "'hnil'" := (HList.HNil _).
End HListNotations.

Definition arity sorts := list sorts.

Record signature: Type :=
  { sig_sorts: Type;
    sig_funs: arity sig_sorts -> sig_sorts -> Type;
    sig_rels: arity sig_sorts -> Type }.

Section FOL.
  Variable sig: signature.

  (* Variable context. *)
  Inductive ctx: Type :=
  | CEmp: ctx
  | CSnoc: ctx -> sig.(sig_sorts) -> ctx.
  Derive NoConfusion for ctx.

  Import HListNotations.

  Ltac solve_existT :=
    repeat match goal with
           | H: ?X = ?X |- _ => clear H
           | H: existT _ _ _ = existT _ _ _ |- _ =>
             eapply Eqdep.EqdepTheory.inj_pair2 in H; subst
           end.

  Inductive var: ctx -> sig.(sig_sorts) -> Type :=
  | VHere:
      forall ctx s,
        var (CSnoc ctx s) s
  | VThere:
      forall ctx s s',
        var ctx s' ->
        var (CSnoc ctx s) s'.
  Derive Signature NoConfusion for var.

  (* First-order terms. *)
  Inductive tm: ctx -> sig.(sig_sorts) -> Type :=
  | TVar: forall c s,
      var c s ->
      tm c s
  | TFun:
      forall c args ret,
        sig.(sig_funs) args ret ->
        HList.t (tm c) args ->
        tm c ret.
  Derive Signature for tm.

  (* First-order formulas. *)
  Inductive fm: ctx -> Type :=
  | FTrue: forall c, fm c
  | FFalse: forall c, fm c
  | FEq: forall c s,
      tm c s ->
      tm c s ->
      fm c
  | FRel:
      forall c args,
        sig.(sig_rels) args ->
        HList.t (tm c) args ->
        fm c
  | FNeg: forall c, fm c -> fm c
  | FOr: forall c, fm c -> fm c -> fm c
  | FAnd: forall c, fm c -> fm c -> fm c
  | FImpl: forall c, fm c -> fm c -> fm c
  | FForall:
      forall c s,
        fm (CSnoc c s) ->
        fm c.
  Derive Signature for fm.

  Record model :=
    { mod_sorts: sig.(sig_sorts) -> Type;
      mod_fns: forall args ret,
          sig.(sig_funs) args ret ->
          HList.t mod_sorts args ->
          mod_sorts ret;
      mod_rels: forall args,
          sig.(sig_rels) args ->
          HList.t mod_sorts args ->
          Prop }.

  Section Interp.
    Variable (m: model).

    Inductive valu : ctx -> Type :=
    | VEmp: valu CEmp
    | VSnoc: forall s c,
        m.(mod_sorts) s ->
        valu c ->
        valu (CSnoc c s).
    Derive Signature for valu.

    Equations find {c s} (x: var c s) (v: valu c) : m.(mod_sorts) s :=
      { find (VHere _ _) (VSnoc _ _ val _) := val;
        find (VThere _ _ _ x') (VSnoc _ _ _ v') := find x' v' }.

    Equations interp_tm (c: ctx) (s: sig_sorts sig) (v: valu c) (t: tm c s) : m.(mod_sorts) s
      by struct t :=
      { interp_tm _ _ v (TVar c s x) :=
          find x v;
        interp_tm _ _ v (TFun c typs rets fn args) :=
          m.(mod_fns) typs rets fn (interp_tms _ _ v args) }
    where interp_tms (c: ctx) typs (v: valu c) (args: HList.t (tm c) typs) : HList.t m.(mod_sorts) typs
      by struct args :=
      { interp_tms _ _ _ hnil := hnil;
        interp_tms _ _ _ (tm ::: args') :=
          interp_tm _ _ v tm ::: interp_tms _ _ v args' }.

    Equations interp_fm (c: ctx) (v: valu c) (f: fm c) : Prop
      by struct f :=
      { interp_fm _ v (FTrue _) := True;
        interp_fm _ v (FFalse _) := False;
        interp_fm _ v (FRel c typs rel args) :=
          m.(mod_rels) typs rel (interp_tms c _ v args);
        interp_fm _ v (FEq c s t1 t2) :=
          interp_tm c s v t1 = interp_tm c s v t2;
        interp_fm _ v (FNeg _ f) :=
          ~ interp_fm _ v f;
        interp_fm _ v (FOr _ f1 f2) :=
          interp_fm _ v f1 \/ interp_fm _ v f2;
        interp_fm _ v (FAnd _ f1 f2) :=
          interp_fm _ v f1 /\ interp_fm _ v f2;
        interp_fm _ v (FImpl _ f1 f2) :=
          interp_fm _ v f1 -> interp_fm _ v f2;
        interp_fm _ v (FForall c s f) :=
          forall val: m.(mod_sorts) s,
            interp_fm (CSnoc c s) (VSnoc _ _ val v) f }.
  End Interp.

  Fixpoint app_ctx (c1 c2: ctx): ctx :=
    match c2 with
    | CEmp => c1
    | CSnoc c2' sort => CSnoc (app_ctx c1 c2') sort
    end.

  Fixpoint ccons s (c: ctx) :=
    match c with
    | CEmp => CSnoc CEmp s
    | CSnoc c s0 => CSnoc (ccons s c) s0
    end.

  Fixpoint app_ctx' (c1 c2: ctx): ctx :=
    match c1 with
    | CEmp => c2
    | CSnoc c1' sort => app_ctx' c1' (ccons sort c2)
    end.

  Equations app_valu
             {m: model}
             {c c': ctx}
             (v: valu m c)
             (v': valu m c')
    : valu m (app_ctx c c') :=
    { app_valu v (VEmp _) := v;
      app_valu v (VSnoc _ _ _ x v') := VSnoc _ _ _ x (app_valu v v') }.

  Equations vcons {c s m} (x: mod_sorts m s) (v: valu m c) : valu m (ccons s c) :=
    { vcons x (VEmp _) := VSnoc _ _ _ x (VEmp _);
      vcons x (VSnoc _ _ _ y v) := VSnoc _ _ _ y (vcons x v) }.

  Equations app_valu'
             {m: model}
             {c c': ctx}
             (v: valu m c)
             (v': valu m c')
    : valu m (app_ctx' c c') :=
    { app_valu' (VEmp _) v' := v';
      app_valu' (VSnoc _ _ _ x v) v' := app_valu' v (vcons x v') }.

  Lemma app_ctx_emp_l:
    forall c,
      c = app_ctx CEmp c.
  Proof.
    induction c.
    - reflexivity.
    - simpl.
      congruence.
  Qed.

  Lemma app_ctx_app_ctx':
    forall c1 c2,
      app_ctx c1 c2 = app_ctx' c1 c2.
  Proof.
    induction c1; induction c2; intros; simpl.
    - reflexivity.
    - rewrite <- app_ctx_emp_l.
      reflexivity.
    - rewrite <- IHc1.
      simpl.
      reflexivity.
    - rewrite IHc2.
      simpl.
      rewrite <- IHc1.
      cbn.
      rewrite <- IHc1.
      simpl.
      reflexivity.
  Qed.

  Lemma app_ctx'_app_ctx:
    forall c1 c2,
      app_ctx' c1 c2 = app_ctx c1 c2.
  Proof.
    intros.
    apply eq_sym.
    apply app_ctx_app_ctx'.
  Qed.

  Fixpoint quantify {c0: ctx} (c: ctx): fm (app_ctx c0 c) -> fm c0 :=
    match c as c' return fm (app_ctx c0 c') -> fm c0 with
    | CEmp => fun f => f
    | CSnoc c' sort => fun f => quantify c' (FForall _ _ f)
    end.

  Lemma quantify_correct:
    forall m c c' (v': valu m c') phi,
     interp_fm m c' v' (quantify c phi) <->
     forall valu,
       interp_fm m (app_ctx c' c) (app_valu v' valu) phi.
  Proof.
    induction c.
    - cbn.
      intuition.
      + dependent destruction valu0.
        assumption.
      + specialize (H (VEmp _)).
        autorewrite with app_valu in *.
        assumption.
    - cbn.
      intuition.
      + cbn in *.
        dependent destruction valu0.
        rewrite IHc in H.
        specialize (H valu0).
        autorewrite with app_valu interp_fm in *.
        eauto.
      + rewrite IHc.
        intros v.
        autorewrite with interp_fm.
        intros.
        pose (VSnoc _ _ _ val v) as v''.
        specialize (H v'').
        eauto.
  Qed.

  Equations quantify' {c0: ctx} (c: ctx) (f: fm (app_ctx' c0 c)) : fm c0 :=
    { quantify' c f := quantify c (eq_rect _ (fun x => fm x) f (app_ctx c0 c)
                                           (app_ctx'_app_ctx _ _)) }.

  Lemma quantify'_correct:
    forall m c c' (v': valu m c') phi,
     interp_fm m c' v' (quantify' c phi) <->
     forall valu,
       interp_fm m (app_ctx' c' c) (app_valu' v' valu) phi.
  Proof.
  Admitted.

  Equations quantify_all {c: ctx} (f: fm c): fm CEmp := {
    @quantify_all (CSnoc c _) f := quantify_all (FForall _ _ f);
    @quantify_all CEmp f := f;
  }.

  Lemma quantify_all_correct:
    forall m c phi,
     interp_fm m CEmp (VEmp _) (quantify_all phi) <->
     forall valu,
       interp_fm m c valu phi.
  Proof.
    dependent induction c; intros.
    - autorewrite with quantify_all.
      firstorder.
      now dependent destruction valu0.
    - autorewrite with quantify_all.
      rewrite IHc.
      split; intros.
      + dependent destruction valu0.
        specialize (H valu0).
        autorewrite with interp_fm in H.
        apply H.
      + autorewrite with interp_fm; intros.
        apply H.
  Qed.

  Fixpoint reindex_var {c c': ctx} {sort: sig.(sig_sorts)} (v: var c' sort) : var (app_ctx c c') sort :=
    match v in (var c' sort) return (var (app_ctx c c') sort) with
    | VHere ctx _ =>
      VHere (app_ctx c ctx) _
    | VThere ctx _ _ v' =>
      VThere (app_ctx c ctx) _ _ (reindex_var v')
    end.

  Equations reindex_tm {c c': ctx} {sort: sig.(sig_sorts)} (t: tm c' sort) : tm (app_ctx c c') sort := {
    reindex_tm (TVar _ _ v) := TVar _ _ (reindex_var v);
    reindex_tm (TFun _ _ _ f args) := TFun _ _ _ f (reindex_tms args)
  } where reindex_tms {c c':ctx} {sorts: list sig.(sig_sorts)} (ts: HList.t (tm c') sorts) : HList.t (tm (app_ctx c c')) sorts := {
    reindex_tms hnil := hnil;
    reindex_tms (t ::: ts) := reindex_tm t ::: reindex_tms ts
  }.

  Equations weaken_var {sort: sig.(sig_sorts)}
             {c1: ctx} (c2: ctx) (v: var c1 sort)
    : var (app_ctx c1 c2) sort :=
    { weaken_var CEmp v := v;
      weaken_var (CSnoc c2' sort') v := VThere _ _ _ (weaken_var c2' v) }.

  Equations weaken_tm (sort: sig.(sig_sorts))
             (c1: ctx) (c2: ctx) (t: tm c1 sort)
    : tm (app_ctx c1 c2) sort
    by struct t :=
    { weaken_tm _ _ c2 (TVar _ _ v) := TVar _ _ (weaken_var c2 v);
      weaken_tm _ _ c2 (TFun _ _ _ f args) :=
        TFun _ _ _ f (weaken_tms _ _ c2 args) }
  where weaken_tms (sorts: list sig.(sig_sorts))
       (c1: ctx) (c2: ctx) (ts: HList.t (tm c1) sorts)
        : HList.t (tm (app_ctx c1 c2)) sorts
    by struct ts :=
    { weaken_tms _ _ _ hnil := hnil;
      weaken_tms _ _ _ (t ::: ts) :=
        weaken_tm _ _ c2 t ::: weaken_tms _ _ c2 ts }.

End FOL.

Arguments TVar {_ _ _}.
Arguments TFun _ {_ _ _} _ _.
Arguments FTrue {sig c}.
Arguments FFalse {sig c}.
Arguments FEq {_ _ _} _ _.
Arguments FRel {_ _} _ _.
Arguments FNeg {_} _.
Arguments FOr {_} _ _.
Arguments FAnd {_} _ _.
Arguments FForall {_ _} _.
Arguments FImpl {_ _} _ _.

Arguments interp_fm {_ _ _} _ _.
Arguments interp_tm {_ _ _ _} _ _.
Arguments interp_tms {_ _ _ _} _ _.

Arguments app_ctx {sig} c1 c2.
Arguments quantify {sig c0} c f.
Arguments quantify' {sig c0} c f.
Arguments quantify_all {sig} c f.
Arguments reindex_var {sig c c' sort} v.
Arguments reindex_tm {sig c c' sort} t.
Arguments reindex_tms {sig c c' sorts} ts.
Arguments weaken_var {sig sort c1} c2 v.
Arguments weaken_tm {sig sort c1} c2 t.
