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
  Derive Signature NoConfusion Subterm for var.
  Next Obligation.
    destruct a as [[c s] a].
    simpl in *.
    constructor; intros.
    remember {| pr1 := {| pr1 := c; pr2 := s |}; pr2 := a |}
      as a'.
    revert Heqa'.
    dependent induction H; intros; subst; cbn in *.
    - generalize dependent x.
      dependent induction a.
      + intros.
        inversion H.
      + intros.
        destruct x as [[cx sx] x]; cbn in *.
        assert (cx = ctx0 /\ s' = sx).
        {
          inversion H.
          solve_existT.
          tauto.
        }
        destruct H0; subst.
        assert (x = a).
        {
          inversion H.
          solve_existT.
          tauto.
        }
        subst.
        destruct a.
        * constructor; intros.
          remember {| pr1 := {| pr1 := CSnoc ctx0 s0; pr2 := s0 |}; pr2 := VHere ctx0 s0 |}
            as s0'.
          revert Heqs0'.
          induction H0; intros; subst; cbn in *.
          -- inversion H0.
          -- intuition.
        * constructor; intros.
          remember {| pr1 := {| pr1 := CSnoc ctx0 s0; pr2 := s' |}; pr2 := VThere ctx0 s0 s' a |}
            as s0'.
          revert Heqs0'.
          induction H0; intros; subst; cbn in *.
          -- inversion H0; solve_existT.
             eauto.
          -- intuition.
    - intuition.
  Qed.

  (* First-order terms. *)
  Inductive tm: ctx -> sig.(sig_sorts) -> Type :=
  | TVar: forall c s,
      var c s ->
      tm c s
  | TFun:
      forall c args ret,
        sig.(sig_funs) args ret ->
        tms c args ->
        tm c ret
  with tms: ctx -> list sig.(sig_sorts) -> Type :=
  | TSNil: forall c,
      tms c nil
  | TSCons: forall c s typs,
      tm c s ->
      tms c typs ->
      tms c (s :: typs)
  (* First-order formulas. *)
  with fm: ctx -> Type :=
  | FEq: forall c s,
      tm c s ->
      tm c s ->
      fm c
  | FRel:
      forall c args,
        sig.(sig_rels) args ->
        tms c args ->
        fm c
  | FNeg: forall c, fm c -> fm c
  | FOr: forall c, fm c -> fm c -> fm c
  | FAnd: forall c, fm c -> fm c -> fm c
  | FForall:
      forall c s,
        fm (CSnoc c s) -> 
        fm c.
  Scheme tm_rect' := Induction for tm Sort Type
    with tms_rect' := Induction for tms Sort Type
    with fm_rect' := Induction for fm Sort Type.
  Combined Scheme tm_tms_fm_rect from tm_rect', tms_rect', fm_rect'.

  Derive Signature NoConfusion Subterm for tm tms fm.
  Lemma subterm_wf:
    (forall c (s : sig_sorts sig) (t : tm c s),
        Acc tm_subterm {| pr1 := {| pr1 := c; pr2 := s |}; pr2 := t|}) *
    ((forall (c : ctx) (l : list (sig_sorts sig)) (t : tms c l), 
        Acc tms_subterm {| pr1 := {| pr1 := c; pr2 := l |}; pr2 := t|}) *
    (forall (c : ctx) (fg : fm c), Acc fm_subterm {| pr1 := c; pr2 := fg|})).
  Proof.
    pose (Ptm c s t := Acc tm_subterm {| pr1 := {| pr1 := c; pr2 := s |}; pr2 := t|}).
    pose (Ptms c l t := Acc tms_subterm {| pr1 := {| pr1 := c; pr2 := l |}; pr2 := t|}).
    pose (Pfm c fg := Acc fm_subterm {| pr1 := c; pr2 := fg|}).
    apply (tm_tms_fm_rect Ptm Ptms Pfm).
    - subst Ptm.
      intros.
      simpl.
      constructor.
      intros.
      assert (~ tm_subterm y {| pr1 := {| pr1 := c; pr2 := s |}; pr2 := TVar c s v |}).
      {
        repeat match goal with H: _ |- _ => clear H end.
        intro.
        induction H; tauto.
      }
      tauto.
    - subst Ptms Ptm.
      simpl.
      intros.
      constructor; intros.
      induction H0; tauto.
    - subst Ptms Ptm.
      simpl.
      intros.
      constructor.
      intros.
      assert (~ tms_subterm y {| pr1 := {| pr1 := c; pr2 := nil |}; pr2 := TSNil c |}).
      {
        repeat match goal with H: _ |- _ => clear H end.
        intro.
        remember ({| pr1 := {| pr1 := c; pr2 := nil |}; pr2 := TSNil c |}) as t.
        revert Heqt.
        induction H; intros; subst; simpl in *.
        - inversion H.
        - apply IHclos_trans2.
          tauto.
      }
      tauto.
    - subst Ptms Ptm.
      simpl.
      intros.
      constructor; intros.
      remember ({| pr1 := {| pr1 := c; pr2 := (s :: typs)%list |}; pr2 := TSCons c s typs t t0 |}) as t'.
      remember (TSCons c s typs t t0) as t0'.
      revert Heqt'.
      revert Heqt0'.
      revert t0'.
      destruct t' as [[c_ s_] t_].
      simpl in *.
      revert t t0 H H0.
      induction H1.
      + intros.
        subst. 
        simpl in *.
        destruct x as [[c' s'] t'].
        simpl in *.
        assert (Hcs: c' = c /\ s' = typs).
        {
          inversion H.
          subst.
          tauto.
        }
        destruct Hcs.
        subst c' s'.
        assert (t' = t0).
        {
          inversion H.
          subst.
          solve_existT.
          tauto.
        }
        subst t'.
        auto.
      + intros.
        subst.
        destruct x as [[c' s'] t'].
        destruct y as [[c'' s''] t''].
        simpl in *.
        constructor; intros.
        eapply IHclos_trans2; eauto.
        econstructor 2; eauto.
    - subst Ptm Pfm.
      intros.
      cbn in *.
      inversion H.
      inversion H0.
      constructor.
      intros.
      remember ({| pr1 := c; pr2 := FEq c s t t0 |}) as x.
      revert Heqx.
      induction H3; intros; subst; cbn in *.
      + inversion H3.
      + apply IHclos_trans2; eauto.
    - subst Ptms Pfm.
      intros; cbn in *.
      constructor; intros.
      remember ({| pr1 := c; pr2 := FRel c args s t |}) as x.
      revert Heqx.
      induction H0; intros; subst; cbn in *.
      + inversion H0.
      + apply IHclos_trans2; eauto.
    - subst Ptms Pfm.
      intros; cbn in *.
      constructor; intros.
      remember ({| pr1 := c; pr2 := FNeg c f |}) as x.
      revert Heqx.
      induction H0; intros; subst; cbn in *.
      + inversion H0.
        subst.
        solve_existT.
        auto.
      + apply IHclos_trans2; eauto.
    - subst Pfm.
      intros; cbn in *.
      constructor; intros.
      remember ({| pr1 := c; pr2 := FOr c f f0 |}) as x.
      revert Heqx.
      induction H1; intros; subst; cbn in *.
      + inversion H1; subst; solve_existT; auto.
      + apply IHclos_trans2; eauto.
    - subst Pfm.
      intros; cbn in *.
      constructor; intros.
      remember ({| pr1 := c; pr2 := FAnd c f f0 |}) as x.
      revert Heqx.
      induction H1; intros; subst; cbn in *.
      + inversion H1; subst; solve_existT; auto.
      + apply IHclos_trans2; eauto.
    - subst Pfm; intros; cbn in *.
      constructor; intros.
      remember ({| pr1 := c; pr2 := FForall c s f |}) as x.
      revert Heqx.
      induction H0; intros; subst; cbn in *.
      + destruct x.
        inversion H0; subst; solve_existT; auto.
      + apply IHclos_trans2; eauto.
  Qed.
  Next Obligation.
    apply subterm_wf.
  Qed.
  Next Obligation.
    apply subterm_wf.
  Qed.

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
    Derive Signature NoConfusion Subterm for valu.
    Next Obligation.
      constructor.
      intros.
      destruct y as [c y].
      induction c.
      - constructor; intros.
        dependent destruction y.
        remember {| pr1 := CEmp; pr2 := VEmp |} as y.
        revert Heqy.
        induction H0.
        + intros; subst.
          inversion H0.
        + intros; subst.
          apply IHclos_trans2; eauto.
      - dependent destruction y.
        constructor.
        intros.
        remember {| pr1 := CSnoc c s; pr2 := VSnoc s c m0 y |} as y'.
        revert Heqy'.
        induction H0.
        + intros; subst.
          destruct x; simpl in *.
          assert (pr1 = c).
          {
            inversion H0.
            solve_existT.
            auto.
          }
          subst.
          assert (pr2 = y).
          {
            inversion H0.
            solve_existT.
            auto.
          }
          subst.
          apply IHc.
          set (g := ({|pr1 := CSnoc c s; pr2 := VSnoc s c m0 y|})).
          change (CSnoc c s) with (pr1 g) in H0.
          change (VSnoc s c m0 y) with (pr2 g) in H0.
          econstructor 2.
          econstructor 1.
          simpl.
          eapply H0.
          eapply H.
        + intros.
          intuition eauto with *.
    Qed.

    Equations find {c s} (x: var c s) (v: valu c) : m.(mod_sorts) s :=
      { find (VHere _ _) (VSnoc _ _ val _) := val;
        find (VThere _ _ _ x') (VSnoc _ _ _ v') := find x' v' }.
    Derive NoConfusion Subterm for signature.

    Equations interp_fm (c: ctx) (v: valu c) (f: fm c) : Prop
      by struct f :=
      { interp_fm _ v (FRel c typs rel args) :=
          m.(mod_rels) typs rel (interp_tms c _ v args);
        interp_fm _ v (FEq c s t1 t2) :=
          interp_tm c s v t1 = interp_tm c s v t2;
        interp_fm _ v (FNeg _ f) :=
          ~ interp_fm _ v f;
        interp_fm _ v (FOr _ f1 f2) :=
          interp_fm _ v f1 \/ interp_fm _ v f2;
        interp_fm _ v (FAnd _ f1 f2) :=
          interp_fm _ v f1 /\ interp_fm _ v f2;
        interp_fm _ v (FForall c s f) :=
          forall val: m.(mod_sorts) s,
            interp_fm (CSnoc c s) (VSnoc _ _ val v) f }
    where interp_tm (c: ctx) (s: sig_sorts sig) (v: valu c) (t: tm c s) : m.(mod_sorts) s
      by struct t :=
      { interp_tm _ _ v (TVar c s x) :=
          find x v;
        interp_tm _ _ v (TFun c typs rets fn args) :=
          m.(mod_fns) typs rets fn (interp_tms _ _ v args) }
    where interp_tms (c: ctx) typs (v: valu c) (args: tms c typs) : HList.t m.(mod_sorts) typs
      by struct args :=
      { interp_tms _ _ _ (TSNil _) := HList.HNil _;
        interp_tms _ _ _ (TSCons _ _ _ tm args') :=
          @HList.HCons _ _ _ _ (interp_tm _ _ v tm) (interp_tms _ _ v args') }.
  End Interp.
End FOL.

Arguments TVar {_ _ _}.
Arguments TFun _ {_ _ _} _ _.
Arguments TSNil {_ _}.
Arguments TSCons {_ _ _ _} _ _.
Arguments FEq {_ _ _} _ _.
Arguments FRel {_ _} _ _.
Arguments FNeg {_} _.
Arguments FOr {_} _ _.
Arguments FAnd {_} _ _.
Arguments FForall {_ _} _.

Arguments interp_fm {_ _ _} _ _.
Arguments interp_tm {_ _ _ _} _ _.
Arguments interp_tms {_ _ _ _} _ _.
