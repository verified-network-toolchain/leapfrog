Require Import Equations.Equations.

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
  Admitted.

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
  Next Obligation.
    destruct a.
    pose (Ptm c s t := Acc tm_subterm {| pr1 := {| pr1 := c; pr2 := s |}; pr2 := t|}).
    pose (Ptms c s ts := Acc tms_subterm {| pr1 := {| pr1 := c; pr2 := s |}; pr2 := ts|}).
    pose (Pfm c f := Acc fm_subterm {| pr1 := c; pr2 := f|}).
    pose proof (tm_tms_fm_rect Ptm Ptms Pfm).
    apply H.
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
      induction H1; tauto.
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
      revert Heqt'.
      revert t t0 H0 H1.
      induction H2.
      + intros.
        subst. 
        simpl in *.
        destruct x as [[c' s'] t'].
        simpl in *.
        assert (Hcs: c' = c /\ s' = typs).
        {
          inversion H0.
          subst.
          tauto.
        }
        destruct Hcs.
        subst c' s'.
        assert (t' = t0).
        {
          inversion H0.
          subst.
          repeat match goal with
                 | H: ?X = ?X |- _ => clear H
                 | H: existT _ _ _ = existT _ _ _ |- _ =>
                   eapply Eqdep.EqdepTheory.inj_pair2 in H; subst
                 end.
          tauto.
        }
        subst t'.
        auto.
      + admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.
  Next Obligation.
  Admitted.

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
    Admitted.

    Equations find {c s} (x: var c s) (v: valu c) : m.(mod_sorts) s :=
      { find (VHere _ _) (VSnoc _ _ val _) := val;
        find (VThere _ _ _ x') (VSnoc _ _ _ v') := find x' v' }.
    Derive NoConfusion Subterm for signature.

    Equations interp_fm (c: ctx) (v: valu c) (f: fm c) : Prop
      by struct f :=
      { interp_fm _ v (FRel c typs rel args) :=
          m.(mod_rels) typs rel (interp_tms c v _ args);
        interp_fm _ v (FEq c s t1 t2) :=
          interp_tm c v s t1 = interp_tm c v s t2;
        interp_fm _ v (FNeg _ f) :=
          ~ interp_fm _ v f;
        interp_fm _ v (FOr _ f1 f2) :=
          interp_fm _ v f1 \/ interp_fm _ v f2;
        interp_fm _ v (FAnd _ f1 f2) :=
          interp_fm _ v f1 /\ interp_fm _ v f2;
        interp_fm _ v (FForall c s f) :=
          forall val: m.(mod_sorts) s,
            interp_fm (CSnoc c s) (VSnoc _ _ val v) f }
    where interp_tm (c: ctx) (v: valu c) s (t: tm c s) : m.(mod_sorts) s
      by struct t :=
      { interp_tm _ v _ (TVar c s x) :=
          find x v;
        interp_tm _ v _ (TFun c typs rets fn args) :=
          m.(mod_fns) typs rets fn (interp_tms _ v _ args) }
    where interp_tms (c: ctx) (v: valu c) typs (args: tms c typs) : HList.t m.(mod_sorts) typs
      by struct args :=
      { interp_tms _ _ _ (TSNil _) := HList.HNil _;
        interp_tms _ _ _ (TSCons _ _ _ tm args') :=
          @HList.HCons _ _ _ _ (interp_tm _ v _ tm) (interp_tms _ v _ args') }.
  End Interp.
End FOL.
