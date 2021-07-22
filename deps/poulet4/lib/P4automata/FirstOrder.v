Require Import Equations.Equations.
Require Import Poulet4.P4automata.PreBisimulationSyntax.

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
  Parameter sig: signature.

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

    Equations find {c s} (x: var c s) (v: valu c) : m.(mod_sorts) s :=
      { find (VHere _ _) (VSnoc _ _ val _) := val;
        find (VThere _ _ _ x') (VSnoc _ _ _ v') := find x' v' }.
    Derive Signature NoConfusion Subterm for var.
    Derive NoConfusion Subterm for signature.

    Fail Equations interp_fm (c: ctx) (v: valu c) (f: fm c) : Prop :=
      { interp_fm _ v (FRel c typs rel args) :=
          m.(mod_rels) typs rel (interp_tms c v _ args);
        interp_fm _ v (FNeg _ f) :=
          ~ interp_fm _ v f;
        interp_fm _ v (FOr _ f1 f2) :=
          interp_fm _ v f1 \/ interp_fm _ v f2;
        interp_fm _ v (FAnd _ f1 f2) :=
          interp_fm _ v f1 /\ interp_fm _ v f2;
        interp_fm _ v (FForall c s f) :=
          forall val: m.(mod_sorts) s,
            interp_fm (CSnoc c s) (VSnoc _ _ val v) f }
    where interp_tm (c: ctx) (v: valu c) s (t: tm c s) : m.(mod_sorts) s :=
      { interp_tm _ v _ (TVar c s x) :=
          find x v;
        interp_tm _ v _ (TFun c typs rets fn args) :=
          m.(mod_fns) typs rets fn (interp_tms _ v _ args) }
    where interp_tms (c: ctx) (v: valu c) typs (args: tms c typs) : HList.t m.(mod_sorts) typs :=
      {
        interp_tms _ _ _ (TSNil _) := HList.HNil _;
        interp_tms _ _ _ (TSCons _ _ _ tm args') :=
          @HList.HCons _ _ _ _ (interp_tm _ v _ tm) (interp_tms _ v _ args') }.

End FOL.
