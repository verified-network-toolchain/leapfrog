Require Import Coq.NArith.Nnat.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Poulet4.P4automata.FirstOrder.
Require Import Coq.Init.Specif.
Require Import Coq.micromega.Lia.
Require Import SMTCoq.SMTCoq.
Import BVList.BITVECTOR_LIST.
Require Import Coq.NArith.BinNat.

Section BitsBV.

  Inductive bv_sorts: Type :=
  | BVBits (len: {n: nat | n > 0})
  | BVBool.

  Definition pos := {n: nat | n > 0}.

  Program Definition plus (l: {n: nat | n > 0}) (r: {n: nat | n > 0}) : {n: nat | n > 0} := l + r.
  Next Obligation.
  lia.
  Defined.

  (* Definition gt (l: {n: nat | n > 0}) (r: {n: nat | n > 0})  := . *)

  Program Definition sub_add_one (i : nat) (j: nat) : (i >= j) -> {n: nat | n > 0} := fun pf => i - j + 1.
  Next Obligation.
  lia.
  Defined.

  Inductive bool_bop: Type :=
  | BImpl | BXor.

  Inductive bv_funs: arity bv_sorts -> bv_sorts -> Type :=
  | BoolLit: forall (b: bool), bv_funs [] BVBool
  | BVLit: forall (bv: list bool) (pf: List.length bv > 0), bv_funs [] (BVBits (exist _ (List.length bv) pf))
  | BoolBop: forall (bop: bool_bop), bv_funs [BVBool; BVBool] BVBool
  | BVConcat : forall i j, bv_funs [BVBits i; BVBits j] (BVBits (plus i j))
  | BVExtract : forall (i j: nat) (m n : {x: nat | x > 0}) (pf: i >= j),
    proj1_sig m > i ->
    n = sub_add_one _ _ pf  ->
    bv_funs [BVBits m] (BVBits n).

  Inductive bv_rels: arity bv_sorts -> Type := .

  Definition bv_sig : signature :=
    {| sig_sorts := bv_sorts; sig_funs := bv_funs; sig_rels := bv_rels |}.

  Definition bv_mod_sorts (sig: bv_sig.(sig_sorts)) : Type :=
    match sig with
    | BVBool => bool
    | BVBits n => bitvector (N_of_nat (proj1_sig n))
    end.

  (* inclusive slicing *)

  Definition slice {A} (hi lo: nat) (xs: list A) := firstn (hi - lo + 1) (skipn (lo - 1) xs).

  (* Compute (slice 3 2 (1::2::3::4::5::nil)). *)

  Lemma slice_len:
    forall A hi lo (xs : list A),
      List.length xs > hi ->
      hi >= lo ->
      List.length (slice hi lo xs) = hi - lo + 1.
  Proof.
    intros.
    induction hi; induction lo; simpl.
    - unfold slice.
      simpl.
      destruct xs; [exfalso; simpl in *; lia | simpl; trivial].
    - exfalso.
      inversion H0.
    - unfold slice.
      simpl (0 - 1).
      erewrite skipn_O.
      simpl (S hi - 0 + 1).
      erewrite firstn_length.

      eapply min_l.
      lia.

    - admit.
  Admitted.

  Notation "x ::: xs" := (HList.HCons _ x xs) (at level 60, right associativity).

  Definition bv_concat' {x y} (l: bv_mod_sorts (BVBits x)) (r: bv_mod_sorts (BVBits y)) : bv_mod_sorts (BVBits (plus x y)).
  unfold plus.
  simpl in *.
  erewrite Nat2N.inj_add.
  exact (bv_concat l r).
  Defined.


  Equations bv_mod_fns {args: arity (sig_sorts bv_sig)} {ret: sig_sorts bv_sig}
    (sf: bv_sig.(sig_funs) args ret)
    (env: HList.t bv_mod_sorts args) : bv_mod_sorts ret := {
      bv_mod_fns (BoolLit b) _ := b;
      bv_mod_fns (BVLit bv _) _ := of_bits bv;
      bv_mod_fns (BoolBop op) (l ::: r ::: _) :=
        match op with
        | BImpl => implb l r
        | BXor => xorb l r
        end;
      bv_mod_fns (@BVExtract hi lo n m _ _ _) (x ::: _) := _;
      bv_mod_fns (BVConcat _ _) (l ::: r ::: _) := bv_concat' l r
  }.
  Next Obligation.
  refine (@bv_extr (N.of_nat hi) _ _ x).
  Defined.

  Definition bv_mod_rels {args}
    (sig_args: bv_sig.(sig_rels) args)
    (env: HList.t bv_mod_sorts args) : Prop := False.

  Definition bv_model : model bv_sig.
  refine {| FirstOrder.mod_sorts := bv_mod_sorts;
       FirstOrder.mod_fns := _; FirstOrder.mod_rels := _ |}.

  - intros.
    exact (bv_mod_fns H X).
  - intros.
    exact (bv_mod_rels X X0).
  Defined.

  (* true = true *)

  Definition ex0 : FirstOrder.fm bv_sig (CEmp _).
  refine (FEq _ _).
  - refine (TFun _ _ _).
    * refine (BoolLit true).
    * constructor.
  - refine (TFun _ _ _).
    * refine (BoolLit true).
    * constructor.
  Defined.


  Lemma ex0_interp : interp_fm (m := bv_model) (VEmp _ _) ex0.
  Proof.
    unfold ex0.
    autorewrite with interp_fm bv_mod_fns.
    simpl.
    (*
    smt_uncheck; admit.
    *)
  Admitted.


  (* forall x, x -> x *)

  Definition ex1 : FirstOrder.fm bv_sig (CEmp _).
  refine (FForall _ (FEq _ _)).
  - refine (TFun _ _ _).
    * refine (BoolBop BImpl).
    * repeat constructor;  refine (TVar _ _ _ _); constructor.
  - refine (TFun _ _ _).
    * refine (BoolLit true).
    * constructor.
  Defined.

  Lemma ex1_interp : interp_fm (m := bv_model) (VEmp _ _) ex1.
  Proof.
    unfold ex1.
    autorewrite with interp_fm.
    intros.
    autorewrite with interp_fm bv_mod_fns find.
    simpl in *. (* we need this to reduce the hypothesis' type to bool, otherwise smtcoq breaks*)
    (*
    smt_uncheck; admit.
    *)
    (* confusingly, vm_compute reduces to an if-then-else, which is not recognized by smtcoq *)
  Admitted.

  (* forall a b c, (a -> b) -> (b -> c) -> (a -> c) *)

  (* Definition ex2 : fm bv_sig (CEmp _).
  refine (
    FForall _ (CEmp _) _ _
  ).
  refine (
    FForall _ _ _ _
  ).
  refine (
    FForall _ _ _ _
  ).
  refine (
    FEq _ _ _ _ _
  ).
  - refine (TFun _ _ _ _ _ _).
    * refine (BoolBop BImpl).
    * constructor.
      + refine (TFun _ _ _ _ _ _).

  - refine (TFun _ _ _ _ _ _).
    * refine (BoolLit true).
    * constructor.
  Defined. *)

End BitsBV.
