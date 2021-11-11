From Equations Require Import Equations.

Require Import Coq.Classes.EquivDec.

Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4automata.Ntuple.
Require Import Poulet4.P4automata.FirstOrder.
Import HListNotations.

Require Poulet4.P4automata.FirstOrderConfRelSimplified.
Require Poulet4.P4automata.FirstOrderBitVec.

Require Import Coq.Program.Equality.
Module FOS := FirstOrderConfRelSimplified.
Module FOBV := FirstOrderBitVec.

Section CompileFirstOrderConfRelSimplified.
  Set Implicit Arguments.
  (* State identifiers. *)
  Variable (S: Type).
  Context `{S_eq_dec: EquivDec.EqDec S eq}.
  Context `{S_finite: @Finite S _ S_eq_dec}.

  (* Header identifiers. *)
  Variable (H: nat -> Type).
  Context `{H_eq_dec: forall n, EquivDec.EqDec (H n) eq}.
  Context `{H'_eq_dec: EquivDec.EqDec (P4A.H' H) eq}.
  Context `{H_finite: @Finite (Syntax.H' H) _ H'_eq_dec}.

  Variable (a: P4A.t S H).

  Equations compile_store_ctx_partial
    (hdrs: list (Syntax.H' H))
    : ctx FOBV.sig
  := {
    compile_store_ctx_partial nil := CEmp _;
    compile_store_ctx_partial (hdr :: hdrs) :=
      CSnoc _ (compile_store_ctx_partial hdrs) (FOBV.Bits (projT1 hdr))
  }.

  (* TODO: make this a normal fixpoint or equations definition *)
  Definition compile_store_valu_partial
    (hdrs: list (Syntax.H' H))
    : (HList.t (fun x => (n_tuple bool (projT1 x))) hdrs)
    -> valu FOBV.sig FOBV.fm_model (compile_store_ctx_partial hdrs).
  refine ((
    fix recur hdrs :=
      match hdrs with 
      | nil => fun _ => _
      | hdr :: hdrs => fun vs => 
        _
      end 
  ) hdrs).
  - exact (VEmp _ _).
  - inversion vs.
    refine (VSnoc _ _ _ _ _ _).
    + exact X.
    + eapply recur. exact X0.
  Defined.

  Definition compile_store_ctx : ctx FOBV.sig :=
    compile_store_ctx_partial (enum (Syntax.H' H)).

  Equations compile_ctx (c: ctx (FOS.sig H)) : ctx FOBV.sig := {
    compile_ctx (CEmp _) := CEmp _;
    compile_ctx (CSnoc _ c FOS.Store) :=
      app_ctx (compile_ctx c) compile_store_ctx;
    compile_ctx (CSnoc _ c (FOS.Bits n)) :=
      CSnoc _ (compile_ctx c) (FOBV.Bits n)
  }.

  Equations build_hlist_env 
    (hdrs: list (Syntax.H' H))
    (env: P4A.store H)
    : (HList.t (fun x => (n_tuple bool (projT1 x))) hdrs) := {
      build_hlist_env nil _ := hnil;
      build_hlist_env (hdr :: hdrs) env := 
        _ ::: (build_hlist_env hdrs) env
    }.
  Next Obligation.
  exact (
    match P4A.find H (projT2 hdr) env with 
    | P4A.VBits _ v => v 
    end
  ).
  Defined.

  Equations compile_valu 
    {c: ctx (FOS.sig H)} 
    (v: valu (FOS.sig H) (FOS.fm_model a) c) 
    : valu FOBV.sig FOBV.fm_model (compile_ctx c) := {
    compile_valu (VEmp _ _) := VEmp _ _;
    compile_valu (VSnoc _ _ (FOS.Bits n) _ v vinner) := 
      VSnoc _ FOBV.fm_model (FOBV.Bits n) _ v (compile_valu vinner);
    compile_valu (VSnoc _ _ (FOS.Store) _ v vinner) := 
      app_valu _ (compile_valu vinner) (compile_store_valu_partial (build_hlist_env _ _))
  }.
  Next Obligation.
  Defined.

  Lemma here_or_there
    {X: Type}
    `{EquivDec.EqDec X eq}
    (x x': X)
    (l: list X)
    (Hin: List.In x (x' :: l))
  :
    {x' = x} + {List.In x l}.
  Proof.
    destruct (equiv_dec x' x).
    - left.
      exact e.
    - right.
      destruct Hin.
      + contradiction.
      + exact H1.
  Defined.

  Equations compile_lookup'
    (k: Syntax.H' H)
    (enum: list (Syntax.H' H))
    (elem_of_enum: List.In k enum)
    : var (FOBV.sig) (compile_store_ctx_partial enum)
          (FOBV.Bits (projT1 k)) := {
    compile_lookup' k (elem :: enum) elem_of_enum :=
      match here_or_there elem_of_enum with
      | left Heq => eq_rec_r _ (fun _ =>
          VHere _ (compile_store_ctx_partial enum) (FOBV.Bits (projT1 k))
        ) Heq elem_of_enum
      | right Helse => VThere FOBV.sig _ (FOBV.Bits (projT1 elem))
                              _ (compile_lookup' k enum Helse)
      end
  }.

  Definition compile_lookup (k: Syntax.H' H)
    : var FOBV.sig compile_store_ctx (FOBV.Bits (projT1 k))
  :=
    compile_lookup' k (enum (Syntax.H' H)) (elem_of_enum k).

  Equations tm_cons {c s' s}
    (t: tm FOBV.sig c s)
    : tm FOBV.sig (CSnoc _ c s') s := {
    tm_cons (TVar v) := TVar (VThere _ _ _ _ v);
    tm_cons (TFun _ fn args) := TFun _ fn (tms_cons args)
  } where tms_cons {c s' s}
    (ts: HList.t (tm FOBV.sig c) s)
    : HList.t (tm FOBV.sig (CSnoc _ c s')) s := {
    tms_cons hnil := hnil;
    tms_cons (t ::: ts) := tm_cons t ::: tms_cons ts
  }.

  Definition compile_sizes (enum: list (Syntax.H' H)): nat :=
    let sizes := List.map (@projT1 nat H) enum in
    (* let sizes' := List.filter (fun n => (0 <? n)%nat) sizes in  *)
    List.fold_right Nat.add 0 sizes.

  Definition compile_sort (s: FOS.sorts) : FOBV.sorts :=
    match s with
    | FOS.Bits n => FOBV.Bits n
    | FOS.Store => FOBV.Bits (compile_sizes (enum (Syntax.H' H)))
    end.

  Equations compile_store'
    (enum: list (Syntax.H' H))
    : tm FOBV.sig (compile_store_ctx_partial enum)
                  (FOBV.Bits (compile_sizes enum)) := {
    compile_store' nil := TFun FOBV.sig (FOBV.BitsLit 0 tt) hnil;
    compile_store' (elem :: enum) :=
      TFun FOBV.sig (FOBV.Concat (projT1 elem) (compile_sizes enum))
                    (TVar (VHere _ _ _) :::
                     tm_cons (compile_store' enum) ::: hnil)
  }.

  Definition compile_store
    : tm (FOBV.sig) compile_store_ctx (compile_sort FOS.Store)
  :=
    compile_store' (enum (Syntax.H' H)).

  Equations subscript {c n}
    (v: var (FOS.sig H) c FOS.Store)
    (v': var FOBV.sig compile_store_ctx (FOBV.Bits n))
    : var FOBV.sig (compile_ctx c) (FOBV.Bits n)
  := {
    subscript (VHere c' _) v' :=
      reindex_var v';
    subscript (VThere _ c (FOS.Bits n) _ v) v' :=
      VThere _ _ _ _ (subscript v v');
    subscript (VThere _ c FOS.Store _ v) v' :=
      weaken_var _ (subscript v v')
  }.

  Equations compile_var
    {c: ctx (FOS.sig H)}
    {s: FOS.sorts}
    (v: var (FOS.sig H) c s)
    : tm FOBV.sig (compile_ctx c) (compile_sort s)
  := {
    compile_var (VHere _ c (FOS.Bits n)) :=
      TVar (VHere _ (compile_ctx c) (FOBV.Bits n));
    compile_var (VHere _ c FOS.Store) := reindex_tm compile_store;
    compile_var (VThere _ c (FOS.Bits _) s' v) := tm_cons (compile_var v);
    compile_var (VThere _ c FOS.Store s' v) := weaken_tm _ (compile_var v)
  }.

  Equations compile_tm
    {c: ctx (FOS.sig H)}
    {s: FOS.sorts}
    (t: tm (FOS.sig H) c s):
    tm FOBV.sig (compile_ctx c) (compile_sort s) := {
    compile_tm (TVar v) := compile_var v;
    compile_tm (TFun _ (FOS.BitsLit _ n v) hnil) :=
      TFun FOBV.sig (FOBV.BitsLit n v) hnil;
    compile_tm (TFun _ (FOS.Concat _ n m) (t1 ::: t2 ::: hnil)) :=
      TFun FOBV.sig (FOBV.Concat n m)
                    (compile_tm t1 ::: compile_tm t2 ::: hnil);
    compile_tm (TFun _ (FOS.Slice _ n hi lo) (t ::: hnil)) :=
      TFun FOBV.sig (FOBV.Slice n hi lo) (compile_tm t ::: hnil);
    compile_tm (TFun _ (FOS.Lookup n h) (TVar v ::: hnil)) :=
      TVar (subscript v (compile_lookup (existT H n h)))
  }.

  Equations compile_fm
    {c: ctx (FOS.sig H)}
    (f: fm (FOS.sig H) c)
    : fm FOBV.sig (compile_ctx c) := {
    compile_fm FTrue := FTrue;
    compile_fm FFalse := FFalse;
    compile_fm (FEq t1 t2) := FEq (compile_tm t1) (compile_tm t2);
    compile_fm (FNeg f) := FNeg _ (compile_fm f);
    compile_fm (FOr f1 f2) := FOr _ (compile_fm f1) (compile_fm f2);
    compile_fm (FAnd f1 f2) := FAnd _ (compile_fm f1) (compile_fm f2);
    compile_fm (FImpl f1 f2) := FImpl (compile_fm f1) (compile_fm f2);
    compile_fm (@FForall _ c (FOS.Bits n) f) :=
      FForall (sig := FOBV.sig) (FOBV.Bits n) (compile_fm f);
    compile_fm (@FForall _ c FOS.Store f) :=
      quantify compile_store_ctx (compile_fm f)
  }.

  

  

  Lemma compile_simplified_fm_bv_correct:
      forall c v (fm : fm _ c),
        interp_fm (m := FOS.fm_model a) v fm <->
        interp_fm (m := FOBV.fm_model) (compile_valu v) (compile_fm (c := c) fm)
        .
  Proof.
    intros.
    dependent induction fm;
    autorewrite with compile_fm;
    autorewrite with interp_fm;
    try now (split; intros; trivial).
    
    - dependent destruction t; dependent destruction t0;
      autorewrite with compile_tm;
      dependent induction v;
      try (now inversion v0).
      + dependent destruction v0;
        dependent destruction v1;
        split; intros H''; try (now inversion H'').
        autorewrite with interp_tm in H''.
        autorewrite with compile_valu.
  Admitted.
End CompileFirstOrderConfRelSimplified.

Register FOBV.Bits as p4a.sorts.bits.

Register FOBV.BitsLit as p4a.funs.bitslit.
Register FOBV.Concat as p4a.funs.concat.
Register FOBV.Slice as p4a.funs.slice.