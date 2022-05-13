From Equations Require Import Equations.
Require Import Coq.Program.Equality.

Require Import Leapfrog.FinType.
Require Import Leapfrog.ConfRel.
Require Import Leapfrog.P4automaton.
Require Import Leapfrog.FirstOrderBitVec.
Require Import Leapfrog.Ntuple.
Require Import MirrorSolve.FirstOrder.
Require Import MirrorSolve.HLists.
Import HListNotations.

Require Import MirrorSolve.BV.

Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.

Set Universe Polymorphism.

Require Import SMTCoq.SMTCoq.

Import BVList.BITVECTOR_LIST.

Section CompileBitVec.

  Definition conv_sort (bvs: FirstOrderBitVec.sorts) : BV.sorts :=
    match bvs with 
    | Bits n => @BV (N.of_nat n)
    end.

  Definition conv_arr := @fmap_arity FirstOrderBitVec.sig BV.sig conv_sort.

  (* pulled from Clement Pit-Claudel's blog: https://plv.csail.mit.edu/blog/computing-with-opaque-proofs.html#computing-with-opaque-proofs *)
  Definition comp_eq_N {m n: N} (opaque_eq: m = n) : m = n :=
    match N.eq_dec m n with
    | left transparent_eq => transparent_eq
    | right _ => opaque_eq
    end.

  Definition comp_eq_nat {m n: nat} (opaque_eq: m = n) : m = n :=
    match PeanoNat.Nat.eq_dec m n with
    | left transparent_eq => transparent_eq
    | right _ => opaque_eq
    end.
  

  Definition trans_inj_add : forall n n' : nat, N.of_nat (n + n') = (N.of_nat n + N.of_nat n')%N 
    := fun n n' => comp_eq_N (Nat2N.inj_add n n').

  Definition trans_inj_sub : forall n n' : nat, N.of_nat (n - n') = (N.of_nat n - N.of_nat n')%N 
    := fun n n' => comp_eq_N (Nat2N.inj_sub n n').

  Definition trans_inj_min : forall n n' : nat, N.of_nat (PeanoNat.Nat.min n n') = N.min (N.of_nat n) (N.of_nat n')
    := fun n n' => comp_eq_N (Nat2N.inj_min n n').

  Definition trans_t2l_len : forall {A: Type} (n : nat) (x : n_tuple A n), length (t2l x) = n := 
    fun _ n x => comp_eq_nat (t2l_len n x).

  (* use t2l to convert bs to a list and cast the length of t2l to w *)
  Definition conv_n_tuple (w: nat) (bs: n_tuple bool w) : bitvector (N.of_nat w) :=
    eq_rect _ (fun n => bitvector (N.of_nat n)) (of_bits (t2l bs)) _ (trans_t2l_len _ bs).


  Local Obligation Tactic := intros.
  Equations conv_fun {arr : arity (sig_sorts FirstOrderBitVec.sig)} {srt: sig_sorts FirstOrderBitVec.sig} (nf: sig_funs FirstOrderBitVec.sig arr srt) : sig_funs sig (conv_arr arr) (conv_sort srt) :=
  {
    conv_fun (BitsLit w bs) := BVLit (N.of_nat w) (conv_n_tuple _ bs);
    conv_fun (Concat n m) := eq_rect_r (fun n' => funs _ (BV n')) (BVCat (N.of_nat n) (N.of_nat m)) (Nat2N.inj_add n m);
    conv_fun (Slice n hi lo) := 
      let r := BVExtr (N.of_nat n) (N.of_nat hi) (N.of_nat lo) in 
        _;
  }.
 Next Obligation.
  unfold sig_funs, conv_arr, conv_sort.
  Opaque Nat.min.
  Opaque Nat.add.
  Opaque Nat.sub.
  simpl.
  change Nat.min with PeanoNat.Nat.min.
  change 1%N with (N.of_nat 1) in r.
  erewrite <- trans_inj_add in r.
  erewrite <- trans_inj_min in r.
  erewrite <- trans_inj_sub in r.
  exact r.
 Defined.

 Transparent conv_fun_obligations_obligation_1.

  Definition conv_rel {arr } (r: sig_rels FirstOrderBitVec.sig arr) : sig_rels sig (conv_arr arr) := 
    match r with end.

  Equations conv_mv {srt} (v: FirstOrderBitVec.mod_sorts srt) : BV.mod_sorts (conv_sort srt) := 
  {
    @conv_mv (Bits n) bv := conv_n_tuple _ bv;
  }.

  Program Definition conv_functor : @theory_functor FirstOrderBitVec.sig BV.sig FirstOrderBitVec.fm_model BV.fm_model := {|
    fmap_sorts := @conv_sort;
    fmap_funs := @conv_fun;
    fmap_rels := @conv_rel;
    fmap_mv := @conv_mv;
  |}.

  (* Notation fmap_ctx := (@fmap_ctx n2z_func). *)

  Notation fmap_ctx' := (fmap_ctx _ _ _ _ conv_functor).

  Local Obligation Tactic := unfold conv_sort in *; intros; simpl in *.
  Equations conv_fun_arrs {c arr srt} 
    (f: FirstOrderBitVec.funs arr srt) 
    (args: HList.t (fun srt' : FirstOrderBitVec.sorts => FirstOrder.tm sig (fmap_ctx' c) (conv_sort srt')) arr) : 
    HList.t (FirstOrder.tm sig (fmap_ctx' c)) (conv_arr arr) := 
  {
    conv_fun_arrs (BitsLit w bs) _ := hnil;
    conv_fun_arrs (Concat n m) (x ::: y ::: _) := _;
    conv_fun_arrs (Slice n hi lo) (x ::: _) := _;
  }.
  Next Obligation.
  exact (x ::: y ::: hnil).
  Defined.
  Next Obligation.
  exact (x ::: hnil).
  Defined.

  Transparent conv_fun_arrs.

  Definition conv_rel_arrs {c arr} (rel: FirstOrderBitVec.rels arr) (args: HList.t (fun srt' : FirstOrderBitVec.sorts => FirstOrder.tm sig (fmap_ctx' c) (conv_sort srt')) arr) 
    : HList.t (FirstOrder.tm sig (fmap_ctx' c)) (conv_arr arr) := 
  match rel with end.

  Program Definition conv_forall_op {c} {srt: sig_sorts FirstOrderBitVec.sig} (f: FirstOrder.fm sig (fmap_ctx' (Snoc _ c srt))) : FirstOrder.fm sig (fmap_ctx' (Snoc _ c srt)) := f.

  Program Definition conv_wf : functor_wf _ _ _ _ conv_functor (@conv_fun_arrs) (@conv_rel_arrs) (@conv_forall_op) := {|
    interp_tm_inj := _;
    fmap_rel_equi := ltac:(intros; inversion r);
    interp_fmap_forall_equi := _;
  |}.
  Next Obligation.
  Admitted.
  Next Obligation.
  unfold conv_forall_op.
  simpl.
  dependent induction f; 
  try now ( 
    split; intros; autorewrite with interp_fm in *; trivial
  ).
  Admitted.

  Lemma conv_corr: 
    forall (c : ctx FirstOrderBitVec.sig) (v : valu FirstOrderBitVec.sig FirstOrderBitVec.fm_model c) (f : FirstOrder.fm FirstOrderBitVec.sig c),
      interp_fm v f <->
      interp_fm (fmap_valu FirstOrderBitVec.sig sig FirstOrderBitVec.fm_model fm_model conv_functor v)
        (fmap_fm FirstOrderBitVec.sig sig FirstOrderBitVec.fm_model fm_model conv_functor 
            (@conv_fun_arrs) (@conv_rel_arrs) (@conv_forall_op) f).
  Proof.
    eapply fmap_corr.
    eapply conv_wf.
  Qed.

End CompileBitVec.
