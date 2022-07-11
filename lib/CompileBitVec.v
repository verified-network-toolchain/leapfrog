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
Require Import Coq.Lists.List.
Import ListNotations.

Section CompileBitVec.

  Definition conv_sort (bvs: FirstOrderBitVec.sorts) : BV.sorts :=
    match bvs with 
    | Bits n => @BV (N.of_nat n)
    end.

  Definition conv_arr := @fmap_arity FirstOrderBitVec.sig BV.sig conv_sort.

  (* Inspired by Clement Pit-Claudel's blog post: https://plv.csail.mit.edu/blog/computing-with-opaque-proofs.html#computing-with-opaque-proofs *)
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

  Lemma conv_n_tuple_succ : 
    forall n b (bs : n_tuple bool n) bs',
      bs' ~= (bs, b) ->
      conv_n_tuple (S n) bs' ~= 
      bv_concat (m := 1%N) (conv_n_tuple n bs) (conv_n_tuple 1%nat (tt, b)).
  Admitted.

  (* Lemma conv_n_tuple_succ :
    forall n b bs,
      conv_n_tuple (S n) (b, bs) ~=  *)

  Definition conv_bitvector {n} (x: bitvector n) : n_tuple bool (N.to_nat n) :=
    eq_rect _ _ (l2t (bits x)) _ (comp_eq_nat (bits_size x)).
  
  Require Import Coq.PArith.Pnat.


  Lemma mk_bv: 
    forall n m bv bv' pf pf', 
      n ~= m ->
      bv ~= bv' -> 
      pf ~= pf' -> 
      @MkBitvector n bv pf ~= @MkBitvector m bv' pf'.
  Proof.
    intros.
    subst.
    trivial.
  Qed.

  Lemma bv_concat_bit:
    forall bv bv' b b',
      bv = bv' -> 
      b = b' -> 
        BVList.RAWBITVECTOR_LIST.bv_concat bv
          (BVList.RAWBITVECTOR_LIST.of_bits [b]) = b' :: bv'.
  Proof.
    intros.
    subst.
    exact eq_refl.
  Qed.

  Lemma conv_bv_inv : 
    forall {n n' n'' b b' bv} {bits : n_tuple bool n} pf pf',
      (bits, b) ~= conv_bitvector (n := n') {| bv := b' :: bv; wf := pf |} ->
      b = b' /\ 
      bits ~= conv_bitvector (n := n'') {| bv := bv; wf := pf' |}.
  Admitted.

  Lemma bv_size_cons:
    forall b bv n, 
      BVList.RAWBITVECTOR_LIST.size (b :: bv) =
        N.pos (BinPos.Pos.of_succ_nat n) -> 
      BVList.RAWBITVECTOR_LIST.size bv = N.of_nat n.
  Proof.
    intros.
    unfold BVList.RAWBITVECTOR_LIST.size in *.
    simpl length in *.
    Lia.lia.
  Qed.

  Lemma conv_tupl_rt : 
    forall n v, 
      (conv_n_tuple n
        (eq_rect (N.to_nat (N.of_nat n)) (n_tuple bool)
          (conv_bitvector v) n (Nat2N.id n))) = v.
  Proof.
    intros.
    remember (conv_bitvector v) as w.
    assert (forall w',
               w' ~= w ->
               conv_n_tuple n w' ~= v) by shelve.
    clear Heqw.
    revert H.
    revert w.
    revert v.
    generalize dependent (Nat2N.id n).
    generalize (N.to_nat (N.of_nat n)).
    intros n0 e.
    rewrite e.
    simpl.
    intros.
    erewrite H; trivial.
    Unshelve.
    rewrite Heqw.
    intros.
    clear Heqw.
    clear w.
    induction n; intros; simpl in *.
    - vm_compute.
      destruct v.
      destruct bv0.
      * erewrite (ProofIrrelevance.proof_irrelevance _ _ wf0).
        trivial.
      * exfalso.
        inversion wf0.
    - destruct v.
      destruct bv0.
      * exfalso. admit.
      * destruct w'.

        assert (BVList.RAWBITVECTOR_LIST.size bv0 = N.of_nat n) by (eapply bv_size_cons; trivial).
        destruct (conv_bv_inv wf0 H0 H) as [? ?].
        subst.
      
        pose proof conv_n_tuple_succ.
        evar (n': nat).
        evar (b': bool).
        evar (bs': n_tuple bool n').
        specialize (H1 n' b' bs');
        subst b';
        subst bs';
        subst n';
        match goal with 
        | |- conv_n_tuple _ ?X ~= _ => 
          specialize (H1 X)
        end.
        clear H.
        simpl in *.
        erewrite H1; trivial.
        
        simpl in *.
        assert (@eq BVList.RAWBITVECTOR_LIST.bitvector
        (@bv (N.of_nat n) (conv_n_tuple n n0)) bv0) by (
          erewrite IHn; eauto; trivial
        ).
        eapply mk_bv;
        try now (subst; trivial).
        -- admit.
        -- simpl.
           assert ((N.add (N.of_nat n) (Npos xH)) = (Npos (BinPos.Pos.of_succ_nat n)))%N by Lia.lia.
           revert wf0.
           erewrite <- H.
           intros.
           match goal with 
           | |- ?X ~= _ => 
            generalize X
           end.
           match goal with 
           | |- forall _ : _ ?X = _, _ => 
            assert (X = (b :: (conv_n_tuple n n0 : BVList.RAWBITVECTOR_LIST.bitvector))) by (
              eapply bv_concat_bit; trivial
            )
           end.
           revert wf0.
           simpl in *.
           erewrite H3.
           intros.
           erewrite ProofIrrelevance.proof_irrelevance;
           trivial.

           Unshelve.
           exact b0.
  Admitted.

  Lemma conv_tuple_bitvector_rt : 
    forall n' n (bs: bitvector n) bits,
      n' = N.to_nat n ->
      conv_bitvector bs ~= bits ->
      conv_n_tuple n' bits ~= bs.
  Proof.
  Admitted.
    (* dependent induction n'.
    - intros; simpl in *;
      assert (n = 0%N) by Lia.lia.
      subst.
      destruct bits0.
      unfold conv_n_tuple.
      simpl.
      destruct bs.
      unfold of_bits.
      compute.
      destruct bv0.
      + erewrite (ProofIrrelevance.proof_irrelevance _ _ wf0).
        eapply JMeq_refl.
      + exfalso.
        inversion wf0.
    - intros.
      destruct bits0.
      simpl.
      assert (exists n'', n = (n'' + 1)%N) by admit.
      destruct H0.
      subst.
      destruct bs.
      destruct bv0.
      * exfalso.
        simpl in *.
        destruct x; simpl in *; inversion wf0.
      * pose proof conv_n_tuple_succ.
        specialize (H0 n' b n0).
        simpl in H0.
        erewrite H0.
        simpl.
        unfold conv_n_tuple at 2.
        simpl.
        unfold bv_concat.
        simpl.
        simpl in *.
        erewrite IHn' with (bs := (conv_n_tuple n' n0)).
        unfold conv_n_tuple.
        simpl.
        fold conv_n_tuple. *)


  Lemma conv_bitvector_tuple_rt : 
    forall (n n' : nat) bits,
      n ~= n' ->
      conv_bitvector (conv_n_tuple n' bits) ~= bits.
  Admitted.

  Local Obligation Tactic := intros.
  Equations conv_fun {arr : arity (sig_sorts FirstOrderBitVec.sig)} {srt: sig_sorts FirstOrderBitVec.sig} (nf: sig_funs FirstOrderBitVec.sig arr srt) : sig_funs sig (conv_arr arr) (conv_sort srt) :=
  {
    conv_fun (BitsLit w bs) := BVLit (N.of_nat w) (conv_n_tuple _ bs);
    conv_fun (Concat n m) := eq_rect_r (fun n' => funs _ (BV n')) (BVCat (N.of_nat n) (N.of_nat m)) (trans_inj_add n m);
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

  Definition conv_mv {srt} (v: FirstOrderBitVec.mod_sorts srt) : BV.mod_sorts (conv_sort srt) := 
    match srt as srt' return FirstOrderBitVec.mod_sorts srt' -> BV.mod_sorts (conv_sort srt') with 
    | Bits n => fun v' => conv_n_tuple _ v'
    end v.

  (* Unfortunately this does not typecheck *)
  (* Lemma conv_mv_bitvector: 
    forall {n} bv, 
      @conv_mv (Bits n) (conv_bitvector bv) = bv.  *)

  

  Require Import Coq.PArith.Pnat.

  Lemma conv_mv_bitvector: 
    forall {n} bs bs' bv, 
      @conv_mv (Bits n) bs = bv -> 
      conv_bitvector bv = bs' -> 
      bs ~= bs'.
  Proof.
    induction n; intros; simpl in *.
    - destruct bs, bs'; eapply JMeq_refl.
    - admit.
      (* destruct bs.
      subst.
      unfold conv_n_tuple.
      erewrite SuccNat2Pos.id_succ in bs'. *)
  Admitted.


  Program Definition conv_functor : @theory_functor FirstOrderBitVec.sig BV.sig FirstOrderBitVec.fm_model BV.fm_model := {|
    fmap_sorts := @conv_sort;
    fmap_funs := @conv_fun;
    fmap_rels := @conv_rel;
    fmap_mv := @conv_mv;
  |}.

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


  Definition conv_rel_arrs {c arr} (rel: FirstOrderBitVec.rels arr) (args: HList.t (fun srt' : FirstOrderBitVec.sorts => FirstOrder.tm sig (fmap_ctx' c) (conv_sort srt')) arr) 
    : HList.t (FirstOrder.tm sig (fmap_ctx' c)) (conv_arr arr) := 
  match rel with end.

  Program Definition conv_forall_op {c} {srt: sig_sorts FirstOrderBitVec.sig} (f: FirstOrder.fm sig (fmap_ctx' (Snoc _ c srt))) : FirstOrder.fm sig (fmap_ctx' (Snoc _ c srt)) := f.

  Lemma fmap_tm_inj: 
    forall {srt c} {v: valu _ _ c} 
      (t t': FirstOrder.tm FirstOrderBitVec.sig c srt), 
      interp_tm v t = interp_tm v t' <-> 
      interp_tm
        (fmap_valu
          FirstOrderBitVec.sig
          sig
          FirstOrderBitVec.fm_model
          fm_model
          conv_functor v)
        (fmap_tm
          FirstOrderBitVec.sig
          sig
          FirstOrderBitVec.fm_model
          fm_model
          conv_functor
          (@conv_fun_arrs) t) =
      interp_tm
        (fmap_valu
          FirstOrderBitVec.sig
          sig
          FirstOrderBitVec.fm_model
          fm_model
          conv_functor v)
        (fmap_tm
          FirstOrderBitVec.sig
          sig
          FirstOrderBitVec.fm_model
          fm_model
          conv_functor
          (@conv_fun_arrs) t').
  Admitted.

  Ltac conv_bitvector := 
    match goal with 
    | x: bitvector (N.of_nat ?n) |- _ => 
      match goal with 
      | H : forall (_ : n_tuple bool ?n), _ |- _ =>  
        specialize (H (eq_rect _ _ (conv_bitvector x) _ (Nat2N.id n)));
        autorewrite with interp_fm in H;
        erewrite conv_tupl_rt in H;
        eapply H
      end
    end.

  Lemma interp_fmap_fm_equi: 
    forall {c srt} {v: valu _ _ c}
      (f: FirstOrder.fm FirstOrderBitVec.sig (Snoc _ c srt)),
    (forall
      vA : FirstOrder.mod_sorts
              FirstOrderBitVec.sig
              FirstOrderBitVec.fm_model
              srt,
    interp_fm
      (VSnoc sig fm_model
          (fmap_sorts
            conv_functor srt)
          (fmap_ctx' c)
          (fmap_valu
            FirstOrderBitVec.sig
            sig
            FirstOrderBitVec.fm_model
            fm_model
            conv_functor v)
          (fmap_mv
            conv_functor srt
            vA))
      (fmap_fm
          FirstOrderBitVec.sig
          sig
          FirstOrderBitVec.fm_model
          fm_model
          conv_functor
          (@conv_fun_arrs)
          (@conv_rel_arrs)
          (@conv_forall_op) f)) <->
    (forall
      vB : FirstOrder.mod_sorts
              sig fm_model
              (fmap_sorts
                conv_functor
                srt),
    interp_fm
      (VSnoc sig fm_model
          (fmap_sorts
            conv_functor srt)
          (fmap_ctx' c)
          (fmap_valu
            FirstOrderBitVec.sig
            sig
            FirstOrderBitVec.fm_model
            fm_model
            conv_functor v)
          vB)
      (conv_forall_op
          (fmap_fm
            FirstOrderBitVec.sig
            sig
            FirstOrderBitVec.fm_model
            fm_model
            conv_functor
            (@conv_fun_arrs)
            (@conv_rel_arrs)
            (@conv_forall_op)
            f))).
  Proof.
    intros.
    unfold conv_forall_op.
    simpl.
    dependent induction f; destruct srt; simpl; 
    autorewrite with fmap_fm;
    autorewrite with interp_fm.
    - split; intros; autorewrite with interp_fm in *; trivial.
    - split; intros; autorewrite with interp_fm in *; trivial.
      + specialize (H (n_tuple_repeat n false)).
        auto.
      + specialize (H (conv_n_tuple _ vA)).
        auto.
    - split; intros; autorewrite with fmap_fm in *; autorewrite with interp_fm in *; simpl in *.
      + conv_bitvector.
      + evar (x: bitvector (N.of_nat n)).
        specialize (H x).
        subst x.
        autorewrite with interp_fm in H.
        eapply H.
    - inversion s.
    - split; intros.
      + conv_bitvector.
      + specialize (H (conv_n_tuple _ vA)).
        autorewrite with fmap_fm in *.
        autorewrite with interp_fm in *.
        eapply H.
    - split; intros; autorewrite with interp_fm.
      + conv_bitvector.
      + specialize (H (conv_n_tuple _ vA)).
        autorewrite with interp_fm in H.
        destruct H; intuition eauto.
    - split; intros; autorewrite with interp_fm.
      + conv_bitvector.
      + specialize (H (conv_n_tuple _ vA)).
        autorewrite with interp_fm in H.
        intuition eauto.
    - split; intros; autorewrite with interp_fm.
      + conv_bitvector.
      + specialize (H (conv_n_tuple _ vA)).
        autorewrite with interp_fm in H.
        intuition eauto.
    - split; intros; autorewrite with interp_fm.
      + conv_bitvector.
      + specialize (H (conv_n_tuple _ vA)).
        autorewrite with interp_fm in H.
        intuition eauto.
  Qed.

  Definition conv_wf : functor_wf _ _ _ _ conv_functor (@conv_fun_arrs) (@conv_rel_arrs) (@conv_forall_op) := {|
    interp_tm_inj := ltac:(intros; eapply fmap_tm_inj);
    fmap_rel_equi := ltac:(intros; inversion r);
    interp_fmap_forall_equi := ltac:(intros; eapply interp_fmap_fm_equi);
  |}.

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

  Print Assumptions conv_corr.

End CompileBitVec.
