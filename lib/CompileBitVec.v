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

Require Import Coq.Lists.List.
Import ListNotations.

Lemma JMeq_refl' : 
  forall T (x y: T), 
    x = y -> 
    x ~= y.
Proof.
  intros;
  subst;
  eapply JMeq_refl.
Qed.

Lemma Jmeq_pair_inv: 
  forall {A B} {x y : A * B},
    x ~= y -> 
    fst x ~= fst y /\ snd x ~= snd y.
Proof.
  intros;
  subst;
  intuition (eapply JMeq_refl).
Qed.

Lemma n_tuple_get_cons:
  forall {T} n (bs: n_tuple T (S n)), 
    exists x bs', bs = n_tuple_cons bs' x.
Proof.
  induction n; 
  intros.
  - destruct bs.
    exists t.
    simpl in *.
    exists tt.
    destruct n.
    trivial.
  - destruct (IHn (fst bs)) as [? [? ?]].
    exists x.
    exists (x0, snd bs).
    destruct bs.
    simpl in *.
    erewrite H.
    trivial.
Qed.

Lemma n_tuple_cons_ind:
  forall {T} (P : forall n, n_tuple T n -> Prop),
    P 0 tt -> 
    (forall n b bs (IH: P n bs), P (S n) (n_tuple_cons bs b : n_tuple T (1 + n))) -> 
    forall n bs, 
      P n bs.
Proof.
  induction n;
  intros;
  simpl in *.
  - destruct bs. trivial.
  - destruct (n_tuple_get_cons _ bs) as [? [? ?]].
    erewrite H1.
    eapply H0.
    eapply IHn.
Qed.

Ltac n_tuple_cons_ind := 
  match goal with 
  | BV: n_tuple _ ?N |- _ => 
    eapply n_tuple_cons_ind with (bs := BV);
    clear BV;
    clear N
  end.

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

  Definition trans_t2l_len : forall {A: Type} (n : nat) (x : n_tuple A n), N.of_nat (length (t2l x)) = (N.of_nat n) := 
    fun _ n x => comp_eq_N (f_equal _ (t2l_len n x)).

  

  (* use t2l to convert bs to a list and cast the length of t2l to w *)
  Definition conv_n_tuple (w: nat) (bs: n_tuple bool w) : bitvector (N.of_nat w) := 
    MkBitvector _ _ (trans_t2l_len _ bs).

  Lemma bv_length : 
    forall {n} (x: bitvector n), 
      length (bv_bits x) = N.to_nat n.
  Proof.
    intros.
    pose proof (bv_wf x).
    destruct x; 
    simpl in *;
    erewrite <- H.
    erewrite Nat2N.id.
    trivial.
  Qed.

  Definition conv_bitvector {n} (x: bitvector n) : n_tuple bool (N.to_nat n) :=
    eq_rect _ _ (l2t (bv_bits x)) _ (comp_eq_nat (bv_length x)).

  Require Import Coq.PArith.Pnat.


  Lemma mk_bv: 
    forall bv bv', 
      bv ~= bv' -> 
      MkBitvector bv ~= MkBitvector bv'.
  Proof.
    intros.
    subst.
    trivial.
  Qed.

  Lemma mk_bv_cons :
    forall n n' bv bv' (b b' : bool) (pf: N.of_nat (length (b :: bv)) = n)(pf': N.of_nat (length (b' :: bv')) = n'),
      b = b' -> 
      bv = bv' -> 
      pf ~= pf' -> 
      exist (fun x => N.of_nat (length x) = n) (b :: bv) pf ~= exist (fun x => N.of_nat (length x) = n') (b' :: bv') pf'.
  Proof.
    intros.
    subst.
    simpl.
    econstructor.
  Qed.

  Lemma mk_bv_cons' :
    forall n n' (b b' : bool) (l : {x : list bool | N.of_nat (length x) = n}) (r : {x : list bool | N.of_nat (length x) = n'}),
      b = b' -> 
      n = n' -> 
      proj1_sig l ~= proj1_sig r ->
      proj2_sig l ~= proj2_sig r -> 
      l ~= r.
  Proof.
    intros.
    subst.
    destruct l.
    destruct r.
    simpl in *.
    subst.
    erewrite H2.
    econstructor.
  Qed.
  
  Lemma cons_bv_inv : 
    forall {n n' b b' bv} {bits : n_tuple bool (length bv)} pf pf',
      n_tuple_cons bits b ~= conv_bitvector (n := n) {| bits := b' :: bv; wf := pf |} ->
      b = b' /\ 
      bits ~= conv_bitvector (n := n') {| bits := bv; wf := pf' |}.
  Proof.
    intros.
    revert H.
    unfold conv_bitvector.
    generalize (comp_eq_nat (bv_length {| bits := b' :: bv; wf := pf |})).
    generalize (comp_eq_nat (bv_length {| bits := bv; wf := pf' |})).
    simpl.
    generalize (N.to_nat n).
    
    intros.
    revert H.
    revert e0.
    revert e. 
    remember (l2t bv).
    match goal with 
    | H: ?X = l2t ?BV |- _ => 
      assert (X ~= l2t BV) by (eapply JMeq_refl'; trivial);
      clear H
    end.
    revert H.
    revert n0.
    intros.
    subst;
    simpl in *.

    destruct e.
    simpl.

    revert H0.
    revert bits.
    revert b.
    induction bv; simpl; intros; destruct bits.
    - destruct (Jmeq_pair_inv H0);
      simpl in *;
      subst.
      intuition.
    - 
      set (t := l2t bv) in *.
      destruct (n_tuple_cons t a) eqn:?.
      destruct (Jmeq_pair_inv H0).
      simpl in *.
      destruct (n_tuple_cons t a) eqn:?;
      simpl in *;
      destruct (n_tuple_cons_inj_r _ _ _ _ _ _ H);
      subst;
      trivial.
      clear H.
      clear H0.
      inversion Heqn0.
      subst.
      clear Heqn0.
      intuition.
  Qed.

  Definition len {n} (x: bitvector n) := length (bv_bits x).

  Lemma conv_n_tuple_size: 
    forall n bs, 
      len (conv_n_tuple n bs) = n.
  Proof.
    intros.
    unfold len, bv_bits.
    simpl.
    eapply t2l_len.
  Qed.

  Lemma N_of_nat_succ : 
    forall n, 
      (N.of_nat n + 1)%N ~=
      N.pos (BinPos.Pos.of_succ_nat n).
  Proof.
    intros.
    eapply JMeq_refl'.
    Lia.lia.
  Qed.

  Lemma conv_tuple_rt:
    forall (n : nat) (v : bitvector (N.of_nat n)) (w : n_tuple bool n),
      w ~= (conv_bitvector v) ->
      conv_n_tuple n w ~= v.
  Proof.
    intros.
    eapply bv_equal; trivial.
    simpl bits.
    revert H.
    revert v.


    eapply n_tuple_cons_ind with (bs := w);
    clear w;
    clear n;
    intros.
    - vm_compute.
      destruct v.
      destruct bits.
      * simpl in *.
        pose proof (@Eqdep_dec.UIP_dec N N.eq_dec _ _ wf eq_refl).
        subst;
        trivial.
      * exfalso.
        inversion wf.
    - destruct v.
      destruct bits.
      * exfalso. 
        simpl in *.
        Lia.lia.
      * erewrite t2l_cons.
        simpl.


        assert (length bits = n) by (simpl in *; Lia.lia).
        subst n. 

        pose proof (@cons_bv_inv).
        assert ((N.of_nat (length bits)) = (N.of_nat (length bits))) by exact eq_refl.
        destruct (cons_bv_inv (n' := (N.of_nat (length bits))) wf H1 H) as [? ?];
        subst;
        simpl in *.
        erewrite (IH _ H3).
        trivial.
  Qed.


  Lemma conv_tuple_rt_cast : 
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
    clear e.
    clear n0.
    simpl.
    revert n.
    intros.
    erewrite H; trivial.
    Unshelve.

    intros.

    eapply conv_tuple_rt.
    subst.
    trivial.
  Qed.


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

  Lemma conv_tuple_inj:
    forall n v v', 
      v = v' <-> conv_n_tuple n v = conv_n_tuple n v'.
  Proof.
    unfold conv_n_tuple.
    intros.
    split;
    intros; subst; trivial.
    inversion H.
    erewrite (t2l_eq _ _ _ _ H1).
    trivial.
  Qed.

  Ltac destruct_hlists := 
    repeat match goal with 
    | H: HList.t _ _ |- _ => 
      dependent destruction H
    | H: HList.all _ (_ ::: _) |- _ => 
      destruct H
    | H: HList.all _ hnil |- _ => 
      destruct H
    end.

  Lemma bv_ntuple_concat : 
    forall m r' n n' (l: bitvector (N.of_nat n)) l' (r: bitvector (N.of_nat m))  out,
      l ~= conv_n_tuple n l' -> 
      r ~= conv_n_tuple m r' ->
      n' ~= n + m -> 
      out ~= n_tuple_concat r' l' ->
      bv_concat l r ~= conv_n_tuple n' out.
  Proof.
    intros.
    subst.
    eapply bv_equal;
    try now (
      eapply JMeq_refl';
      Lia.lia
    ).
    simpl.
    revert H2.
    revert out.
    assert (n + m = m + n) by Lia.lia.
    erewrite H.
    intros.
    erewrite H2.
    now erewrite t2l_concat.
  Qed.

  Lemma bv_ntuple_slice : 
    forall n n' (x: bitvector (N.of_nat n)) x' hi lo out,
      x ~= conv_n_tuple n x' -> 
      out ~= n_tuple_slice hi lo x' ->
      n' ~= (Nat.min (1 + hi) n - lo) ->
      bv_extr (N.of_nat hi) (N.of_nat lo) x ~= conv_n_tuple n' out.
  Proof.
    intros.
    subst.
    eapply bv_equal;
    try now (
      eapply JMeq_refl';
      Lia.lia
    ).
    simpl.
    erewrite H0.
    unfold n_tuple_slice.
    eapply JMeq_refl'.
    erewrite t2l_n_tuple_skip_n.
    f_equal; try Lia.lia.
    erewrite t2l_n_tuple_take_n.
    f_equal. 
    Lia.lia.
  Qed.

  Lemma interp_tm_conv_tuple: 
    forall {srt c} {v: valu _ _ c} (t: FirstOrder.tm FirstOrderBitVec.sig c srt) n v', 
      srt ~= Bits n ->
      v' ~= interp_tm v t ->
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
          (@conv_fun_arrs) t) ~= 
        conv_n_tuple n v'.
  Proof.
    dependent induction t using tm_ind'.
    - intros;
      subst;
      dependent induction v; 
      dependent destruction v0;
      match goal with 
      | H: forall _, _ |- _ => 
        specialize (H n v0)
      | |- _ => idtac
      end;
      autorewrite with fmap_valu in *;
      autorewrite with fmap_tm in *;
      autorewrite with interp_tm in *;
      autorewrite with fmap_var in *;
      autorewrite with find in *;
      simpl in *;
      autorewrite with find in *;
      trivial.
    - intros.
      induction srt;
      match goal with 
      | H: Bits _ ~= Bits _ |- _ => 
        eapply JMeq_eq in H;
        inversion H
      end;
      destruct_hlists;
      subst;
      autorewrite with fmap_tm;
      autorewrite with conv_fun_arrs;
      autorewrite with interp_tm in *;
      autorewrite with conv_fun;
      simpl;
      autorewrite with mod_fns in *;
      simpl.
      * now erewrite <- H1.
      * generalize (trans_inj_add n0 m).
        unfold eq_rect_r.
        intros.
        generalize (eq_sym e).
        simpl.
        clear e.
        clear H0.
        clear x.
        revert H1.
        revert v'.

        assert ( forall
        (n': nat)
        (_ : n' ~= m + n0)
        (v' : n_tuple bool n')
        (_ : @JMeq (n_tuple bool n') v'
               (FirstOrder.mod_sorts FirstOrderBitVec.sig FirstOrderBitVec.fm_model
                  (Bits (n0 + m)))
               (@n_tuple_concat bool n0 m
                  (@interp_tm FirstOrderBitVec.sig FirstOrderBitVec.fm_model c
                     (Bits n0) v t)
                  (@interp_tm FirstOrderBitVec.sig FirstOrderBitVec.fm_model c
                     (Bits m) v t0)))
        (e : @eq N (N.add (N.of_nat n0) (N.of_nat m)) (N.of_nat n')),
      @JMeq (bitvector (N.of_nat n'))
        (mod_fns
           (@cons sorts (BV (N.of_nat n0))
              (@cons sorts (BV (N.of_nat m)) (@nil sorts)))
           (BV (N.of_nat n'))
           (@eq_rect N (N.add (N.of_nat n0) (N.of_nat m))
              (fun y : N =>
               funs
                 (@cons sorts (BV (N.of_nat n0))
                    (@cons sorts (BV (N.of_nat m)) (@nil sorts))) 
                 (BV y)) (BVCat (N.of_nat n0) (N.of_nat m))
              (N.of_nat n') e)
           (@HList.HCons sorts mod_sorts (BV (N.of_nat n0))
              (@cons sorts (BV (N.of_nat m)) (@nil sorts))
              (@interp_tm sig fm_model
                 (fmap_ctx FirstOrderBitVec.sig sig FirstOrderBitVec.fm_model
                    fm_model conv_functor c) (BV (N.of_nat n0))
                 (@fmap_valu FirstOrderBitVec.sig sig FirstOrderBitVec.fm_model
                    fm_model conv_functor c v)
                 (@fmap_tm FirstOrderBitVec.sig sig FirstOrderBitVec.fm_model
                    fm_model conv_functor (@conv_fun_arrs) c 
                    (Bits n0) t))
              (@HList.HCons sorts mod_sorts (BV (N.of_nat m)) 
                 (@nil sorts)
                 (@interp_tm sig fm_model
                    (fmap_ctx FirstOrderBitVec.sig sig FirstOrderBitVec.fm_model
                       fm_model conv_functor c) (BV (N.of_nat m))
                    (@fmap_valu FirstOrderBitVec.sig sig FirstOrderBitVec.fm_model
                       fm_model conv_functor c v)
                    (@fmap_tm FirstOrderBitVec.sig sig FirstOrderBitVec.fm_model
                       fm_model conv_functor (@conv_fun_arrs) c 
                       (Bits m) t0)) (@HList.HNil sorts mod_sorts))))
        (bitvector (N.of_nat n')) (conv_n_tuple n' v')) by shelve.

        eapply H0.
        eapply JMeq_refl'.
        Lia.lia.
        Unshelve.

        intros.
        destruct e.
        simpl.
        autorewrite with mod_fns.
        unfold eq_rect_r.
        destruct (eq_sym _).
        simpl.
        eapply bv_ntuple_concat;
        intuition eauto.

      * unfold conv_fun_obligations_obligation_1.
        unfold eq_rec_r.
        unfold eq_rec.
        destruct (eq_sym (trans_inj_sub (PeanoNat.Nat.min (1 + hi) n0) lo)).
        destruct (eq_sym (trans_inj_min (1 + hi) n0)).
        destruct (eq_sym (trans_inj_add 1 hi)).
        simpl eq_rect.
        autorewrite with mod_fns.
        clear x.
        clear H0.
        eapply bv_ntuple_slice;
        intuition eauto.
  Qed.

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
  Proof.
    induction srt.
    intros.
    pose proof @interp_tm_conv_tuple.
    erewrite (@interp_tm_conv_tuple (Bits n) c v t n (interp_tm v t));
    eauto.
    erewrite (@interp_tm_conv_tuple (Bits n) c v t' n (interp_tm v t'));
    eauto.
    eapply conv_tuple_inj.
  Qed.


  Ltac conv_bitvector := 
    match goal with 
    | x: bitvector (N.of_nat ?n) |- _ => 
      match goal with 
      | H : forall (_ : n_tuple bool ?n), _ |- _ =>  
        specialize (H (eq_rect _ _ (conv_bitvector x) _ (Nat2N.id n)));
        autorewrite with interp_fm in H;
        erewrite conv_tuple_rt_cast in H;
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

End CompileBitVec.
