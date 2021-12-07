From Equations Require Import Equations.

Require Import Coq.Classes.EquivDec.

Require Import Leapfrog.FinType.
Require Import Leapfrog.ConfRel.
Require Import Leapfrog.P4automaton.
Require Import Leapfrog.Ntuple.
Require Import Leapfrog.FirstOrder.
Require Import Coq.Logic.JMeq.
Import HListNotations.

Require Leapfrog.FirstOrderConfRelSimplified.
Require Leapfrog.FirstOrderBitVec.

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
  Variable (H: Type).
  Context `{H_eq_dec: EquivDec.EqDec H eq}.
  Context `{H_finite: @Finite H _ H_eq_dec}.
  Variable (sz: H -> nat).

  Variable (a: P4A.t S sz).

  Equations compile_store_ctx_partial
    (hdrs: list H)
    : ctx FOBV.sig
  := {
    compile_store_ctx_partial nil := CEmp _;
    compile_store_ctx_partial (hdr :: hdrs) :=
      CSnoc _ (compile_store_ctx_partial hdrs) (FOBV.Bits (sz hdr))
  }.

  Definition compile_store_ctx : ctx FOBV.sig :=
    compile_store_ctx_partial (enum H).

  Equations compile_store_valu_partial
    {hdrs: list H}
    (hl: HList.t (fun h => (n_tuple bool (sz h))) hdrs)
    : valu FOBV.sig FOBV.fm_model (compile_store_ctx_partial hdrs)
      by struct hl
  := {
    compile_store_valu_partial hnil := VEmp _ _;
    compile_store_valu_partial (hdr ::: hdrs) :=
      VSnoc _ FOBV.fm_model (FOBV.Bits _) _ hdr
            (compile_store_valu_partial hdrs)
  }.

  Equations compile_ctx (c: ctx (FOS.sig sz)) : ctx FOBV.sig := {
    compile_ctx (CEmp _) := CEmp _;
    compile_ctx (CSnoc _ c FOS.Store) :=
      app_ctx (compile_ctx c) compile_store_ctx;
    compile_ctx (CSnoc _ c (FOS.Bits n)) :=
      CSnoc _ (compile_ctx c) (FOBV.Bits n)
  }.

  Equations build_hlist_env
    (hdrs: list H)
    (env: P4A.store H sz)
    : (HList.t (fun h => (n_tuple bool (sz h))) hdrs) := {
      build_hlist_env nil _ := hnil;
      build_hlist_env (hdr :: hdrs) env :=
        let v := match P4A.find H sz hdr env with
                 | P4A.VBits _ v => v
                 end in
        (_ v) ::: build_hlist_env hdrs env
    }.

  Equations compile_valu
    {c: ctx (FOS.sig sz)}
    (v: valu (FOS.sig sz) (FOS.fm_model a) c)
    : valu FOBV.sig FOBV.fm_model (compile_ctx c) := {
    compile_valu (VEmp _ _) := VEmp _ _;
    compile_valu (VSnoc _ _ (FOS.Bits n) _ v vinner) :=
      VSnoc _ FOBV.fm_model (FOBV.Bits n) _ v (compile_valu vinner);
    compile_valu (VSnoc _ _ (FOS.Store) _ v vinner) :=
      app_valu _ (compile_valu vinner) (compile_store_valu_partial (build_hlist_env _ v))
  }.

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

  Equations compile_lookup_partial
    (k: H)
    (enum: list H)
    (elem_of_enum: List.In k enum)
    : var (FOBV.sig) (compile_store_ctx_partial enum)
          (FOBV.Bits (sz k)) := {
    compile_lookup_partial k (elem :: enum) elem_of_enum :=
      match here_or_there elem_of_enum with
      | left Heq =>
        _ (VHere _ (compile_store_ctx_partial enum) (FOBV.Bits (sz elem)))
      | right Helse =>
        VThere FOBV.sig _ (FOBV.Bits (sz elem))
               _ (compile_lookup_partial k enum Helse)
      end
  }.

  Definition compile_lookup (k: H)
    : var FOBV.sig compile_store_ctx (FOBV.Bits (sz k))
  :=
    compile_lookup_partial k (enum H) (elem_of_enum k).

  Definition get_sizes (enum: list H) : list nat :=
    List.map sz enum.

  Definition compile_sizes (enum: list H) : nat :=
    List.list_sum (get_sizes enum).

  Definition compile_sort (s: FOS.sorts) : FOBV.sorts :=
    match s with
    | FOS.Bits n => FOBV.Bits n
    | FOS.Store => FOBV.Bits (compile_sizes (enum H))
    end.

  Equations compile_store_partial
    (enum: list H)
    : tm FOBV.sig (compile_store_ctx_partial enum)
                  (FOBV.Bits (compile_sizes enum)) := {
    compile_store_partial nil := TFun FOBV.sig (FOBV.BitsLit 0 tt) hnil;
    compile_store_partial (elem :: enum) :=
      TFun FOBV.sig (FOBV.Concat (sz elem) (compile_sizes enum))
                    (TVar (VHere _ _ _) :::
                     tm_cons FOBV.sig (compile_store_partial enum) ::: hnil)
  }.

  Definition compile_store
    : tm (FOBV.sig) compile_store_ctx (compile_sort FOS.Store)
  :=
    compile_store_partial (enum H).

  Equations subscript {c n}
    (v: var (FOS.sig sz) c FOS.Store)
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
    {c: ctx (FOS.sig sz)}
    {s: FOS.sorts}
    (v: var (FOS.sig sz) c s)
    : tm FOBV.sig (compile_ctx c) (compile_sort s)
  := {
    compile_var (VHere _ c (FOS.Bits n)) :=
      TVar (VHere _ (compile_ctx c) (FOBV.Bits n));
    compile_var (VHere _ c FOS.Store) := reindex_tm compile_store;
    compile_var (VThere _ c (FOS.Bits _) s' v) := tm_cons FOBV.sig (compile_var v);
    compile_var (VThere _ c FOS.Store s' v) := weaken_tm _ (compile_var v)
  }.

  Equations compile_tm
    {c: ctx (FOS.sig sz)}
    {s: FOS.sorts}
    (t: tm (FOS.sig sz) c s):
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
      TVar (subscript v (compile_lookup h))
  }.

  Equations compile_fm
    {c: ctx (FOS.sig sz)}
    (f: fm (FOS.sig sz) c)
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

  Equations compile_store_val_partial
    (s: store (P4A.interp a))
    (enum: list H)
    : n_tuple bool (compile_sizes enum)
  := {
    compile_store_val_partial s nil := tt;
    compile_store_val_partial s (elem :: enum) :=
      let '(P4A.VBits _ v) := P4A.find H sz elem s in
      n_tuple_concat v (compile_store_val_partial s enum)
  }.

  Equations compile_val
    {sort: FOS.sorts}
    (val: FOS.mod_sorts a sort)
    : FOBV.mod_sorts (compile_sort sort)
  := {
    @compile_val (FOS.Bits _) v := _ v;
    @compile_val FOS.Store s :=
      compile_store_val_partial s (enum H);
  }.

  Transparent compile_store_valu_partial.

  Lemma compile_store_val_correct':
    forall (h : H)
      (m : mod_sorts (FOS.sig sz) (FOS.fm_model a) FOS.Store) enum Hin,
    List.NoDup enum ->
    match P4A.find H sz h m with
    | P4A.VBits _ v1 => v1
    end =
    find FOBV.sig FOBV.fm_model
      (compile_lookup_partial h enum Hin)
      (compile_store_valu_partial (build_hlist_env enum m))
  .
  Proof.
    intros.
    dependent induction enum.
    - contradiction.
    - autorewrite with build_hlist_env.
      simpl.
      unfold build_hlist_env_obligations_obligation_1.
      autorewrite with compile_lookup_partial.
      destruct Hin.
      + subst; simpl.
        unfold here_or_there.
        destruct (equiv_dec _ _); [|congruence].
        simpl.
        unfold compile_lookup_partial_obligations_obligation_1.
        simpl.
        unfold equiv in e.
        dependent destruction e.
        cbn.
        now rewrite (find_equation_1 FOBV.sig FOBV.fm_model (compile_store_ctx_partial enum) (FOBV.Bits (sz h))).
      + unfold here_or_there.
        destruct (equiv_dec _ _); simpl.
        unfold equiv in e.
        inversion H0.
        congruence.
        rewrite (find_equation_2 FOBV.sig FOBV.fm_model (compile_store_ctx_partial enum) (FOBV.Bits (sz a0)) (FOBV.Bits (sz h))).
        apply IHenum.
        now inversion H0.
  Qed.

  Opaque compile_store_valu_partial.

  Lemma compile_store_val_correct:
    forall (h : H) c (v0 : var (FOS.sig sz) c FOS.Store) v,
      match P4A.find H sz h (find (FOS.sig sz) (FOS.fm_model a) v0 v)
      with
      | P4A.VBits _ v1 => v1
      end =
      find FOBV.sig FOBV.fm_model
        (subscript v0 (compile_lookup h)) (compile_valu v).
  Proof.
    intros.
    dependent induction v; dependent destruction v0.
    - rewrite (compile_valu_equation_3 (c0 := c) m).
      rewrite (subscript_equation_1 c).
      replace (find FOBV.sig FOBV.fm_model _ _)
      with (find FOBV.sig FOBV.fm_model (compile_lookup h)
                 (compile_store_valu_partial (build_hlist_env (enum H) m))).
      + autorewrite with find.
        unfold compile_lookup.
        apply compile_store_val_correct'.
        apply NoDup_enum.
      + erewrite <- find_app_right; now f_equal.
    - autorewrite with find.
      rewrite IHv; auto.
      destruct s.
      + simpl.
        rewrite (subscript_equation_2 n (ctx1 := c) v0 (compile_lookup h)).
        rewrite (compile_valu_equation_2 n (c0 := c) m).
        now rewrite (find_equation_2 FOBV.sig FOBV.fm_model (compile_ctx c) (FOBV.Bits n) (FOBV.Bits (sz h))).
      + rewrite (subscript_equation_3 (ctx1 := c) v0).
        rewrite (compile_valu_equation_3 (c0 := c) m v).
        erewrite <- find_app_left; now f_equal.
  Qed.

  Equations decompile_store_val_partial
    (enum: list H)
    (val: n_tuple bool (compile_sizes enum))
    (store: P4A.store H sz)
    : P4A.store H sz
  := {
    decompile_store_val_partial nil val store := store;
    decompile_store_val_partial (elem :: enum) val store :=
      let prefix := rewrite_size _ (n_tuple_take_n (sz elem) val) in
      let suffix := rewrite_size _ (n_tuple_skip_n (sz elem) val) in
      P4A.assign H sz elem (P4A.VBits _ prefix)
                 (decompile_store_val_partial enum suffix store)
  }.
  Next Obligation.
    unfold compile_sizes.
    simpl.
    remember (List.list_sum _).
    remember (sz elem).
    Lia.lia.
  Defined.
  Next Obligation.
    unfold compile_sizes.
    simpl.
    remember (List.list_sum _).
    remember (sz elem).
    Lia.lia.
  Defined.

  Definition init_store: P4A.store H sz.
  Proof.
    apply DepEnv.init.
    intro.
    constructor.
    apply n_tuple_repeat.
    exact false.
  Defined.

  Equations decompile_val
    {sort: FOS.sorts}
    (val: FOBV.mod_sorts (compile_sort sort))
    : FOS.mod_sorts a sort
  := {
    @decompile_val (FOS.Bits _) v := v;
    @decompile_val FOS.Store v :=
      decompile_store_val_partial (enum H) v init_store;
  }.

  Lemma compile_store_val_partial_invariant:
    forall h v enum s,
      ~ List.In h enum ->
      compile_store_val_partial (P4A.assign H sz h v s) enum =
      compile_store_val_partial s enum.
  Proof.
    intros.
    induction enum.
    - reflexivity.
    - autorewrite with compile_store_val_partial; simpl.
      rewrite IHenum.
      + rewrite P4A.find_not_first; auto.
        contradict H0.
        subst; now apply List.in_eq.
      + contradict H0.
        now apply List.in_cons.
  Qed.

  Lemma decompile_store_val_partial_roundtrip:
    forall enum val,
      List.NoDup enum ->
      val ~= compile_store_val_partial (decompile_store_val_partial enum val init_store) enum.
  Proof.
    induction enum; intros.
    - autorewrite with decompile_store_val_partial.
      autorewrite with compile_store_val_partial.
      now destruct val.
    - autorewrite with decompile_store_val_partial.
      autorewrite with compile_store_val_partial.
      simpl.
      rewrite P4A.assign_find; auto.
      symmetry.
      rewrite <- NtupleProofs.n_tuple_concat_roundtrip with (n := sz a0).
      symmetry.
      apply NtupleProofs.concat_proper with
        (xs2 := (rewrite_size (decompile_store_val_partial_obligations_obligation_1 a0 enum) _))
        (ys2 := (compile_store_val_partial _ enum)).
      + now rewrite rewrite_size_jmeq.
      + rewrite compile_store_val_partial_invariant.
        rewrite <- IHenum.
        now rewrite rewrite_size_jmeq.
        all: now inversion H0.
  Qed.

  Lemma compile_val_roundtrip:
    forall s (val: FOBV.mod_sorts (compile_sort s)),
      val = compile_val (decompile_val val).
  Proof.
    intros.
    destruct s.
    - reflexivity.
    - autorewrite with decompile_val.
      autorewrite with compile_val.
      rewrite <- decompile_store_val_partial_roundtrip; auto.
      apply NoDup_enum.
  Qed.

  Definition store_almost_equal (s1 s2: store (P4A.interp a)) :=
    forall (h: H), P4A.find H sz h s1 = P4A.find H sz h s2.

  Theorem store_eq:
    forall (s1 s2: store (P4A.interp a)),
      store_almost_equal s1 s2 ->
      s1 = s2.
  Proof.
    unfold store_almost_equal, P4A.find.
    intros.
    eapply DepEnv.env_extensionality; eauto.
  Qed.

  Lemma decompile_val_roundtrip:
    forall s (val: FOS.mod_sorts a s),
      val = decompile_val (compile_val val).
  Proof.
    intros.
    destruct s.
    - autorewrite with compile_val.
      autorewrite with decompile_val.
      constructor.
    - apply store_eq.
      unfold store_almost_equal; intros.
      autorewrite with compile_val.
      autorewrite with decompile_val.
      pose proof (elem_of_enum (Finite := H_finite) h).
      revert h H0; induction (enum H); intros.
      + contradiction.
      + destruct (h == a0).
        * unfold equiv in e.
          subst.
          clear IHl.
          autorewrite with compile_store_val_partial.
          autorewrite with decompile_store_val_partial.
          simpl.
          rewrite P4A.assign_find;
            try solve [eauto | typeclasses eauto].
          destruct (P4A.find H sz a0 val).
          f_equal.
          apply JMeq_eq.
          rewrite rewrite_size_jmeq.
          pose proof NtupleProofs.n_tuple_take_n_roundtrip.
          now specialize (H1 (sz a0) n _ (compile_store_val_partial val l)).
        * unfold equiv, complement in c.
          autorewrite with compile_store_val_partial.
          autorewrite with decompile_store_val_partial.
          simpl.
          rewrite P4A.find_not_first by assumption.
          rewrite IHl by (destruct H0; congruence).
          do 2 f_equal.
          destruct (P4A.find H sz a0 val).
          apply JMeq_eq.
          rewrite rewrite_size_jmeq.
          pose proof NtupleProofs.n_tuple_skip_n_roundtrip.
          now specialize (H1 (sz a0) n _ (compile_store_val_partial val l)).
  Qed.

  Lemma compile_store_val_partial_correct':
    forall enum m,
      compile_store_val_partial m enum =
      interp_tm
          (compile_store_valu_partial (build_hlist_env enum m))
          (compile_store_partial enum).
  Proof.
    induction enum; intros.
    - reflexivity.
    - autorewrite with compile_store_val_partial.
      autorewrite with build_hlist_env.
      simpl.
      unfold build_hlist_env_obligations_obligation_1.
      destruct (P4A.find H sz a0 m).
      rewrite (compile_store_valu_partial_equation_2 a0 (rest := enum) n).
      rewrite (compile_store_partial_equation_2 a0 enum).
      autorewrite with interp_tm; simpl.
      autorewrite with mod_fns.
      f_equal.
      rewrite <- interp_tm_tm_cons.
      apply IHenum.
  Qed.

  Lemma compile_store_val_partial_correct:
    forall m,
      compile_store_val_partial m (enum H) =
      interp_tm
          (compile_store_valu_partial (build_hlist_env (enum H) m))
          (compile_store_partial (enum H)).
  Proof.
    apply compile_store_val_partial_correct'.
  Qed.

  Lemma compile_var_correct:
    forall c s (v: var _ c s) val,
      compile_val (interp_tm (m := FOS.fm_model a) val (TVar v)) =
      interp_tm (compile_valu val) (compile_var v).
  Proof.
    dependent induction val; intros.
    - dependent destruction v.
    - dependent destruction v.
      + destruct s; [easy|].
        rewrite (compile_var_equation_2 c).
        rewrite (compile_valu_equation_3 (c0 := c) m).
        unfold compile_store.
        autorewrite with interp_tm.
        autorewrite with find.
        replace (@interp_tm FOBV.sig FOBV.fm_model _ _ _ _)
        with (interp_tm
                (compile_store_valu_partial (build_hlist_env (enum H) m))
                (compile_store_partial (enum (Finite := H_finite) H))).
        * autorewrite with compile_val.
          apply compile_store_val_partial_correct.
        * now rewrite interp_tm_reindex_tm with (sig := FOBV.sig) (v' := compile_valu val).
      + destruct s0.
        * rewrite (compile_var_equation_3 n (ctx1 := c)).
          rewrite (compile_valu_equation_2 (c0 := c) n).
          replace (@interp_tm FOBV.sig FOBV.fm_model _ _ _ _)
          with (interp_tm (compile_valu val) (compile_var v)).
          autorewrite with interp_tm.
          autorewrite with find.
          rewrite <- IHval.
          now autorewrite with interp_tm.
          now rewrite interp_tm_tm_cons with
            (sig := FOBV.sig)
            (m := FOBV.fm_model)
            (s' := FOBV.Bits n)
            (val := m).
        * rewrite (compile_var_equation_4 v).
          rewrite (compile_valu_equation_3 (c0 := c) m).
          autorewrite with interp_tm.
          autorewrite with find.
          replace (@interp_tm FOBV.sig FOBV.fm_model _ _ _ _)
          with (interp_tm (compile_valu val) (compile_var v)).
          rewrite <- IHval.
          -- now autorewrite with interp_tm.
          -- now rewrite interp_tm_weaken_tm with
               (v' := (compile_store_valu_partial (build_hlist_env (enum H) m))).
  Qed.

  Lemma compile_simplified_tm_bv_correct:
    forall c s v (tm: tm _ c s),
      compile_val (interp_tm (m := FOS.fm_model a) v tm) =
      interp_tm (compile_valu v) (compile_tm (c := c) tm).
  Proof.
    intros.
    dependent induction tm using tm_ind'.
    - autorewrite with compile_tm.
      apply compile_var_correct.
    - destruct srt;
      repeat dependent destruction hl;
      autorewrite with compile_tm;
      autorewrite with interp_tm; simpl;
      autorewrite with mod_fns;
      repeat match goal with
      | H : HList.all _ _ |- _ =>
        destruct H
      end;
      auto.
      + unfold compile_val_obligations_obligation_1.
        now rewrite <- H0, <- H1.
      + now rewrite <- H0.
      + dependent destruction t; [|easy].
        autorewrite with compile_tm.
        autorewrite with interp_tm.
        autorewrite with compile_val.
        unfold compile_val_obligations_obligation_1.
        apply compile_store_val_correct.
  Qed.

  Lemma compile_store_valu_partial_invariant:
    forall h v enum s,
      ~ List.In h enum ->
      compile_store_valu_partial (build_hlist_env enum (P4A.assign H sz h v s)) =
      compile_store_valu_partial (build_hlist_env enum s).
  Proof.
    induction enum; intros.
    - now autorewrite with build_hlist_env.
    - autorewrite with build_hlist_env.
      simpl.
      unfold build_hlist_env_obligations_obligation_1.
      rewrite P4A.find_not_first;
        try solve [typeclasses eauto | eauto].
      + destruct (P4A.find H sz a0 s).
        specialize (IHenum s).
        rewrite (compile_store_valu_partial_equation_2 _ (rest := enum)).
        rewrite (compile_store_valu_partial_equation_2 _ (rest := enum)).
        f_equal.
        apply IHenum.
        contradict H0.
        now apply List.in_cons.
      + contradict H0.
        subst.
        apply List.in_eq.
  Qed.

  Lemma compile_store_valu_partial_surjective':
    forall enum,
      List.NoDup enum ->
      forall (val: valu FOBV.sig FOBV.fm_model (compile_store_ctx_partial enum)),
        exists s: P4A.store H sz,
          compile_store_valu_partial (build_hlist_env enum s) = val.
  Proof.
    induction enum; intros.
    - setoid_rewrite build_hlist_env_equation_1.
      exists init_store.
      dependent destruction val.
      reflexivity.
    - dependent destruction val.
      inversion H0.
      specialize (IHenum H4 val).
      destruct IHenum as [? ?].
      exists (P4A.assign H sz a0 (P4A.VBits _ m) x0).
      autorewrite with build_hlist_env.
      simpl.
      unfold build_hlist_env_obligations_obligation_1.
      subst.
      rewrite (compile_store_valu_partial_equation_2 a0 (rest := enum)).
      f_equal.
      rewrite P4A.assign_find; auto.
      now apply compile_store_valu_partial_invariant.
  Qed.

  Lemma compile_store_valu_partial_surjective:
    forall (val: valu FOBV.sig FOBV.fm_model compile_store_ctx),
      exists s: P4A.store H sz,
        compile_store_valu_partial (build_hlist_env (enum H) s) = val.
  Proof.
    intros.
    apply compile_store_valu_partial_surjective'.
    apply NoDup_enum.
  Qed.

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
    try easy.
    - repeat rewrite <- compile_simplified_tm_bv_correct.
      split; intros.
      + now f_equal.
      + rewrite decompile_val_roundtrip.
        rewrite decompile_val_roundtrip at 1.
        now f_equal.
    - now rewrite IHfm.
    - now rewrite IHfm1, IHfm2.
    - now rewrite IHfm1, IHfm2.
    - now rewrite IHfm1, IHfm2.
    - destruct s.
      + autorewrite with compile_fm.
        autorewrite with interp_fm.
        intuition.
        -- specialize (H0 (decompile_val val (sort := FOS.Bits n))).
           apply IHfm in H0.
           apply H0.
        -- specialize (H0 (compile_val val)).
           apply IHfm.
           apply H0.
      + autorewrite with compile_fm.
        rewrite quantify_correct.
        intuition.
        -- pose proof (compile_store_valu_partial_surjective valu).
           destruct H1 as [s ?].
           specialize (H0 s).
           apply IHfm in H0.
           rewrite (compile_valu_equation_3 s (c0 := c)) in H0.
           now rewrite H1 in H0.
        -- specialize (H0 (compile_store_valu_partial (build_hlist_env _ val))).
           apply IHfm.
           now rewrite (compile_valu_equation_3 val (c0 := c)).
  Qed.

End CompileFirstOrderConfRelSimplified.

Print Assumptions compile_simplified_fm_bv_correct.

Register FOBV.Bits as p4a.sorts.bits.

Register FOBV.BitsLit as p4a.funs.bitslit.
Register FOBV.Concat as p4a.funs.concat.
Register FOBV.Slice as p4a.funs.slice.
