From Equations Require Import Equations.

Require Import Coq.Classes.EquivDec.

Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4automata.Ntuple.
Require Import Poulet4.P4automata.FirstOrder.
Require Import Coq.Logic.JMeq.
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

  Definition compile_store_ctx : ctx FOBV.sig :=
    compile_store_ctx_partial (enum (Syntax.H' H)).

  Equations compile_store_valu_partial
    {hdrs: list (Syntax.H' H)}
    (hl: HList.t (fun x => (n_tuple bool (projT1 x))) hdrs)
    : valu FOBV.sig FOBV.fm_model (compile_store_ctx_partial hdrs)
      by struct hl
  := {
    compile_store_valu_partial hnil := VEmp _ _;
    compile_store_valu_partial (hdr ::: hdrs) :=
      VSnoc _ FOBV.fm_model (FOBV.Bits _) _ hdr
            (compile_store_valu_partial hdrs)
  }.

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
        let v := match P4A.find H (projT2 hdr) env with
                 | P4A.VBits _ v => v
                 end in
        (_ v) ::: build_hlist_env hdrs env
    }.

  Equations compile_valu
    {c: ctx (FOS.sig H)}
    (v: valu (FOS.sig H) (FOS.fm_model a) c)
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
    (k: Syntax.H' H)
    (enum: list (Syntax.H' H))
    (elem_of_enum: List.In k enum)
    : var (FOBV.sig) (compile_store_ctx_partial enum)
          (FOBV.Bits (projT1 k)) := {
    compile_lookup_partial k (elem :: enum) elem_of_enum :=
      match here_or_there elem_of_enum with
      | left Heq =>
        _ (VHere _ (compile_store_ctx_partial enum) (FOBV.Bits (projT1 k)))
      | right Helse =>
        VThere FOBV.sig _ (FOBV.Bits (projT1 elem))
               _ (compile_lookup_partial k enum Helse)
      end
  }.

  Definition compile_lookup (k: Syntax.H' H)
    : var FOBV.sig compile_store_ctx (FOBV.Bits (projT1 k))
  :=
    compile_lookup_partial k (enum (Syntax.H' H)) (elem_of_enum k).

  Equations compile_sizes (enum: list (Syntax.H' H)): nat := {
    compile_sizes nil := 0;
    compile_sizes (elem :: enum) := projT1 elem + compile_sizes enum;
  }.

  Definition compile_sort (s: FOS.sorts) : FOBV.sorts :=
    match s with
    | FOS.Bits n => FOBV.Bits n
    | FOS.Store => FOBV.Bits (compile_sizes (enum (Syntax.H' H)))
    end.

  Equations compile_store_partial
    (enum: list (Syntax.H' H))
    : tm FOBV.sig (compile_store_ctx_partial enum)
                  (FOBV.Bits (compile_sizes enum)) := {
    compile_store_partial nil := TFun FOBV.sig (FOBV.BitsLit 0 tt) hnil;
    compile_store_partial (elem :: enum) :=
      TFun FOBV.sig (FOBV.Concat (projT1 elem) (compile_sizes enum))
                    (TVar (VHere _ _ _) :::
                     tm_cons FOBV.sig (compile_store_partial enum) ::: hnil)
  }.

  Definition compile_store
    : tm (FOBV.sig) compile_store_ctx (compile_sort FOS.Store)
  :=
    compile_store_partial (enum (Syntax.H' H)).

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
    compile_var (VThere _ c (FOS.Bits _) s' v) := tm_cons FOBV.sig (compile_var v);
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

  Equations compile_store_val_partial
    (s: store (P4A.interp a))
    (enum: list (Syntax.H' H))
    : n_tuple bool (compile_sizes enum)
  := {
    compile_store_val_partial s nil := tt;
    compile_store_val_partial s (elem :: enum) :=
      let '(P4A.VBits _ v) := P4A.find H (projT2 elem) s in
      n_tuple_concat v (compile_store_val_partial s enum)
  }.

  Equations compile_val
    {sort: FOS.sorts}
    (val: FOS.mod_sorts a sort)
    : FOBV.mod_sorts (compile_sort sort)
  := {
    @compile_val (FOS.Bits _) v := _ v;
    @compile_val FOS.Store s :=
      compile_store_val_partial s (enum (Syntax.H' H));
  }.

  Lemma compile_store_val_correct:
    forall (n: nat) (h : H n) c (v0 : var (FOS.sig H) c FOS.Store) v,
      compile_val (sort := FOS.Bits n)
        match P4A.find H h (find (FOS.sig H) (FOS.fm_model a) v0 v)
        with
        | P4A.VBits _ v1 => v1
        end =
      find FOBV.sig FOBV.fm_model
        (subscript v0 (compile_lookup (existT H n h))) (compile_valu v).
  Proof.
  Admitted.

  Equations decompile_store_val_partial
    (enum: list (Syntax.H' H))
    (val: n_tuple bool (compile_sizes enum))
    : store (P4A.interp a)
  := {
    decompile_store_val_partial nil val := nil;
    decompile_store_val_partial (elem :: enum) val :=
      let prefix := rewrite_size _ (n_tuple_take_n (projT1 elem) val) in
      let suffix := rewrite_size _ (n_tuple_skip_n (projT1 elem) val) in
      P4A.assign H (projT2 elem) (P4A.VBits _ prefix)
                   (decompile_store_val_partial enum suffix)
  }.
  Next Obligation.
    autorewrite with compile_sizes; Lia.lia.
  Defined.
  Next Obligation.
    autorewrite with compile_sizes; Lia.lia.
  Defined.

  Equations decompile_val
    {sort: FOS.sorts}
    (val: FOBV.mod_sorts (compile_sort sort))
    : FOS.mod_sorts a sort
  := {
    @decompile_val (FOS.Bits _) v := v;
    @decompile_val FOS.Store v :=
      decompile_store_val_partial (enum (Syntax.H' H)) v;
  }.

  Lemma compile_store_val_partial_invariant:
    forall h v enum s,
      ~ List.In h enum ->
      compile_store_val_partial (P4A.assign H (projT2 h) v s) enum =
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
      val ~= compile_store_val_partial (decompile_store_val_partial enum val) enum.
  Proof.
    induction enum; intros.
    - autorewrite with decompile_store_val_partial.
      autorewrite with compile_store_val_partial.
      now destruct val.
    - autorewrite with decompile_store_val_partial.
      autorewrite with compile_store_val_partial.
      simpl.
      rewrite P4A.assign_find.
      symmetry.
      rewrite <- NtupleProofs.n_tuple_concat_roundtrip with (n := projT1 a0).
      symmetry.
      apply NtupleProofs.concat_proper with
        (xs2 := (rewrite_size (decompile_store_val_partial_obligations_obligation_1 a0 enum) _))
        (ys2 := (compile_store_val_partial _ enum)).
      + now rewrite rewrite_size_jmeq.
      + inversion H0.
        now rewrite compile_store_val_partial_invariant,
                    <- IHenum,
                    rewrite_size_jmeq by auto.
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

  Inductive val_almost_equal:
    forall s,
      FOS.mod_sorts a s ->
      FOS.mod_sorts a s ->
      Prop
  :=
  | ValAlmostEqualBits:
      forall (n: nat) (t: n_tuple bool n), val_almost_equal (FOS.Bits n) t t
  | ValAmostEqualStore:
      forall (s1 s2: store (P4A.interp a)),
        (forall n (h: H n), P4A.find H h s1 = P4A.find H h s2) ->
        val_almost_equal FOS.Store s1 s2.

  Definition store_almost_equal (s1 s2: store (P4A.interp a)) :=
    forall n (h: H n), P4A.find H h s1 = P4A.find H h s2.

  Axiom store_eq:
    forall (s1 s2: store (P4A.interp a)),
      store_almost_equal s1 s2 ->
      s1 = s2.

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
      pose proof (elem_of_enum (Finite := H_finite) (existT _ n h)).
      revert h H0; induction (enum (Syntax.H' H)); intros.
      + contradiction.
      + destruct (existT _ n h == a0).
        * unfold equiv in e.
          subst.
          clear IHl.
          autorewrite with compile_store_val_partial.
          autorewrite with decompile_store_val_partial.
          simpl.
          rewrite P4A.assign_find.
          destruct (P4A.find H h val).
          f_equal.
          apply JMeq_eq.
          rewrite rewrite_size_jmeq.
          pose proof NtupleProofs.n_tuple_take_n_roundtrip.
          now specialize (H1 n n0 _ (compile_store_val_partial val l)).
        * unfold equiv, complement in c.
          autorewrite with compile_store_val_partial.
          autorewrite with decompile_store_val_partial.
          simpl.
          replace h with (projT2 (existT _ n h)).
          pose proof P4A.find_not_first.
          specialize (H1 H _ _ (existT H n h) a0).
          rewrite H1.
          rewrite IHl.
          f_equal.
          f_equal.
          destruct (P4A.find H (projT2 a0) val).
          apply JMeq_eq.
          rewrite rewrite_size_jmeq.
          pose proof NtupleProofs.n_tuple_skip_n_roundtrip.
          now specialize (H2 (projT1 a0) n0 _ (compile_store_val_partial val l)).
          simpl.
          destruct H0.
          congruence.
          assumption.
          easy.
          now simpl.
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
      destruct (P4A.find H (projT2 a0) m).
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
      compile_store_val_partial m (enum (Syntax.H' H)) =
      interp_tm
          (compile_store_valu_partial (build_hlist_env (enum (Syntax.H' H)) m))
          (compile_store_partial (enum (Syntax.H' H))).
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
                (compile_store_valu_partial (build_hlist_env (enum (Syntax.H' H)) m))
                (compile_store_partial (enum (Finite := H_finite) (Syntax.H' H)))).
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
               (v' := (compile_store_valu_partial (build_hlist_env (enum (Syntax.H' H)) m))).
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
        apply compile_store_val_correct.
  Qed.

  Lemma compile_store_valu_partial_invariant:
    forall h v enum s,
      ~ List.In h enum ->
      compile_store_valu_partial (build_hlist_env enum (P4A.assign H (projT2 h) v s)) =
      compile_store_valu_partial (build_hlist_env enum s).
  Proof.
    (* Probably something similar to compile_store_val_partial_invariant *)
  Admitted.

  Lemma compile_store_valu_partial_surjective':
    forall enum,
      List.NoDup enum ->
      forall (val: valu FOBV.sig FOBV.fm_model (compile_store_ctx_partial enum)),
        exists s: P4A.store H,
          compile_store_valu_partial (build_hlist_env enum s) = val.
  Proof.
    induction enum; intros.
    - exists nil.
      autorewrite with build_hlist_env.
      dependent destruction val.
      now rewrite <- compile_store_valu_partial_equation_1.
    - dependent destruction val.
      inversion H0.
      specialize (IHenum H4 val).
      destruct IHenum as [? ?].
      exists (P4A.assign H (projT2 a0) (P4A.VBits _ m) x0).
      autorewrite with build_hlist_env.
      simpl.
      unfold build_hlist_env_obligations_obligation_1.
      rewrite P4A.assign_find.
      rewrite (compile_store_valu_partial_equation_2 a0 (rest := enum) m).
      f_equal.
      now rewrite compile_store_valu_partial_invariant.
  Qed.

  Lemma compile_store_valu_partial_surjective:
    forall (val: valu FOBV.sig FOBV.fm_model compile_store_ctx),
      exists s: P4A.store H,
        compile_store_valu_partial (build_hlist_env (enum (Syntax.H' H)) s) = val.
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

Register FOBV.Bits as p4a.sorts.bits.

Register FOBV.BitsLit as p4a.funs.bitslit.
Register FOBV.Concat as p4a.funs.concat.
Register FOBV.Slice as p4a.funs.slice.
