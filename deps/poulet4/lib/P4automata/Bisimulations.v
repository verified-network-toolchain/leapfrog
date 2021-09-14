Require Import Coq.micromega.Lia.
Require Import Compare_dec.
Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Equality.
Import List.ListNotations.

Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.Relations.
Require Poulet4.P4automata.WPSymLeap.
Require Poulet4.P4automata.Reachability.
Require Poulet4.P4cub.Utiliser.

Module SemBisim.
  Section SemBisim.
    Variable (a: p4automaton).
    Notation conf := (configuration a).

    Definition bisimulation (R: rel conf) :=
      forall q1 q2,
        R q1 q2 ->
        (accepting q1 <-> accepting q2) /\
        forall b, R (step q1 b) (step q2 b).

    Definition bisimilar q1 q2 :=
      exists R, bisimulation R /\ R q1 q2.

    Lemma bisimilar_implies_equiv :
      forall (c1 c2: conf),
        bisimilar c1 c2 ->
        lang_equiv c1 c2.
    Proof.
      intros.
      unfold lang_equiv.
      intros; revert c1 c2 H.
      induction input; intros.
      - unfold accepted.
        simpl.
        unfold bisimilar in H.
        destruct H as [R [? ?]].
        now apply H in H0.
      - unfold accepted.
        autorewrite with follow.
        apply IHinput.
        unfold bisimilar in H.
        destruct H as [R [? ?]].
        exists R.
        apply H in H0.
        easy.
    Qed.

    Lemma lang_equiv_is_bisimulation :
        bisimulation lang_equiv
    .
    Proof.
      unfold bisimulation; intros.
      split.
      - apply (H nil).
      - intros.
        unfold lang_equiv in *.
        intros.
        specialize (H (b :: input)).
        apply H.
    Qed.

    Lemma equiv_implies_bisimilar
          (c1 c2: conf)
      :
        lang_equiv c1 c2 -> bisimilar c1 c2
    .
    Proof.
      intros.
      exists lang_equiv.
      split; try easy.
      apply lang_equiv_is_bisimulation.
    Qed.

    Theorem bisimilar_iff_lang_equiv
            (c1 c2: conf)
      :
        lang_equiv c1 c2 <-> bisimilar c1 c2
    .
    Proof.
      split.
      - apply equiv_implies_bisimilar.
      - apply bisimilar_implies_equiv.
    Qed.

  End SemBisim.
End SemBisim.

Module SemBisimCoalg.
  Section SemBisimCoalg.
    Variable (a: p4automaton).
    Notation conf := (configuration a).
    CoInductive bisimilar : rel conf :=
    | Bisimilar:
        forall q1 q2,
          (accepting q1 <-> accepting q2) ->
          (forall b, bisimilar (step q1 b) (step q2 b)) ->
          bisimilar q1 q2
    .

    Lemma bisimilar_coalg_implies_sem_bisim:
      forall q1 q2,
        bisimilar q1 q2 ->
        SemBisim.bisimilar a q1 q2.
    Proof.
      intros.
      exists bisimilar.
      split.
      - unfold SemBisim.bisimulation.
        intros.
        inversion H0; firstorder.
      - tauto.
    Qed.

    Lemma sem_bisim_implies_bisimilar_coalg:
      forall q1 q2,
        SemBisim.bisimilar a q1 q2 ->
        bisimilar q1 q2.
    Proof.
      cofix C.
      intros.
      constructor.
      - unfold SemBisim.bisimulation in *.
        firstorder.
      - intros.
        eapply C.
        unfold SemBisim.bisimilar, SemBisim.bisimulation in *.
        firstorder.
    Qed.

  End SemBisimCoalg.
End SemBisimCoalg.

Module SemBisimUpto.
  Section SemBisimUpto.
    Variable (a: p4automaton).
    Notation conf := (configuration a).
    Definition bisimulation_upto
               (f: rel conf -> rel conf)
               (R: rel conf)
      :=
        forall c1 c2,
          R c1 c2 ->
          (accepting c1 <-> accepting c2) /\
          forall b, f R (step c1 b) (step c2 b)
    .

    Definition bisimilar_upto
               (f: rel conf -> rel conf)
               (c1 c2: conf)
      :=
        exists R, bisimulation_upto f R /\ R c1 c2
    .

    Definition closure_extends
               (close: rel conf -> rel conf)
      :=
        forall (R: rel conf) c1 c2,
          R c1 c2 -> close R c1 c2
    .

    Definition closure_preserves_accept
               (close: rel conf -> rel conf)
      :=
        forall (R: rel conf),
          (forall c1 c2, R c1 c2 -> accepting c1 <-> accepting c2) ->
          (forall c1 c2, close R c1 c2 -> accepting c1 <-> accepting c2)
    .

    Definition closure_preserves_transition
               (close: rel conf -> rel conf)
      :=
        forall (R: rel conf),
          (forall c1 c2, R c1 c2 ->
                    forall b, close R (step c1 b) (step c2 b)) ->
          (forall c1 c2, close R c1 c2 ->
                    forall b, close R (step c1 b) (step c2 b))
    .

    Definition closure_mono
               (close: rel conf -> rel conf)
      :=
        forall (R R': rel conf),
          (forall c1 c2, R c1 c2 -> R' c1 c2) ->
          (forall c1 c2, close R c1 c2 -> close R' c1 c2)
    .

    Class SoundClosure
          (f: rel conf -> rel conf)
      := {
      closure_sound_extends: closure_extends f;
      closure_sound_preserves_accept: closure_preserves_accept f;
      closure_sound_preserves_transition: closure_preserves_transition f;
      closure_sound_mono: closure_mono f;
        }.

    Lemma bisimilar_implies_bisimilar_upto
          (f: rel conf -> rel conf)
      :
        SoundClosure f ->
        forall c1 c2,
          SemBisim.bisimilar a c1 c2 ->
          bisimilar_upto f c1 c2
    .
    Proof.
      intros.
      destruct H0 as [R [? ?]].
      exists R; split; auto.
      intros c1' c2' ?; split.
      - now apply H0.
      - intros.
        now apply H, H0.
    Qed.

    Lemma bisimilar_upto_implies_bisimilar
          (f: rel conf -> rel conf)
      :
        SoundClosure f ->
        forall c1 c2,
          bisimilar_upto f c1 c2 ->
          SemBisim.bisimilar a c1 c2
    .
    Proof.
      intros.
      destruct H0 as [R [? ?]].
      exists (f R); split.
      - intros c1' c2' ?; split.
        + revert c1' c2' H2.
          now apply H, H0.
        + revert c1' c2' H2.
          now apply H, H0.
      - now apply closure_sound_extends.
    Qed.

    (* Sanity check: the identity function is a valid closure. *)
    Definition close_id (R: rel conf) := R.

    Program Instance close_id_sound
      : SoundClosure close_id
    .
    Solve Obligations with firstorder.

  End SemBisimUpto.
End SemBisimUpto.

Module SemBisimLeaps.
  Section SemBisimLeaps.
    Variable (a: p4automaton).
    Notation conf := (configuration a).

    Inductive close_interpolate (R: rel conf) : rel conf :=
      | InterpolateBase:
          forall c1 c2,
            R c1 c2 -> close_interpolate _ c1 c2
      | InterpolateStep
          (c1 c2: conf)
          (s1 s2: states a)
          (b: bool)
          (H1: configuration_has_room c1)
          (H2: configuration_has_room c2):
          conf_state c1 = inl s1 ->
          conf_state c2 = inl s2 ->
          close_interpolate R c1 c2 ->
          (forall buf,
              length buf = min
                (configuration_room_left c1)
                (configuration_room_left c2) ->
              R (follow c1 buf) (follow c2 buf)) ->
          close_interpolate R (step c1 b) (step c2 b)
    .

    Program Instance close_interpolate_sound
      : SemBisimUpto.SoundClosure a close_interpolate
    .
    Next Obligation.
      eauto using InterpolateBase.
    Qed.
    Next Obligation.
      induction H0; eauto.
      unfold configuration_has_room in H1, H2.
      repeat (unfold step; destruct (le_lt_dec _ _); try lia).
      unfold accepting; simpl.
      subst; easy.
    Qed.
    Next Obligation.
      revert b; induction H0; intros; eauto.
      destruct (le_lt_dec (Nat.min (configuration_room_left c1)
                                   (configuration_room_left c2)) 2).
      - apply InterpolateBase.
        replace (step (step c1 b) b0) with (follow c1 [b; b0]) by auto.
        replace (step (step c2 b) b0) with (follow c2 [b; b0]) by auto.
        apply H5; simpl.
        unfold configuration_room_left in *.
        unfold configuration_has_room in H1, H2.
        lia.
      - unfold configuration_room_left in *.
        eapply InterpolateStep with (s1 := s1) (s2 := s2); auto.
        + unfold configuration_has_room, step.
          destruct (le_lt_dec _ _); simpl; lia.
        + unfold configuration_has_room, step.
          destruct (le_lt_dec _ _); simpl; lia.
        + unfold step.
          destruct (le_lt_dec _ _); try lia.
          easy.
        + unfold step.
          destruct (le_lt_dec _ _); try lia.
          easy.
        + intros.
          repeat rewrite <- follow_equation_2.
          apply H5; simpl.
          unfold configuration_room_left in H6.
          rewrite H6; unfold step.
          repeat (destruct (le_lt_dec _ _)); simpl; lia.
    Qed.
    Next Obligation.
      induction H0.
      - eauto using InterpolateBase.
      - eauto using InterpolateStep.
    Qed.

    Definition bisimulation_with_leaps
               (R: rel conf)
      :=
        forall c1 c2,
          R c1 c2 ->
          (accepting c1 <-> accepting c2) /\
          forall buf,
            length buf = min
              (configuration_room_left c1)
              (configuration_room_left c2) ->
            R (follow c1 buf) (follow c2 buf)
    .

    Definition bisimilar_with_leaps (c1 c2: conf) :=
      exists R,
        R c1 c2 /\ bisimulation_with_leaps R
    .

    Lemma bisimilar_with_leaps_implies_bisimilar_upto
          (c1 c2: conf)
      :
        bisimilar_with_leaps c1 c2 ->
        SemBisimUpto.bisimilar_upto a close_interpolate c1 c2
    .
    Proof.
      intros.
      destruct H as [R [? ?]].
      exists R.
      split; auto.
      intros c1' c2' ?; split; [now apply H0|]; intros.
      destruct (conf_state c1') eqn:?;
      destruct (conf_state c2') eqn:?.
      - destruct (le_lt_dec 2 (min (configuration_room_left c1')
                                   (configuration_room_left c2'))).
        + unfold configuration_room_left in *.
          eapply InterpolateStep with (s1 := s) (s2 := s0); auto.
          * unfold configuration_has_room in *; lia.
          * unfold configuration_has_room in *; lia.
          * now apply InterpolateBase.
          * now apply H0.
        + rewrite <- follow_equation_1.
          rewrite <- follow_equation_1 at 1.
          repeat rewrite <- follow_equation_2.
          apply InterpolateBase, H0; auto; simpl.
          unfold configuration_room_left in *.
          destruct c1', c2'; simpl in *.
          lia.
      - rewrite <- follow_equation_1.
        rewrite <- follow_equation_1 at 1.
        repeat rewrite <- follow_equation_2.
        apply InterpolateBase, H0; auto; simpl.
        unfold configuration_room_left.
        clear H1.
        destruct c1', c2'; simpl in *; subst.
        autorewrite with size' in *.
        lia.
      - rewrite <- follow_equation_1.
        rewrite <- follow_equation_1 at 1.
        repeat rewrite <- follow_equation_2.
        apply InterpolateBase, H0; auto; simpl.
        unfold configuration_room_left.
        clear H1.
        destruct c1', c2'; simpl in *; subst.
        autorewrite with size' in *.
        lia.
      - rewrite <- follow_equation_1.
        rewrite <- follow_equation_1 at 1.
        repeat rewrite <- follow_equation_2.
        apply InterpolateBase, H0; auto; simpl.
        unfold configuration_room_left.
        clear H1.
        destruct c1', c2'; simpl in *; subst.
        autorewrite with size' in *.
        lia.
    Qed.

    Lemma bisimilar_implies_bisimilar_with_leaps
          (c1 c2: conf)
      :
        SemBisim.bisimilar a c1 c2 ->
        bisimilar_with_leaps c1 c2
    .
    Proof.
      intros.
      destruct H as [R [? ?]].
      exists R.
      split; auto.
      intros c1' c2' ?; split.
      - now apply H.
      - intros.
        clear H2.
        induction buf using rev_ind.
        + now autorewrite with follow.
        + repeat rewrite follow_append.
          now apply H.
    Qed.

    Theorem bisimilar_iff_bisimilar_with_leaps
            (c1 c2: conf)
      :
        SemBisim.bisimilar a c1 c2 <->
        bisimilar_with_leaps c1 c2
    .
    Proof.
      split; intro.
      - now apply bisimilar_implies_bisimilar_with_leaps.
      - apply SemBisimUpto.bisimilar_upto_implies_bisimilar with (f := close_interpolate).
        + apply close_interpolate_sound.
        + now apply bisimilar_with_leaps_implies_bisimilar_upto.
    Qed.

  End SemBisimLeaps.
End SemBisimLeaps.

Module SemPre.
  Section SemPre.
    Variable (a: p4automaton).
    Notation conf := (configuration a).
    Variable (top: rel conf).
    Variable (top_closed: forall x y b, top x y -> top (step x b) (step y b)).

    Notation "⟦ x ⟧" := (interp_rels top x).
    Notation "R ⊨ S" := (forall (q1 q2: conf),
                            ⟦R⟧ q1 q2 ->
                            S q1 q2: Prop)
                          (at level 40).

    Reserved Notation "R ⇝ S" (at level 10).
    Inductive pre_bisimulation : rels conf -> rels conf -> rel conf :=
    | PreBisimulationClose:
        forall R q1 q2,
          ⟦R⟧ q1 q2 ->
          R ⇝ [] q1 q2
    | PreBisimulationSkip:
        forall R T (C: relation conf) q1 q2 (H: {R ⊨ C} + {~(R ⊨ C)}),
          match H with
          | left _ => True
          | _ => False
          end ->
          R ⇝ T q1 q2 ->
          R ⇝ (C :: T) q1 q2
    | PreBisimulationExtend:
        forall (R T: rels conf) C W q1 q2 (H: {R ⊨ C} + {~(R ⊨ C)}),
          match H with
          | right _ => True
          | _ => False
          end ->
          (C :: R) ⇝ (W ++ T) q1 q2 ->
          (forall q1 q2, ⟦W⟧ q1 q2 -> (forall bit, C (step q1 bit) (step q2 bit))) ->
          R ⇝ (C :: T) q1 q2
    where "R ⇝ S" := (pre_bisimulation R S).

    Lemma interp_rels_top:
      forall R x y,
        ⟦R⟧ x y ->
        top x y.
    Proof.
      induction R.
      - simpl in *.
        eauto.
      - simpl in *.
        firstorder.
    Qed.

    Lemma fold_right_conj:
      forall A (r: rel A) (R: list (rel A)) x y,
        fold_right relation_conjunction r R x y <->
        r x y /\ fold_right relation_conjunction rel_true R x y.
    Proof.
      induction R; intros; simpl.
      - unfold rel_true.
        tauto.
      - split; cbn; intuition.
    Qed.

    Lemma interp_rels_app:
      forall R S x y,
        ⟦R ++ S⟧ x y <->
        ⟦R⟧ x y /\
        ⟦S⟧ x y.
    Proof.
      intros.
      split; intros.
      - assert (top x y) by (apply fold_right_conj in H; tauto).
        split.
        + apply in_interp_rels; auto.
          intros.
          eapply interp_rels_in; eauto with datatypes.
        + apply in_interp_rels; auto.
          intros.
          eapply interp_rels_in; eauto with datatypes.
      - destruct H.
        assert (top x y) by (apply fold_right_conj in H; tauto).
        apply in_interp_rels; auto.
        intros.
        apply in_app_or in H2;
          destruct H2;
          eapply interp_rels_in in H2;
          eauto with datatypes.
    Qed.

    Lemma sem_pre_implies_sem_bisim' :
      forall R T,
        (forall q1 q2, ⟦R ++ T⟧ q1 q2 -> accepting q1 <-> accepting q2) ->
        (forall q1 q2, ⟦R ++ T⟧ q1 q2 -> forall b, ⟦R⟧ (step q1 b) (step q2 b)) ->
        forall q1 q2,
          pre_bisimulation R T q1 q2 ->
          SemBisimCoalg.bisimilar a q1 q2
    .
    Proof.
      idtac.
      intros.
      induction H1.
      - revert q1 q2 H1.
        cofix CH; intros.
        apply SemBisimCoalg.Bisimilar.
        + apply H.
          rewrite app_nil_r.
          apply H1.
        + intros.
          apply CH.
          apply H0.
          rewrite app_nil_r.
          apply H1.
      - apply IHpre_bisimulation.
        + intros.
          apply H.
          rewrite interp_rels_app in *.
          cbn.
          intuition.
          destruct H1; simpl in H2; [|contradiction].
          auto.
        + intros.
          apply H0.
          rewrite interp_rels_app in *.
          cbn.
          intuition.
          destruct H1; simpl in H2; [|contradiction].
          auto.
      - apply IHpre_bisimulation.
        + intros.
          apply H.
          rewrite !interp_rels_app in *.
          cbn in *.
          intuition.
        + intros.
          rewrite !interp_rels_app in *.
          simpl.
          cbn.
          intuition.
          eapply H0.
          rewrite !interp_rels_app in *.
          cbn in *.
          intuition.
    Qed.

    Lemma sem_pre_implies_sem_bisim :
      forall T,
        (forall q1 q2, ⟦T⟧ q1 q2 -> accepting q1 <-> accepting q2) ->
        forall q1 q2,
          pre_bisimulation [] T q1 q2 ->
          SemBisimCoalg.bisimilar a q1 q2.
    Proof.
      intros.
      eapply sem_pre_implies_sem_bisim' with (R:=[]) (T:=T); eauto.
      intros.
      apply top_closed.
      eauto using interp_rels_top.
    Qed.

  End SemPre.
End SemPre.

Module SemPreLeaps.
  Section SemPreLeaps.
    Variable (a: p4automaton).
    Notation conf := (configuration a).
    Variable (top: rel conf).
    Variable (top_closed: forall x y b, top x y -> top (step x b) (step y b)).

    Notation "⟦ x ⟧" := (interp_rels top x).
    Notation "R ⊨ S" := (forall q1 q2,
                            ⟦R⟧ q1 q2 ->
                            S q1 q2)
                          (at level 40).

    Reserved Notation "R ⇝ S" (at level 10).
    Inductive pre_bisimulation : rels conf -> rels conf -> rel conf :=
    | PreBisimulationClose:
        forall R q1 q2,
          ⟦R⟧ q1 q2 ->
          R ⇝ [] q1 q2
    | PreBisimulationSkip:
        forall R T (C: relation conf) q1 q2,
          R ⊨ C ->
          R ⇝ T q1 q2 ->
          R ⇝ (C :: T) q1 q2
    | PreBisimulationExtend:
        forall R T C W q1 q2,
          (C :: R) ⇝ (W ++ T) q1 q2 ->
          (forall q1 q2, ⟦W⟧ q1 q2 -> (forall bit, C (step q1 bit) (step q2 bit))) ->
          R ⇝ (C :: T) q1 q2
    where "R ⇝ S" := (pre_bisimulation R S).

  End SemPreLeaps.
End SemPreLeaps.

Module SynPreSynWP.
  Section SynPreSynWP.

    (* State identifiers. *)
    Variable (S1: Type).
    Context `{S1_eq_dec: EquivDec.EqDec S1 eq}.
    Context `{S1_finite: @Finite S1 _ S1_eq_dec}.

    Variable (S2: Type).
    Context `{S2_eq_dec: EquivDec.EqDec S2 eq}.
    Context `{S2_finite: @Finite S2 _ S2_eq_dec}.

    Notation S := ((S1 + S2)%type).

    (* Header identifiers. *)
    Variable (H: nat -> Type).
    Context `{H_eq_dec: forall n, EquivDec.EqDec (H n) eq}.
    Instance H'_eq_dec: EquivDec.EqDec (P4A.H' H) eq := P4A.H'_eq_dec (H_eq_dec:=H_eq_dec).
    Context `{H_finite: @Finite (Syntax.H' H) _ H'_eq_dec}.

    Variable (a: P4A.t S H).

    Variable (wp: P4A.t S H ->
                  conf_rel S H ->
                  list (conf_rel S H)).

    Notation conf := (configuration (P4A.interp a)).

    Variable (top: rel conf).
    Variable (top_closed: forall x y b, top x y -> top (step x b) (step y b)).

    Notation "⟦ x ⟧" := (interp_crel a top x).
    Notation "⦇ x ⦈" := (interp_conf_rel a x).
    Notation "R ⊨ q1 q2" := (⟦R⟧ q1 q2) (at level 40).
    Notation "R ⊨ S" := (interp_entailment a top {| e_prem := R; e_concl := S |}) (at level 40).
    Notation δ := step.

    Reserved Notation "R ⇝ S" (at level 10).
    Inductive pre_bisimulation : crel S H -> crel S H -> relation conf :=
    | PreBisimulationClose:
        forall R q1 q2,
          ⟦R⟧ q1 q2 ->
          R ⇝ [] q1 q2
    | PreBisimulationSkip:
        forall (R T: crel S H) (C: conf_rel S H) q1 q2 (H: {R ⊨ C} + {~(R ⊨ C)}),
          match H with
          | left _ => True
          | _ => False
          end ->
          R ⇝ T q1 q2 ->
          R ⇝ (C :: T) q1 q2
    | PreBisimulationExtend:
        forall (R T: crel S H) (C: conf_rel S H) (W: crel S H) q1 q2 (H: {R ⊨ C} + {~(R ⊨ C)}),
          match H with
          | right _ => True
          | _ => False
          end ->
          W = wp a C ->
          (C :: R) ⇝ (W ++ T) q1 q2 ->
          R ⇝ (C :: T) q1 q2
    where "R ⇝ S" := (pre_bisimulation R S).

    Fixpoint range (n: nat) :=
      match n with
      | 0 => []
      | Datatypes.S n => range n ++ [n]
      end.

    Definition not_accept1 (a: P4A.t S H) (s: S) : crel S H :=
      List.map (fun n =>
                  {| cr_st := {| cs_st1 := {| st_state := inr true; st_buf_len := 0 |};
                                 cs_st2 := {| st_state := inl s;    st_buf_len := n |} |};
                     cr_rel := BRFalse _ BCEmp |})
               (range (P4A.size a s)).

    Definition not_accept2 (a: P4A.t S H) (s: S) : crel S H :=
      List.map (fun n =>
                  {| cr_st := {| cs_st1 := {| st_state := inl s;    st_buf_len := n |};
                                 cs_st2 := {| st_state := inr true; st_buf_len := 0 |} |};
                     cr_rel := BRFalse _ BCEmp |})
               (range (P4A.size a s)).

    Definition init_rel (a: P4A.t S H) : crel S H :=
      List.concat (List.map (not_accept1 a) (enum S) ++
                            List.map (not_accept2 a) (enum S)).


    Definition sum_not_accept1 (a: P4A.t (S1 + S2) H) (s: S1) : crel (S1 + S2) H :=
      List.map (fun n =>
                  {| cr_st := {| cs_st1 := {| st_state := inl (inl s); st_buf_len := n |};
                                 cs_st2 := {| st_state := inr true;    st_buf_len := 0 |} |};
                     cr_rel := BRFalse _ BCEmp |})
               (range (P4A.size a (inl s))).

    Definition sum_not_accept2 (a: P4A.t (S1 + S2) H) (s: S2) : crel (S1 + S2) H :=
      List.map (fun n =>
                  {| cr_st := {| cs_st1 := {| st_state := inr true;    st_buf_len := 0 |};
                                 cs_st2 := {| st_state := inl (inr s); st_buf_len := n |} |};
                     cr_rel := BRFalse _ BCEmp |})
               (range (P4A.size a (inr s))).

    Definition sum_init_rel (a: P4A.t (S1 + S2) H) : crel (S1 + S2) H :=
      List.concat (List.map (sum_not_accept1 a) (enum S1)
                            ++ List.map (sum_not_accept2 a) (enum S2)).
    Notation "ctx , ⟨ s1 , n1 ⟩ ⟨ s2 , n2 ⟩ ⊢ b" :=
      ({| cr_st :=
            {| cs_st1 := {| st_state := s1; st_buf_len := n1 |};
               cs_st2 := {| st_state := s2; st_buf_len := n2 |}; |};
          cr_ctx := ctx;
          cr_rel := b|}) (at level 10).
    Notation btrue := (BRTrue _ _).
    Notation bfalse := (BRFalse _ _).
    Notation "a ⇒ b" := (BRImpl a b) (at level 40).

    Definition not_equally_accepting (s: Reachability.state_pair S1 S2) : bool :=
      let '(s1, s2) := s in
      match s1.(st_state), s2.(st_state) with
      | inr true, inr true => false
      | inr true, _ => true
      | _, inr true => true
      | _, _ => false
      end.

    Definition mk_rel '((s1, s2): Reachability.state_pair S1 S2)
      : conf_rel (S1 + S2) H :=
      {| cr_st := {| cs_st1 := s1;
                     cs_st2 := s2 |};
         cr_ctx := BCEmp;
         cr_rel := bfalse |}.

    Definition mk_partition (r: Reachability.state_pairs _ _)
      : crel (S1 + S2) H :=
      List.map mk_rel (List.filter not_equally_accepting r).

    Definition mk_init (n: nat) s1 s2 :=
      List.nodup (@conf_rel_eq_dec _ _ _ _ _)
                 (mk_partition
                    (Reachability.reachable_states a n s1 s2)).

    Definition lift_l {X Y A} (f: X -> A) (x: X + Y) : A + Y :=
      match x with
      | inl x => inl (f x)
      | inr y => inr y
      end.

    Definition separated (q1 q2: conf) : Prop :=
      ((exists x, conf_state q1 = inl (inl x)) \/
       (exists y, conf_state q1 = inr y)) /\
      ((exists x, conf_state q2 = inl (inr x)) \/
       (exists y, conf_state q2 = inr y)).

    Definition topbdd (C: rel conf) : Prop :=
      forall q1 q2,
        C q1 q2 ->
        top q1 q2.

    Definition ctopbdd (C: crel S H) : Prop :=
      forall r,
        In r C ->
        topbdd ⦇r⦈.

    Lemma ctopbbd_topbdd:
      forall R,
        ctopbdd R ->
        topbdd ⟦R⟧.
    Proof.
      unfold ctopbdd, topbdd.
      induction R; simpl; intros.
      - assumption.
      - inversion H1.
        eauto.
    Qed.

    Lemma ctopbdd_app:
      forall C T,
        ctopbdd C ->
        ctopbdd T ->
        ctopbdd (C ++ T).
    Proof.
      unfold ctopbdd.
      intros.
      rewrite in_app_iff in *.
      intuition.
    Qed.

    Lemma topbdd_mono:
      forall (R S: rel conf),
        (forall x y, R x y -> S x y) ->
        topbdd S ->
        topbdd R.
    Proof.
      unfold topbdd.
      firstorder.
    Qed.

    Definition safe_wp_1bit : Prop :=
      forall C (q1 q2: conf),
        top q1 q2 ->
        ⟦wp a C⟧ q1 q2 ->
        forall bit,
          ⦇C⦈ (δ q1 bit) (δ q2 bit).

    Definition wp_bdd :=
      forall a C,
        topbdd ⦇C⦈ ->
        ctopbdd (wp a C).

    Lemma syn_pre_implies_sem_pre:
      forall R S q1 q2,
        R ⇝ S q1 q2 ->
        ctopbdd R ->
        ctopbdd S ->
        safe_wp_1bit ->
        wp_bdd ->
        SemPre.pre_bisimulation (P4A.interp a)
                                top
                                (map (interp_conf_rel a) R)
                                (map (interp_conf_rel a) S)
                                q1 q2.
    Proof.
      intros R S q1 q2 Hstep.
      induction Hstep.
      - simpl.
        constructor.
        eauto.
      - simpl.
        intros.
        econstructor 2; eauto.
        eapply IHHstep; eauto.
        unfold ctopbdd; intros.
        eauto with datatypes.
      - rewrite map_app in IHHstep.
        subst.
        intros.
        econstructor 3; eauto.
        eapply IHHstep; eauto.
        + unfold ctopbdd in *.
          intros.
          simpl (In _ _) in *.
          intuition.
        + eapply ctopbdd_app.
          * eapply H5.
            eapply H3.
            eauto with datatypes.
          * unfold ctopbdd in *; simpl (In _ _ ) in *; eauto.
        + intros.
          eapply H4; eauto.
          eapply SemPre.interp_rels_top; eauto.
    Qed.

  End SynPreSynWP.
  Arguments pre_bisimulation {S1 equiv0 S1_eq_dec S2 equiv1 S2_eq_dec H H_eq_dec} a wp.
End SynPreSynWP.
