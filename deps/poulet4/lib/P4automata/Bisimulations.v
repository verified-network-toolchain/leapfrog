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
Require Poulet4.P4automata.WP.
Require Poulet4.P4automata.WPSymBit.
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

Module SynPreSynWP1bit.
  Section SynPreSynWP1bit.
    (* State identifiers. *)
    Variable (S1: Type).
    Context `{S1_eq_dec: EquivDec.EqDec S1 eq}.
    Context `{S1_finite: @Finite S1 _ S1_eq_dec}.

    Variable (S2: Type).
    Context `{S2_eq_dec: EquivDec.EqDec S2 eq}.
    Context `{S2_finite: @Finite S2 _ S2_eq_dec}.

    (* Header identifiers. *)
    Variable (H: nat -> Type).
    Context `{H_eq_dec: forall n, EquivDec.EqDec (H n) eq}.
    Instance H'_eq_dec: EquivDec.EqDec (P4A.H' H) eq := P4A.H'_eq_dec (H_eq_dec:=H_eq_dec).
    Context `{H_finite: @Finite (Syntax.H' H) _ H'_eq_dec}.

    Variable (a: P4A.t (S1 + S2) H).

    Notation conf := (configuration (P4A.interp a)).

    Variable (top: conf -> conf -> Prop).

    Notation "⟨ R , v ⟩ ⊨ c1 c2" := (interp_store_rel R v c1 c2) (at level 50).

    Lemma wp_concrete_bdd:
      SynPreSynWP.wp_bdd S1 S2 H a (WP.wp (H:=H)) top.
    Proof.
    Admitted.

    Lemma skipn_skipn:
      forall A (x: list A) n m,
        skipn n (skipn m x) = skipn (n + m) x.
    Proof.
      induction x; intros.
      - rewrite !skipn_nil.
        reflexivity.
      - destruct m.
        + simpl.
          rewrite <- plus_n_O.
          reflexivity.
        + rewrite <- plus_n_Sm.
          simpl.
          apply IHx.
    Qed.

    Lemma firstn_firstn:
      forall A (x: list A) n m,
        firstn n (firstn m x) = firstn (min n m) x.
    Proof.
      induction x; intros.
      - rewrite !firstn_nil.
        reflexivity.
      - destruct m.
        + rewrite Min.min_0_r.
          rewrite firstn_nil.
          reflexivity.
        + simpl.
          destruct n; [reflexivity|].
          simpl.
          rewrite IHx.
          reflexivity.
    Qed.

    Lemma slice_slice:
      forall A (x: list A) hi lo hi' lo',
        P4A.slice (P4A.slice x hi lo) hi' lo' =
        P4A.slice x (Nat.min (lo + hi') hi) (lo + lo').
    Proof.
      intros.
      unfold P4A.slice.
      rewrite firstn_skipn_comm.
      rewrite skipn_skipn.
      rewrite PeanoNat.Nat.add_comm.
      rewrite firstn_firstn.
      replace (Nat.min (lo + (1 + hi')) (1 + hi))
        with (1 + Nat.min (lo + hi') hi)
        by Lia.lia.
      reflexivity.
    Qed.

    Lemma beslice_interp_length:
      forall b1 b2 ctx e hi lo,
        @be_size H ctx b1 b2 (BESlice e hi lo) =
        @be_size H ctx b1 b2 (beslice e hi lo).
    Proof.
    Admitted.

    (*
    Lemma beslice_interp:
      forall ctx (e: bit_expr H ctx) hi lo valu (q1 q2: conf),
        Syntax.rewrite_size (beslice_interp_length _ _ _ _ _ _)
          (interp_bit_expr (beslice e hi lo) valu q1 q2) =
        interp_bit_expr (BESlice e hi lo) valu q1 q2.
    Proof.
      induction e; intros; simpl; autorewrite with interp_bit_expr; auto.
      rewrite slice_slice.
      reflexivity.
    Qed.

    Lemma beconcat_interp:
      forall ctx (e1 e2: bit_expr H ctx) valu (q1 q2: conf),
        interp_bit_expr (beconcat e1 e2) valu q1 q2 =
        interp_bit_expr (BEConcat e1 e2) valu q1 q2.
    Proof.
      induction e1; destruct e2; intros; simpl; auto.
    Qed.

    Lemma be_subst_hdr_left:
      forall c (valu: bval c) size (hdr: H size) exp phi (q: conf) s1 st1 buf1 c2 (w: Ntuple.n_tuple bool size) v,
          interp_bit_expr exp valu q c2 = v ->
          conf_state q = s1 ->
          conf_store q = st1 ->
          conf_buf q = buf1 ->
          v = Ntuple.t2l w ->
          interp_bit_expr (a:=a) phi valu
                          (update_conf_store (a:=P4A.interp a)
                                             (P4A.assign _ hdr (P4A.VBits size w) st1)
                                             q)
                          c2 =
          interp_bit_expr (WP.be_subst phi exp (BEHdr c Left (P4A.HRVar (existT _ _ hdr))))
                          valu
                          q
                          c2.
    Proof.
      induction phi; intros.
      - tauto.
      - unfold WP.be_subst.
        destruct (bit_expr_eq_dec _ _); simpl; congruence.
      - unfold WP.be_subst.
        destruct (bit_expr_eq_dec _ _).
        + inversion e; clear e; subst.
          simpl.
          rewrite P4A.eq_dec_refl.
          simpl.
          rewrite P4A.eq_dec_refl.
          congruence.
        + simpl.
          destruct h.
          dependent destruction var.
          simpl in *.
          unfold P4A.find, P4A.assign.
          repeat match goal with
                 | H: context[ match ?e with _ => _ end ] |- _ => destruct e eqn:?
                 | |- context[ match ?e with _ => _ end ] => destruct e eqn:?
                 | |- _ => progress unfold "===" in *
                 | |- _ => progress simpl in *
                 | |- _ => progress subst
                 end;
            congruence.
      - reflexivity.
      - simpl.
        subst.
        erewrite IHphi; eauto.
        rewrite beslice_interp.
        reflexivity.
      - simpl.
        rewrite beconcat_interp.
        erewrite IHphi1, IHphi2; eauto.
    Qed.

    Lemma be_subst_hdr_right:
      forall c (valu: bval c) size (hdr: H size) exp phi (q: conf) s2 st2 buf2 c1 (w: Ntuple.n_tuple bool size) v,
          interp_bit_expr exp valu c1 q = v ->
          conf_state q = s2 ->
          conf_store q = st2 ->
          conf_buf q = buf2 ->
          v = Ntuple.t2l w ->
          interp_bit_expr (a:=a) phi valu
                          c1
                          (update_conf_store (a:=P4A.interp a)
                                             (P4A.assign _ hdr (P4A.VBits size w) st2)
                                             q)
                          =
          interp_bit_expr (WP.be_subst phi exp (BEHdr c Right (P4A.HRVar (existT _ _ hdr))))
                          valu
                          c1
                          q.
    Proof.
      induction phi; intros.
      - tauto.
      - unfold WP.be_subst.
        destruct (bit_expr_eq_dec _ _); simpl; congruence.
      - unfold WP.be_subst.
        destruct (bit_expr_eq_dec _ _).
        + inversion e; clear e; subst.
          simpl.
          rewrite P4A.eq_dec_refl.
          simpl.
          rewrite P4A.eq_dec_refl.
          congruence.
        + simpl.
          destruct h.
          dependent destruction var.
          simpl in *.
          unfold P4A.find, P4A.assign.
          repeat match goal with
                 | H: context[ match ?e with _ => _ end ] |- _ => destruct e eqn:?
                 | |- context[ match ?e with _ => _ end ] => destruct e eqn:?
                 | |- _ => progress unfold "===" in *
                 | |- _ => progress simpl in *
                 | |- _ => progress subst
                 end;
            congruence.
      - reflexivity.
      - simpl.
        subst.
        erewrite IHphi; eauto.
        rewrite beslice_interp.
        reflexivity.
      - simpl.
        rewrite beconcat_interp.
        erewrite IHphi1, IHphi2; eauto.
    Qed.

    Lemma brand_interp:
      forall ctx (r1 r2: store_rel _ ctx) valu q1 q2,
        interp_store_rel (a:=a) (brand r1 r2) valu q1 q2 <->
        interp_store_rel (a:=a) (BRAnd r1 r2) valu q1 q2.
    Proof.
      intros.
      destruct r1, r2; simpl; tauto.
    Qed.

    Lemma bror_interp:
      forall ctx (r1 r2: store_rel _ ctx) valu q1 q2,
        interp_store_rel (a:=a) (bror r1 r2) valu q1 q2 <->
        interp_store_rel (a:=a) (BROr r1 r2) valu q1 q2.
    Proof.
      intros.
      destruct r1, r2; simpl; tauto.
    Qed.

    Lemma brimpl_interp:
      forall ctx (r1 r2: store_rel _ ctx) valu q1 q2,
        interp_store_rel (a:=a) (brimpl r1 r2) valu q1 q2 <->
        interp_store_rel (a:=a) (BRImpl r1 r2) valu q1 q2.
    Proof.
      intros.
      destruct r1, r2; simpl; tauto.
    Qed.

    Lemma sr_subst_hdr_left:
      forall c (valu: bval c) size (hdr: H size) exp phi c1 s1 st1 buf1 c2 (w: Ntuple.n_tuple bool size),
        conf_state c1 = s1 ->
        conf_store c1 = st1 ->
        conf_buf c1 = buf1 ->
        Ntuple.t2l w = interp_bit_expr exp valu c1 c2 ->
        interp_store_rel
          (a:=a)
          (WP.sr_subst phi exp (BEHdr c Left (P4A.HRVar (existT _ _ hdr))))
          valu
          c1
          c2 <->
        interp_store_rel
          (a:=a)
          phi
          valu
          (update_conf_store (a:=P4A.interp a)
                             (P4A.assign _ hdr (P4A.VBits size w) st1)
                             c1)
          c2.
    Proof.
      induction phi;
        simpl in *;
        erewrite ?brand_interp, ?bror_interp, ?brimpl_interp in *;
        repeat match goal with
               | |- forall _, _ => intro
               | |- _ /\ _ => split
               | |- _ <-> _ => split
               | H: _ /\ _ |- _ => destruct H
               | H: _ <-> _ |- _ => destruct H
               | |- _ => progress subst
               end;
        try erewrite ?brand_interp, ?bror_interp, ?brimpl_interp in *;
        simpl in *;
        try solve [erewrite !be_subst_hdr_left in *; eauto|intuition].
    Qed.

    Lemma sr_subst_hdr_right:
      forall c (valu: bval c) size (hdr: H size) exp phi c1 c2 s2 st2 buf2 (w: Ntuple.n_tuple bool size),
        conf_state c2 = s2 ->
        conf_store c2 = st2 ->
        conf_buf c2 = buf2 ->
        Ntuple.t2l w = interp_bit_expr exp valu c1 c2 ->
        interp_store_rel
          (a:=a)
          (WP.sr_subst phi exp (BEHdr c Right (P4A.HRVar (existT _ _ hdr))))
          valu
          c1
          c2 <->
        interp_store_rel
          (a:=a)
          phi
          valu
          c1
          (update_conf_store (a:=P4A.interp a)
                             (P4A.assign _ hdr (P4A.VBits size w) st2)
                             c2).
    Proof.
      induction phi;
        simpl in *;
        erewrite ?brand_interp, ?bror_interp, ?brimpl_interp in *;
        repeat match goal with
               | |- forall _, _ => intro
               | |- _ /\ _ => split
               | |- _ <-> _ => split
               | H: _ /\ _ |- _ => destruct H
               | H: _ <-> _ |- _ => destruct H
               | |- _ => progress subst
               end;
        try erewrite ?brand_interp, ?bror_interp, ?brimpl_interp in *;
        simpl in *;
        try solve [erewrite !be_subst_hdr_right in *; eauto|intuition].
    Qed.

    Lemma wp_op'_size:
      forall (c: bctx) si size (o: P4A.op H size) n phi m phi',
        WP.wp_op' (c:=c) si o (size + n, phi) = (m, phi') ->
        m = n.
    Proof.
      induction o; cbn; intros.
      - congruence.
      - destruct (WP.wp_op' si o2 (n1 + n2 + n, phi)) eqn:?.
        replace (n1 + n2 + n)
          with (n2 + (n1 + n))
          in *
          by Lia.lia.
        apply IHo2 in Heqp.
        subst n0.
        apply IHo1 in H0.
        eauto.
      - replace (projT1 hdr + n - projT1 hdr) with n in * by Lia.lia.
        congruence.
      - congruence.
    Qed.

    Lemma wp_op'_seq:
      forall (c: bctx) n1 n2 (o1: P4A.op H n1) (o2: P4A.op H n2) si phi,
        WP.wp_op' (c:=c) si (P4A.OpSeq o1 o2) phi = WP.wp_op' si o1 (WP.wp_op' si o2 phi).
    Proof.
      induction o1; intros; simpl;
        repeat match goal with
               | H:context [match ?x with _ => _ end] |- _ => destruct x eqn:?; simpl
               | |- context [match ?x with _ => _ end] => destruct x eqn:?; simpl
               | H: (_, _) = (_, _) |- _ => inversion H; clear H; subst
               end;
        reflexivity.
    Qed.

    Ltac break_match :=
      match goal with
      | |- context [match ?x with _ => _ end] =>
        destruct x eqn:?
      | H: context [match ?x with _ => _ end] |- _ =>
        destruct x eqn:?
      end.

    Lemma wp_op'_mono {k}:
      forall (c: bctx) si (o: P4A.op H k) n phi,
        fst (WP.wp_op' (c:=c) si o (n, phi)) <= n.
    Proof.
      induction o; simpl.
      - Lia.lia.
      - intros.
        destruct (WP.wp_op' si o2 _) as [m psi] eqn:?.
        specialize (IHo2 n phi).
        specialize (IHo1 m psi).
        rewrite Heqp in *.
        simpl in *.
        Lia.lia.
      - Lia.lia.
      - Lia.lia.
    Qed.

    Definition projbits {n} (v: P4A.v n) :=
      match v with
      | P4A.VBits _ vec => vec
      end.

    Lemma expr_to_bit_expr_sound:
      forall (c: bctx) si (valu: bval c) n (expr: P4A.expr H n) (c1 c2: conf),
        P4A.eval_expr (S1 + S2) H a n (conf_store (match si with Left => c1 | Right => c2 end)) expr =
        P4A.VBits n (interp_bit_expr (a:=a) (WP.expr_to_bit_expr si _) valu c1 c2).
    Proof.
      assert (Hv: forall v, P4A.VBits match v with P4A.VBits v' => v' end = v).
      {
        intros.
        destruct v; reflexivity.
      }
      induction expr; intros; cbn; auto.
      - destruct (P4A.eval_expr (snd (fst _))) eqn:?.
        unfold P4A.slice.
        specialize (IHexpr c1 c2).
        simpl in IHexpr.
        rewrite -> IHexpr in Heqv.
        congruence.
    Qed.

    Lemma n_slice_slice_eq:
      forall hi lo n (x: Ntuple.n_tuple bool n),
        Ntuple.t2l (WP.P4A.n_slice _ _ a x hi lo) = P4A.slice (Ntuple.t2l x) hi lo.
    Proof.
    Admitted.

    Lemma wp_op'_spec_l:
      forall c (valu: bval c) o n phi c1 s1 st1 buf1 c2,
        P4A.nonempty o ->
        conf_state c1 = s1 ->
        conf_store c1 = st1 ->
        conf_buf c1 = buf1 ->
        interp_store_rel (a:=a)
                         (snd (WP.wp_op' Left o (n + P4A.op_size o, phi)))
                         valu
                         c1
                         c2 <->
        interp_store_rel (a:=a)
                         phi
                         valu
                         (update_conf_store (fst (P4A.eval_op _ _ a _ _ st1 buf1 o)) c1)
                         c2.
    Proof.
      induction o.
      - intros.
        simpl.
        reflexivity.
      - intros.
        destruct H0.
        simpl (P4A.eval_op _ _ _ _).
        destruct (P4A.eval_op st1 n buf1 o1) as [st1' n'] eqn:?.
        destruct (P4A.eval_op st1' n' buf1 o2) as [st2' n''] eqn:?.
        pose proof (eval_op_size o1 _ _ _ _ _ Heqp).
        pose proof (eval_op_size o2 _ _ _ _ _ Heqp0).
        simpl (WP.wp_op' _ _ _).
        destruct (WP.wp_op' Left o2 (n + (P4A.op_size o1 + P4A.op_size o2), phi)) as [wn' phi'] eqn:?.
        assert (wn' = P4A.op_size o1 + n).
        {
          replace (n + (P4A.op_size o1 + P4A.op_size o2))
            with (P4A.op_size o2 + (P4A.op_size o1 + n))
            in Heqp1
            by Lia.lia.
          eapply wp_op'_size.
          eauto.
        }
        subst wn'.
        replace (P4A.op_size o1 + n)
          with (n + P4A.op_size o1)
          by Lia.lia.
        erewrite IHo1 by eauto.
        rewrite Heqp; simpl.
        replace st2' with (fst (P4A.eval_op st1' n' buf1 o2))
          by (rewrite Heqp0; reflexivity).
        replace phi' with (snd (WP.wp_op' Left o2 (n + (P4A.op_size o1 + P4A.op_size o2), phi)))
          by (rewrite Heqp1; reflexivity).
        rewrite Plus.plus_assoc.
        erewrite IHo2 by eauto.
        subst n'.
        rewrite Heqp0.
        reflexivity.
      - simpl.
        intros.
        rewrite sr_subst_hdr_left.
        simpl.
        replace (n + width - width) with n by Lia.lia.
        simpl.
        unfold P4A.slice.
        replace (1 + (n + width - 1)) with (n + width)
          by Lia.lia.
        erewrite <- firstn_skipn_comm.
        reflexivity.
      - simpl.
        unfold WP.wp_op, WP.wp_op'.
        simpl.
        intros.
        destruct lhs.
        rewrite sr_subst_hdr_left.
        simpl.
        rewrite <- expr_to_bit_expr_sound.
        reflexivity.
    Qed.

    (* This is basically a copy-pasted version of wp_op'_spec_l with
        some things flipped around. *)
    Lemma wp_op'_spec_r:
      forall c (valu: bval c) o n phi s2 st2 buf2 c1,
        P4A.nonempty o ->
        interp_store_rel (a:=a)
                         (snd (WP.wp_op' Right o (n + P4A.op_size o, phi)))
                         valu
                         c1
                         (s2, st2, buf2)
        <->
        interp_store_rel (a:=a)
                         phi
                         valu
                         c1
                         (s2,
                          fst (P4A.eval_op st2 n buf2 o),
                          buf2).
    Proof.
      induction o.
      - intros.
        simpl.
        reflexivity.
      - intros.
        destruct H0.
        simpl (P4A.eval_op _ _ _ _).
        destruct (P4A.eval_op st2 n buf2 o1) as [st2' n'] eqn:?.
        destruct (P4A.eval_op st2' n' buf2 o2) as [st2'' n''] eqn:?.
        pose proof (eval_op_size o1 _ _ _ _ _ Heqp).
        pose proof (eval_op_size o2 _ _ _ _ _ Heqp0).
        simpl (WP.wp_op' _ _ _).
        destruct (WP.wp_op' Right o2 (n + (P4A.op_size o1 + P4A.op_size o2), phi)) as [wn' phi'] eqn:?.
        assert (wn' = P4A.op_size o1 + n).
        {
          replace (n + (P4A.op_size o1 + P4A.op_size o2))
            with (P4A.op_size o2 + (P4A.op_size o1 + n))
            in Heqp1
            by Lia.lia.
          eapply wp_op'_size.
          eauto.
        }
        subst wn'.
        replace (P4A.op_size o1 + n)
          with (n + P4A.op_size o1)
          by Lia.lia.
        erewrite IHo1 by eauto.
        rewrite Heqp; simpl.
        replace st2'' with (fst (P4A.eval_op st2' n' buf2 o2))
          by (rewrite Heqp0; reflexivity).
        replace phi' with (snd (WP.wp_op' Right o2 (n + (P4A.op_size o1 + P4A.op_size o2), phi)))
          by (rewrite Heqp1; reflexivity).
        rewrite Plus.plus_assoc.
        erewrite IHo2 by eauto.
        subst n'.
        rewrite Heqp0.
        reflexivity.
      - simpl.
        intros.
        rewrite sr_subst_hdr_right.
        simpl.
        replace (n + width - width) with n by Lia.lia.
        simpl.
        unfold P4A.slice.
        replace (1 + (n + width - 1)) with (n + width)
          by Lia.lia.
        erewrite <- firstn_skipn_comm.
        reflexivity.
      - simpl.
        unfold WP.wp_op, WP.wp_op'.
        simpl.
        intros.
        destruct lhs.
        rewrite sr_subst_hdr_right.
        simpl.
        rewrite <- expr_to_bit_expr_sound.
        reflexivity.
    Qed.

    Definition pred_top {c} (p1 p2: WP.pred S1 S2 H c) : Prop :=
      forall q1 q2,
        match p1 with
        | WP.PredRead _ _ st =>
          interp_state_template st q1
        | WP.PredJump phi s =>
          fst (fst q1) = s
        end ->
        match p2 with
        | WP.PredRead _ _ st =>
          interp_state_template st q2
        | WP.PredJump phi s =>
          fst (fst q2) = s
        end ->
        top q1 q2.

    Lemma wp_pred_pair_step :
      forall C u v,
        SynPreSynWP.topbdd _ _ _ a top (interp_conf_rel C) ->
        (forall sl sr,
            pred_top sl sr ->
            interp_crel (a:=a) top (WP.wp_pred_pair a C (sl, sr)) u v) ->
        (forall b, interp_conf_rel C (step u b) (step v b)).
    Proof.
      intros.
      unfold WP.wp_pred_pair in *.
      destruct u as [[us ust] ubuf].
      destruct v as [[vs vst] vbuf].
      unfold interp_crel, interp_conf_rel, interp_conf_state, interp_state_template in * |-.
      destruct C as [[[Cst1 Clen1] [Cst2 Cbuf2]] Cctx Crel].
      unfold interp_conf_rel, interp_conf_state, interp_state_template.
      intros.
      simpl (st_state _) in *.
      simpl (st_buf_len _) in *.
      simpl (PreBisimulationSyntax.cr_st _) in *.
      simpl (PreBisimulationSyntax.cr_ctx _) in *.
      simpl (PreBisimulationSyntax.cr_rel _) in *.
      destruct H2 as [? [? [? [? [? ?]]]]].
      subst.
      unfold step; cbn.
      simpl in *.
      repeat match goal with
      | |- context [length (?x ++ [_])] =>
        replace (length (x ++ [_])) with (S (length x)) in *
          by (rewrite app_length; simpl; rewrite PeanoNat.Nat.add_comm; reflexivity)
      end.
      destruct vs as [vs | vs], us as [us | us]; simpl.
      simpl in * |-.
      destruct (equiv_dec (S (length ubuf)) (P4A.size a us)),
               (equiv_dec (S (length vbuf)) (P4A.size a vs)).
      - admit.
      - admit.
      - admit.
      - admit.
    Admitted.

    Lemma be_subst_buf_left:
      forall c (valu: bval c) exp phi c2 s1 st1 buf1 v,
        interp_bit_expr exp valu (s1, st1, buf1) c2 = v ->
        interp_bit_expr (a:=a) phi valu
                        (s1, st1, v)
                        c2
        =
        interp_bit_expr (WP.be_subst phi exp (BEBuf _ c Left))
                        valu
                        (s1, st1, buf1)
                        c2.
    Proof.
      induction phi; intros.
      - tauto.
      - unfold WP.be_subst.
        destruct (bit_expr_eq_dec _ _).
        + inversion e; clear e; subst.
          reflexivity.
        + simpl.
          unfold P4A.find, P4A.Env.find, P4A.assign.
          repeat match goal with
                 | H: context[ match ?e with _ => _ end ] |- _ => destruct e eqn:?
                 | |- context[ match ?e with _ => _ end ] => destruct e eqn:?
                 | |- _ => progress simpl in *
                 end;
            congruence.
      - unfold WP.be_subst.
        destruct (bit_expr_eq_dec _ _); try congruence.
        simpl.
        destruct a0; simpl;
          destruct (P4A.find _ _);
          reflexivity.
      - simpl.
        eauto.
      - simpl.
        rewrite beslice_interp.
        simpl.
        admit.
      - simpl.
        erewrite IHphi1, IHphi2; auto.
    Admitted.

    Lemma be_subst_buf_right:
      forall c (valu: bval c) exp phi c1 s2 st2 buf2 v,
        interp_bit_expr exp valu c1 (s2, st2, buf2) = v ->
        interp_bit_expr (a:=a) phi valu
                        c1
                        (s2, st2, v)
        =
        interp_bit_expr (WP.be_subst phi exp (BEBuf _ c Right))
                        valu
                        c1
                        (s2, st2, buf2).
    Proof.
      induction phi; intros.
      - tauto.
      - unfold WP.be_subst.
        destruct (bit_expr_eq_dec _ _).
        + inversion e; clear e; subst.
          reflexivity.
        + simpl.
          unfold P4A.find, P4A.Env.find, P4A.assign.
          repeat match goal with
                 | H: context[ match ?e with _ => _ end ] |- _ => destruct e eqn:?
                 | |- context[ match ?e with _ => _ end ] => destruct e eqn:?
                 | |- _ => progress simpl in *
                 end;
            congruence.
      - unfold WP.be_subst.
        destruct (bit_expr_eq_dec _ _); try congruence.
        simpl.
        destruct a0; simpl;
          destruct (P4A.find _ _);
          reflexivity.
      - simpl.
        eauto.
      - simpl.
        erewrite IHphi; eauto.
        admit.
      - simpl.
        erewrite IHphi1, IHphi2; auto.
        admit.
    Admitted.

    Lemma sr_subst_buf_left:
      forall c (valu: bval c) exp phi s1 st1 buf1 c2,
        interp_store_rel
          (a:=a)
          (WP.sr_subst phi exp (BEBuf _ c Left))
          valu
          (s1, st1, buf1)
          c2 <->
        interp_store_rel
          (a:=a)
          phi
          valu
          (s1,
           st1,
           interp_bit_expr exp valu (s1, st1, buf1) c2)
          c2.
    Proof.
      induction phi; simpl in *; try tauto; split; intros;
        rewrite ?brand_interp, ?bror_interp, ?brimpl_interp in *;
        try solve [erewrite <- ?be_subst_buf_left in *;
                   eauto
                  |simpl in *; intuition].
    Qed.

    Lemma sr_subst_buf_right:
      forall c (valu: bval c) exp phi c1 s2 st2 buf2,
        interp_store_rel
          (a:=a)
          (WP.sr_subst phi exp (BEBuf _ c Right))
          valu
          c1
          (s2, st2, buf2) <->
        interp_store_rel
          (a:=a)
          phi
          valu
          c1
          (s2,
           st2,
           interp_bit_expr exp valu c1 (s2, st2, buf2)).
    Proof.
      induction phi; simpl in *; try tauto; split; intros;
        rewrite ?brand_interp, ?bror_interp, ?brimpl_interp in *;
        try solve [erewrite <- ?be_subst_buf_right in *;
                   eauto
                  |simpl in *; intuition].
    Qed.

    Lemma interp_bit_expr_ignores_state:
      forall {c} (e: bit_expr H c) valu s1 st1 buf1 s2 st2 buf2 s1' s2',
        interp_bit_expr (a:=a) e valu (s1, st1, buf1) (s2, st2, buf2) =
        interp_bit_expr (a:=a) e valu (s1', st1, buf1) (s2', st2, buf2).
    Proof.
      induction e; intros.
      - reflexivity.
      - reflexivity.
      - simpl.
        destruct a0; simpl; reflexivity.
      - reflexivity.
      - simpl.
        erewrite IHe; eauto.
      - simpl.
        erewrite IHe1, IHe2; eauto.
    Qed.

    Lemma interp_store_rel_ignores_state:
      forall {c} (r: store_rel H c) valu s1 st1 buf1 s2 st2 buf2 s1' s2',
        interp_store_rel (a:=a) r valu (s1, st1, buf1) (s2, st2, buf2) ->
        interp_store_rel (a:=a) r valu (s1', st1, buf1) (s2', st2, buf2).
    Proof.
      induction r; intros; simpl in *; try solve [intuition eauto].
      erewrite (interp_bit_expr_ignores_state e1).
      erewrite (interp_bit_expr_ignores_state e2).
      eauto.
    Qed.

    Lemma wp_concrete_safe :
      SynPreSynWP.safe_wp_1bit _ _ _ a (WP.wp (H:=H)) top.
    Proof.
      unfold SynPreSynWP.safe_wp_1bit.
      intros.
      destruct q1 as [[st1 s1] buf1].
      destruct q2 as [[st2 s2] buf2].
      unfold WP.wp in * |-.
      destruct C.
      destruct a; simpl in * |-.
      destruct cr_st.
      unfold WP.wp in * |-.
      (*
either the step is a jump or a read on the left and on the right
so that's a total of 4 cases.
But in each case you need to massage the WP to line up with it,
because you're not branching on the same thing.
*)
      unfold step.
      unfold interp_conf_rel, interp_conf_state, interp_state_template; intros.
      simpl in *.
      intuition.
      simpl in *.
      repeat match goal with
      | |- context [length (?x ++ [_])] =>
        replace (length (x ++ [_])) with (S (length x)) in *
          by (rewrite app_length; simpl; rewrite PeanoNat.Nat.add_comm; reflexivity)
      end.
      destruct (equiv_dec (S (length buf1)) _), (equiv_dec (S (length buf2)) _);
        unfold "===" in *;
        simpl in *.
      - cbv in H0.
        destruct cs_st1 as [cst1 bl1] eqn:?, cs_st2 as [cst2 bl2] eqn:?.
        simpl in *.
        (* this is a real transition*)
        destruct st1 as [[st1 | ?] | st1], st2 as [[st2 | ?] | st2];
          try solve [cbv in H0; tauto].
        + simpl in *.
          admit.
          (* subst bl2.
          subst bl1.
          simpl in *. *)
          (* admit. *)
        + admit.
        + admit.
        + simpl in *.
          admit.
        + admit.
        + admit.
        + admit.
        + admit.
        + admit.
      - admit.
      - admit.
      - (* easiest case probably *)
        admit.
    Admitted.

    Lemma syn_pre_1bit_concrete_implies_sem_pre:
    forall R S q1 q2,
      SynPreSynWP.ctopbdd _ _ _ a top R ->
      SynPreSynWP.ctopbdd _ _ _ a top S ->
      SynPreSynWP.pre_bisimulation a (WP.wp (H:=H)) top R S q1 q2 ->
      SemPre.pre_bisimulation (P4A.interp a)
                              top
                              (map interp_conf_rel R)
                              (map interp_conf_rel S)
                              q1 q2.
    Proof.
      eauto using wp_concrete_safe, wp_concrete_bdd, SynPreSynWP.syn_pre_implies_sem_pre.
    Qed.
    *)

  End SynPreSynWP1bit.
End SynPreSynWP1bit.

Module SynPreSynWPSym.
  Section SynPreSynWPSym.
    (* State identifiers. *)
    Variable (S1: Type).
    Context `{S1_eq_dec: EquivDec.EqDec S1 eq}.
    Context `{S1_finite: @Finite S1 _ S1_eq_dec}.

    Variable (S2: Type).
    Context `{S2_eq_dec: EquivDec.EqDec S2 eq}.
    Context `{S2_finite: @Finite S2 _ S2_eq_dec}.

    (* Header identifiers. *)
    Variable (H: nat -> Type).
    Context `{H_eq_dec: forall n, EquivDec.EqDec (H n) eq}.
    Instance H'_eq_dec: EquivDec.EqDec (P4A.H' H) eq := P4A.H'_eq_dec (H_eq_dec:=H_eq_dec).
    Context `{H_finite: @Finite (Syntax.H' H) _ H'_eq_dec}.

    Variable (a: P4A.t (S1 + S2) H).

    Notation conf := (configuration (P4A.interp a)).
    Variable (top: rel conf).
    Variable (top_closed: forall x y b, top x y -> top (step x b) (step y b)).

    Lemma wp_sym_safe :
      SynPreSynWP.safe_wp_1bit _ _ _ a (WPSymBit.wp (H:=H)) top.
    Proof.
      unfold SynPreSynWP.safe_wp_1bit.
      intros.
    Admitted.

    Lemma wp_sym_bdd :
      SynPreSynWP.wp_bdd S1 S2 H a (WPSymBit.wp (H:=H)) top.
    Proof.
    Admitted.

    (*
    Lemma syn_pre_1bit_sym_implies_sem_pre:
    forall R S q1 q2,
      SynPreSynWP.ctopbdd _ _ _ a top R ->
      SynPreSynWP.ctopbdd _ _ _ a top S ->
      SynPreSynWP.pre_bisimulation a (WPSymBit.wp (H:=H)) top R S q1 q2 ->
      SemPre.pre_bisimulation (P4A.interp a)
                              top
                              (map interp_conf_rel R)
                              (map interp_conf_rel S)
                              q1 q2.
    Proof.
      eauto using wp_sym_safe, wp_sym_bdd, SynPreSynWP.syn_pre_implies_sem_pre.
    Qed.
    *)
  End SynPreSynWPSym.
End SynPreSynWPSym.

Module SynPreSynWPLeap.
End SynPreSynWPLeap.
