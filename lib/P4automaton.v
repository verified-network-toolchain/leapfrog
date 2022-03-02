From Equations Require Import Equations.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Compare_dec.

Require Import Leapfrog.Relations.
Require Import Leapfrog.Ntuple.
Require Import Leapfrog.NtupleProofs.

Require Import Coq.Numbers.BinNums.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.

Record p4automaton := MkP4Automaton {
  store: Type;
  states: Type;
  size: states -> N;
  update: forall (S: states), n_tuple bool (size S) -> store -> store;
  transitions: states -> store -> states + bool;
  cap: forall s, (0 < size s)%N;
}.

Definition state_ref (a: p4automaton) : Type := states a + bool.

Equations size'
  (a: p4automaton)
  (s: state_ref a)
  : N := {
  size' a (inl s) := size a s;
  size' a (inr _) := 1
}.

Equations update'
  (a: p4automaton)
  (s: state_ref a)
  (buf: n_tuple bool (size' a s))
  (st: store a)
  : store a := {
  update' a (inl s) buf st := update a s buf st;
  update' a (inr _) _ st := st
}.

Equations transitions'
  (a: p4automaton)
  (s: state_ref a)
  (st: store a)
  : state_ref a := {
  transitions' a (inl s) st := transitions a s st;
  transitions' a (inr b) st := inr false
}.

Lemma cap' (a: p4automaton): forall s, (0 < size' a s)%N.
Proof.
  destruct s; autorewrite with size'.
  - eapply cap.
  - econstructor.
Qed.

Record configuration (a: p4automaton) := MkConfiguration {
  conf_state: state_ref a;
  conf_buf_len: N;
  conf_buf: n_tuple bool conf_buf_len;
  conf_buf_sane: (conf_buf_len < size' a conf_state)%N;
  conf_store: store a
}.

Arguments conf_state {a} _.
Arguments conf_buf_len {a} _.
Arguments conf_buf {a} _.
Arguments conf_buf_sane {a} _.
Arguments conf_store {a} _.

Definition config_wf {a} (c: configuration a) := n_tup_wf c.(conf_buf).

Definition update_conf_store {a} (v: store a) (c: configuration a) : configuration a :=
  {| conf_state := conf_state c;
     conf_buf_len := conf_buf_len c;
     conf_buf := conf_buf c;
     conf_buf_sane := conf_buf_sane c;
     conf_store := v |}.

Definition configuration_room_left {a: p4automaton} (c: configuration a) : N :=
  size' a c.(conf_state) - c.(conf_buf_len).

Definition configuration_has_room {a: p4automaton} (c: configuration a) :=
  (c.(conf_buf_len) + 1 < size' a c.(conf_state))%N.

Definition initial_configuration
  {a: p4automaton}
  (state: states a)
  (store: store a)
:= {|
  conf_state := inl state;
  conf_buf_len := 0;
  conf_buf := n_tuple_emp;
  conf_buf_sane := cap a state;
  conf_store := store
|}.

Lemma conf_buf_len_done
  {a: p4automaton}
  (q: configuration a)
  (b: bool)
:
  conf_state q = inr b ->
  conf_buf_len q = 0%N.
Proof.
  intros.
  destruct q.
  simpl in *.
  rewrite H in conf_buf_sane0.
  autorewrite with size' in conf_buf_sane0.
  lia.
Qed.

Lemma squeeze {n m}: (n < m -> m <= n+1 -> n+1 = m)%N.
Proof.
  lia.
Qed.

Ltac obl_tac := unfold complement, Equivalence.equiv; Tactics.program_simpl.

(* Local Obligation Tactic := intros. *)

Definition step
  {a: p4automaton}
  (c: configuration a)
  (b: bool)
  : configuration a :=
  let buf_padded : n_tuple bool (conf_buf_len c + 1) := n_tuple_snoc (conf_buf c) b in
  match (N.eq_dec (size' a (conf_state c)) (conf_buf_len c + 1))%N with
  | left H =>
    let buf_full := eq_rect _ _ buf_padded _ (squeeze (conf_buf_sane c) ltac:(lia)) in
    let conf_store' := update' a (conf_state c) buf_full (conf_store c) in
    let conf_state' := transitions' a (conf_state c) conf_store' in
    {|
      conf_state := conf_state';
      conf_buf := n_tuple_emp;
      conf_buf_sane := cap' _ conf_state';
      conf_store := conf_store';
    |}
  | right H => 
    {|
      conf_state := conf_state c;
      conf_buf := buf_padded;
      conf_buf_sane := ltac:(destruct c; simpl in *; lia);
      conf_store := conf_store c;
    |}
  end.

Lemma conf_state_step_done
  {a: p4automaton}
  (q: configuration a)
  (h b: bool)
:
  conf_state q = inr h ->
  conf_state (step q b) = inr false.
Proof.
  intros.
  unfold step.
  simpl.
  destruct (N.eq_dec _ _); simpl.
  - 
    match goal with
    | |- context [update' _ _ ?t _] =>
      generalize t; intros
    end.
    destruct (conf_state q); [discriminate|].
    now autorewrite with transitions'.
  - exfalso.
    destruct q; simpl in *.
    rewrite H in *.
    autorewrite with size' in *.
    lia.
Qed.

Ltac step_worker := intros; unfold step; destruct (N.eq_dec _ _); auto; lia.

Lemma conf_state_step_fill
  {a: p4automaton}
  (q: configuration a)
  (b: bool)
:
  (conf_buf_len q + 1 < size' a (conf_state q)) % N ->
  conf_state (step q b) = conf_state q
.
Proof.
  step_worker.
Qed.

Lemma conf_store_step_fill
  {a: p4automaton}
  (q: configuration a)
  (b: bool)
:
  (conf_buf_len q + 1 < size' a (conf_state q))%N ->
  conf_store (step q b) = conf_store q
.
Proof.
  step_worker.
Qed.

Lemma conf_buf_step_fill
  {a: p4automaton}
  (q: configuration a)
  (b: bool)
:
  (conf_buf_len q + 1 < size' a (conf_state q))%N ->
  (conf_buf (step q b)) = (n_tuple_snoc (conf_buf q) b).
Proof.
  step_worker.
Qed.

Lemma conf_buf_len_step_fill
  {a: p4automaton}
  (q: configuration a)
  (b: bool)
:
  (conf_buf_len q + 1 < size' a (conf_state q))%N ->
  (conf_buf_len (step q b) = conf_buf_len q + 1)%N
.
Proof.
  step_worker.
Qed.

Lemma conf_buf_len_step_transition
  {a: p4automaton}
  (q: configuration a)
  (b: bool)
:
  (conf_buf_len q + 1 = size' a (conf_state q))%N ->
  (conf_buf_len (step q b) = 0)%N
.
Proof.
  step_worker.
Qed.

Lemma conf_state_step_transition
  {a: p4automaton}
  (q: configuration a)
  (b: bool)
  (Heq: (conf_buf_len q + 1 = size' a (conf_state q))%N)
:
  let buf' := (n_tuple_snoc (conf_buf q) b) in
  let store' := update' a
                        (conf_state q)
                        (eq_rect _ _ buf' _ Heq)
                        (conf_store q) in
  conf_state (step q b) = transitions' a (conf_state q) store'
.
Proof.
  unfold step; destruct (N.eq_dec _ _); [simpl|Lia.lia].
  repeat f_equal.
  apply JMeq_eq.
  destruct Heq, (squeeze (conf_buf_sane q) _).
  apply JMeq_refl.
Qed.

Lemma update'_congr:
  forall a s buf st s' buf' st',
    s = s' ->
    buf ~= buf'  ->
    st = st' ->
    update' a s buf st = update' a s' buf' st'.
Proof.
  intros.
  subst.
  reflexivity.
Qed.

Lemma conf_store_step_transition
  {a: p4automaton}
  (q: configuration a)
  (b: bool)
:
  forall full_buf: n_tuple bool (size' a (conf_state q)),
    (conf_buf_len q + 1 = size' a (conf_state q))%N ->
    full_buf ~= (n_tuple_snoc (conf_buf q) b) ->
    conf_store (step q b) = update' a (conf_state q) full_buf (conf_store q).
Proof.
  intros; unfold step.
  destruct (N.eq_dec _ _); simpl; try lia.
  apply update'_congr; auto.

  destruct (squeeze _ _).
  simpl.
  eapply JMeq_sym.
  auto.
Qed.

Equations follow
  {a: p4automaton}
  (c: configuration a)
  (input: list bool)
  : configuration a := {
  follow c nil := c;
  follow c (b :: input) := follow (step c b) input
}.

Lemma conf_state_follow_fill
  {a: p4automaton}
  (q: configuration a)
  (bs: list bool)
:
  (conf_buf_len q + (N.of_nat (length bs)) < size' a (conf_state q))%N ->
  conf_state (follow q bs) = conf_state q
.
Proof.
  revert q; induction bs; intros.
  - now autorewrite with follow.
  - autorewrite with follow.
    simpl in H.
    rewrite IHbs.
    + apply conf_state_step_fill; auto; lia.
    + rewrite conf_state_step_fill, conf_buf_len_step_fill; lia.
Qed.

Lemma conf_store_follow_fill
  {a: p4automaton}
  (q: configuration a)
  (bs: list bool)
:
  (conf_buf_len q + (N.of_nat (length bs)) < size' a (conf_state q))%N ->
  conf_store (follow q bs) = conf_store q
.
Proof.
  revert q; induction bs; intros.
  - now autorewrite with follow.
  - autorewrite with follow.
    simpl in H.
    rewrite IHbs.
    + apply conf_store_step_fill; auto; lia.
    + rewrite conf_state_step_fill, conf_buf_len_step_fill; lia.
Qed.

Lemma conf_buf_follow_fill
  {a: p4automaton}
  (q: configuration a)
  (bs: list bool)
:
  (conf_buf_len q + (N.of_nat (length bs)) < size' a (conf_state q))%N ->
  (conf_buf (follow q bs)) ~= (n_tuple_concat (conf_buf q) (l2t bs))
.
Proof.
  revert q; induction bs; intros.
  - simpl in H; pose proof (conf_buf_sane q).
    simpl in *.
    autorewrite with follow.
    assert (t2l (conf_buf q) = t2l (n_tuple_concat (conf_buf q) n_tuple_emp)) by (
      erewrite t2l_concat; simpl; erewrite app_nil_r; trivial
    ).
 
    eauto using t2l_eq.
  - autorewrite with follow.
    simpl.
    specialize (IHbs (step q a0)).
    simpl in *.
    rewrite IHbs
      by (rewrite conf_buf_len_step_fill, conf_state_step_fill; lia).
    apply t2l_eq.
    erewrite t2l_concat.
    unfold l2t, t2l.
    unfold n_tuple_concat.
    assert (conf_buf (step q a0) = n_tuple_snoc (conf_buf q) a0) by (
      erewrite <- conf_buf_step_fill; trivial; lia
    ).
    erewrite H0.
    unfold n_tuple_snoc.
    erewrite <- app_assoc.
    trivial.
Qed.

Lemma conf_buf_len_follow_transition
  {a: p4automaton}
  (q: configuration a)
  (bs: list bool)
:
  (conf_buf_len q + (N.of_nat (length bs)) = size' a (conf_state q))%N ->
  conf_buf_len (follow q bs) = 0%N
.
Proof.
  revert q; induction bs; intros.
  - simpl in H; pose proof (conf_buf_sane q); lia.
  - destruct bs; simpl in *.
    + autorewrite with follow.
      apply conf_buf_len_step_transition; auto.
    + rewrite follow_equation_2; apply IHbs.
      rewrite conf_buf_len_step_fill, conf_state_step_fill; lia.
Qed.

Lemma conf_store_follow_transition
  {a: p4automaton}
  (q: configuration a)
  (bs: list bool)
:
  forall full_buf: n_tuple bool (size' a (conf_state q)),
    (conf_buf_len q + (N.of_nat (length bs)) = size' a (conf_state q))%N ->
    full_buf ~= n_tuple_concat (conf_buf q) (l2t bs) ->
    conf_store (follow q bs) = update' a (conf_state q) full_buf (conf_store q).
Proof.
  revert q; induction bs; intros.
  - simpl in H; pose proof (conf_buf_sane q); lia.
  - destruct bs; simpl in *.
    + autorewrite with follow.
      apply conf_store_step_transition; eauto.
    + erewrite follow_equation_2.
      assert (Hs: conf_state (step q a0) = conf_state q).
      {
        erewrite conf_state_step_fill; eauto.
        lia.
      }
      assert (Hst: conf_store (step q a0) = conf_store q).
      {
        erewrite conf_store_step_fill; eauto.
        lia.
      }
      assert (Hsz: size' a (conf_state (step q a0))
             = size' a (conf_state q))
        by (now rewrite Hs).
      erewrite (IHbs (step q a0) (rewrite_size Hsz full_buf)); eauto.
      * apply update'_congr; eauto using rewrite_size_jmeq.
      * rewrite Hsz.
        rewrite <- H.
        rewrite conf_buf_len_step_fill; lia.
      * assert (rewrite_size Hsz full_buf ~= full_buf) by eapply rewrite_size_jmeq.
        erewrite H1.
        unfold l2t in *.
        erewrite H0.
        unfold n_tuple_concat.

        assert (conf_buf (step q a0) = n_tuple_snoc (conf_buf q) a0) by (
          erewrite <- conf_buf_step_fill; trivial; lia
        ).
        erewrite H2.
        unfold n_tuple_snoc.
        erewrite <- app_assoc.
        reflexivity.
Qed.

Lemma conf_buf_len_follow_fill
  {a: p4automaton}
  (q: configuration a)
  (bs: list bool)
:
  (conf_buf_len q + (N.of_nat (length bs)) < size' a (conf_state q))%N ->
  (conf_buf_len (follow q bs) = conf_buf_len q + (N.of_nat (length bs)))%N
.
Proof.
  revert q; induction bs; intros.
  - simpl.
    autorewrite with follow.
    lia.
  - autorewrite with follow.
    simpl in *. rewrite IHbs.
    + rewrite conf_buf_len_step_fill; auto; simpl; lia.
    + rewrite conf_state_step_fill, conf_buf_len_step_fill; lia.
Qed.

Lemma follow_append
  {a: p4automaton}
  (c: configuration a)
  (buf: list bool)
  (b: bool):
  follow c (buf ++ [b]) = step (follow c buf) b.
Proof.
  revert c; induction buf; intros.
  - simpl.
    now autorewrite with follow.
  - rewrite <- app_comm_cons.
    autorewrite with follow.
    now rewrite IHbuf.
Qed.

Lemma follow_step {a: p4automaton} (q: configuration a) (bs: list bool):
  conf_state q = inr false ->
  conf_state (follow q bs) = inr false.
Proof.
  revert q; induction bs; intros.
  - now autorewrite with follow.
  - autorewrite with follow.
    apply IHbs.
    eapply conf_state_step_done.
    exact H.
Qed.

Lemma follow_done {a: p4automaton} (q: configuration a) (bs: list bool):
  conf_state q = inr false ->
  conf_state (follow q bs) = inr false.
Proof.
  revert q; induction bs; intros.
  - now autorewrite with follow.
  - autorewrite with follow.
    assert (Hst: conf_state (step q a0) = inr false)
      by (eapply conf_state_step_done; eauto).
    eapply IHbs.
    eauto.
Qed.

Lemma follow_finish {a: p4automaton} (q: configuration a) (bs: list bool):
  forall b,
    length bs > 0 ->
    conf_state q = inr b ->
    conf_state (follow q bs) = inr false.
Proof.
  cut (forall b,
          conf_state q = inr b ->
          conf_state (follow q bs) =
          match bs with
          | [] => inr b
          | _ => inr false
          end).
  {
    intros.
    destruct bs; eauto.
    simpl in *.
    Lia.lia.
  }
  revert q; induction bs; intros.
  - now autorewrite with follow.
  - autorewrite with follow.
    assert (Hst: conf_state (step q a0) = inr false)
      by (eapply conf_state_step_done; eauto).
    specialize (IHbs (step q a0) _ Hst).
    rewrite IHbs.
    destruct bs; reflexivity.
Qed.

Lemma conf_state_follow_transition
  {a: p4automaton}
  (q: configuration a)
  (bs: list bool)
  (s: states a)
:
  conf_state q = inl s ->
  (conf_buf_len q + (N.of_nat (length bs)) = size' a (conf_state q))%N ->
  conf_state (follow q bs) = transitions' a (inl s) (conf_store (follow q bs)).
Proof.
  revert q.
  induction bs; intros; autorewrite with follow.
  - simpl in *.
    pose proof (conf_buf_sane q).
    rewrite H in *.
    lia.
  - destruct bs.
    + simpl in *.
      autorewrite with follow.
      unfold step.
      destruct (N.eq_dec _ _); try lia.
      simpl.
      congruence.
    + assert ((conf_buf_len q + 1 < size' a (conf_state q))%N)
        by (simpl in *; lia).
      eapply IHbs.
      * rewrite conf_state_step_fill by auto.
        congruence.
      * rewrite conf_buf_len_step_fill by eauto.
        rewrite conf_state_step_fill by auto.
        simpl in *.
        lia.
Qed.

Definition accepting
  {a: p4automaton}
  (c: configuration a)
  : Prop
:=
  conf_state c = inr true
.

Definition accepted
  {a: p4automaton}
  (c: configuration a)
  (input: list bool)
  : Prop
:=
  accepting (follow c input)
.

Definition lang_equiv
  {a1 a2: p4automaton}
  (c1: configuration a1)
  (c2: configuration a2)
:=
  forall input,
    accepted c1 input <->
    accepted c2 input
.

Definition lang_equiv_state
  (a1 a2: p4automaton)
  (q1: states a1)
  (q2: states a2)
:=
  forall s1 s2,
    lang_equiv
      {| conf_state := inl q1;
         conf_buf_len := 0;
         conf_buf := n_tuple_emp;
         conf_store := s1;
         conf_buf_sane := cap a1 q1; |}
      {| conf_state := inl q2;
         conf_buf_len := 0;
         conf_buf := n_tuple_emp;
         conf_store := s2;
         conf_buf_sane := cap a2 q2; |}
.

Definition rel a1 a2 := configuration a1 -> configuration a2 -> Prop.
