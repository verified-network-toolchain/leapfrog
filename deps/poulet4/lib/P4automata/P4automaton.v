From Equations Require Import Equations.
Require Import Coq.Lists.List.
Require Import Coq.Logic.JMeq.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Compare_dec.

Require Import Poulet4.Relations.
Require Import Poulet4.P4automata.Ntuple.

Record p4automaton := MkP4Automaton {
  store: Type;
  states: Type;
  size: states -> nat;
  update: forall (S: states), n_tuple bool (size S) -> store -> store;
  transitions: states -> store -> states + bool;
  cap: forall s, 0 < size s;
}.

Definition state_ref (a: p4automaton) : Type := states a + bool.

Equations size'
  (a: p4automaton)
  (s: state_ref a)
  : nat := {
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

Lemma cap' (a: p4automaton): forall s, 0 < size' a s.
Proof.
  destruct s; auto.
  rewrite size'_equation_1.
  apply cap.
Qed.

Record configuration (a: p4automaton) := MkConfiguration {
  conf_state: state_ref a;
  conf_buf_len: nat;
  conf_buf: n_tuple bool conf_buf_len;
  conf_buf_sane: conf_buf_len < size' a conf_state;
  conf_store: store a
}.

Arguments conf_state {a} _.
Arguments conf_buf_len {a} _.
Arguments conf_buf {a} _.
Arguments conf_buf_sane {a} _.
Arguments conf_store {a} _.

Definition update_conf_store {a} (v: store a) (c: configuration a) : configuration a :=
  {| conf_state := conf_state c;
     conf_buf_len := conf_buf_len c;
     conf_buf := conf_buf c;
     conf_buf_sane := conf_buf_sane c;
     conf_store := v |}.

Definition configuration_room_left {a: p4automaton} (c: configuration a) :=
  size' a c.(conf_state) - c.(conf_buf_len).

Definition configuration_has_room {a: p4automaton} (c: configuration a) :=
  c.(conf_buf_len) + 1 < size' a c.(conf_state).

Definition initial_configuration
  {a: p4automaton}
  (state: states a)
  (store: store a)
:= {|
  conf_state := inl state;
  conf_buf_len := 0;
  conf_buf := tt : n_tuple bool 0;
  conf_buf_sane := cap a state;
  conf_store := store
|}.

Lemma conf_buf_len_done
  {a: p4automaton}
  (q: configuration a)
  (b: bool)
:
  conf_state q = inr b ->
  conf_buf_len q = 0.
Proof.
  intros.
  destruct q.
  simpl in *.
  rewrite H in conf_buf_sane0.
  autorewrite with size' in conf_buf_sane0.
  lia.
Qed.

Lemma squeeze {n m}: n < m -> m <= 1+n -> 1+n = m.
Proof.
  lia.
Qed.

Definition step
  {a: p4automaton}
  (c: configuration a)
  (b: bool)
  : configuration a :=
  let buf_padded := n_tuple_cons (conf_buf c) b in
  match le_lt_dec (size' a (conf_state c)) (1 + conf_buf_len c) with
  | left Hle =>
    let buf_full := eq_rect _ _ buf_padded _ (squeeze (conf_buf_sane c) Hle) in
    let conf_store' := update' a (conf_state c) buf_full (conf_store c) in
    let conf_state' := transitions' a (conf_state c) conf_store' in
    {|
      conf_state := conf_state';
      conf_buf := tt : n_tuple bool 0;
      conf_buf_sane := cap' _ conf_state';
      conf_store := conf_store';
    |}
  | right conf_buf_sane' =>
    {|
      conf_state := conf_state c;
      conf_buf := buf_padded;
      conf_buf_sane := conf_buf_sane';
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
  destruct (le_lt_dec _ _).
  - cbn.
    match goal with
    | |- context [update' _ _ ?t _] =>
      generalize t; intros
    end.
    destruct (conf_state q); [discriminate|].
    now autorewrite with transitions'.
  - exfalso.
    rewrite H in l.
    autorewrite with size' in *.
    lia.
Qed.

Lemma conf_state_step_fill
  {a: p4automaton}
  (q: configuration a)
  (b: bool)
:
  conf_buf_len q + 1 < size' a (conf_state q) ->
  conf_state (step q b) = conf_state q
.
Proof.
  intros; unfold step.
  destruct (Compare_dec.le_lt_dec _ _); auto; lia.
Qed.

Lemma conf_buf_len_step_fill
  {a: p4automaton}
  (q: configuration a)
  (b: bool)
:
  conf_buf_len q + 1 < size' a (conf_state q) ->
  conf_buf_len (step q b) = conf_buf_len q + 1
.
Proof.
  intros; unfold step.
  destruct (Compare_dec.le_lt_dec _ _); simpl; lia.
Qed.

Lemma conf_buf_len_step_transition
  {a: p4automaton}
  (q: configuration a)
  (b: bool)
:
  conf_buf_len q + 1 = size' a (conf_state q) ->
  conf_buf_len (step q b) = 0
.
Proof.
  intros; unfold step.
  destruct (Compare_dec.le_lt_dec _ _); simpl; lia.
Qed.

Lemma conf_state_step_transition
  {a: p4automaton}
  (q: configuration a)
  (b: bool)
  (Heq: 1 + conf_buf_len q = size' a (conf_state q))
:
  let buf' := Ntuple.n_tuple_cons (conf_buf q) b in
  let store' := update' a
                        (conf_state q)
                        (eq_rect _ _ buf' _ Heq)
                        (conf_store q) in
  conf_state (step q b) = transitions' a (conf_state q) store'
.
Proof.
  unfold step; destruct (Compare_dec.le_lt_dec _ _); [simpl|Lia.lia].
  repeat f_equal.
  apply JMeq_eq.
  destruct Heq, (squeeze (conf_buf_sane q) l).
  apply JMeq_refl.
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
  conf_buf_len q + length bs < size' a (conf_state q) ->
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

Lemma conf_buf_len_follow_transition
  {a: p4automaton}
  (q: configuration a)
  (bs: list bool)
:
  conf_buf_len q + length bs = size' a (conf_state q) ->
  conf_buf_len (follow q bs) = 0
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

Lemma conf_buf_len_follow_fill
  {a: p4automaton}
  (q: configuration a)
  (bs: list bool)
:
  conf_buf_len q + length bs < size' a (conf_state q) ->
  conf_buf_len (follow q bs) = conf_buf_len q + length bs
.
Proof.
  revert q; induction bs; intros.
  - now autorewrite with follow.
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
  - now autorewrite with follow.
  - rewrite <- app_comm_cons.
    autorewrite with follow.
    now rewrite IHbuf.
Qed.

Lemma follow_done {a: p4automaton} (q: configuration a) (bs: list bool):
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

Definition rel a1 a2 := configuration a1 -> configuration a2 -> Prop.
