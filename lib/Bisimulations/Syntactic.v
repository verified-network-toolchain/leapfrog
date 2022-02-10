Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.

Require Import Leapfrog.FinType.
Require Import Leapfrog.P4automaton.
Require Import Leapfrog.Syntax.
Require Import Leapfrog.Ntuple.

Require Leapfrog.Bisimulations.Semantic.

Section Syntactic.
  Variable (St1: Type).
  Context `{St1_eq_dec: EquivDec.EqDec St1 eq}.
  Context `{St1_finite: @Finite St1 _ St1_eq_dec}.

  Variable (St2: Type).
  Context `{St2_eq_dec: EquivDec.EqDec St2 eq}.
  Context `{St2_finite: @Finite St2 _ St2_eq_dec}.

  (* Header identifiers. *)
  Variable (Hdr1: Type).
  Variable (Hdr1_sz : Hdr1 -> nat).
  Context `{Hdr1_eq_dec: EquivDec.EqDec Hdr1 eq}.
  Context `{Hdr1_finite: @Finite Hdr1 _ Hdr1_eq_dec}.

  Variable (Hdr2: Type).
  Variable (Hdr2_sz : Hdr2 -> nat).
  Context `{Hdr2_eq_dec: EquivDec.EqDec Hdr2 eq}.
  Context `{Hdr2_finite: @Finite Hdr2 _ Hdr2_eq_dec}.

  Variable (a1: Syntax.t St1 Hdr1_sz).
  Variable (a2: Syntax.t St2 Hdr2_sz).

  Variable (Rstate: St1 -> St2 -> Prop).
  Variable (Rstore: store _ Hdr1_sz -> store _ Hdr2_sz -> Prop).

  Definition Rstate' (s1': state_ref St1) (s2': state_ref St2) :=
    match s1', s2' with
    | inl s1'', inl s2'' => Rstate s1'' s2''
    | inr b1, inr b2 => b1 = b2
    | _, _ => False
    end.

  Definition bisimulation :=
    (forall s1 s2, Rstate s1 s2 -> size a1 s1 = size a2 s2) /\
    (forall s1 s2 st1 st2,
      Rstate s1 s2 ->
      Rstore st1 st2 ->
      Rstate' (transitions _ _ _ a1 s1 st1) (transitions _ _ _ a2 s2 st2)).

  Definition concretize
    (c1: configuration (interp a1))
    (c2: configuration (interp a2))
  :=
    Rstate' c1.(conf_state) c2.(conf_state) /\
    Rstore c1.(conf_store) c2.(conf_store) /\
    { H : c1.(conf_buf_len) = c2.(conf_buf_len) &
      c1.(conf_buf) = rewrite_size H c2.(conf_buf) }
  .

  Lemma syntactic_to_semantic: bisimulation -> Semantic.bisimulation concretize.
  Proof.
    unfold bisimulation.
    intros.
    destruct H.
    unfold Semantic.bisimulation.
    intros.
    unfold concretize in *.
    split.
    destruct H1.
    unfold accepting.
    split; intros.
    rewrite H3 in H1.
    destruct (conf_state q2).
    contradiction.
    congruence.
    rewrite H3 in H1.
    destruct (conf_state q1).
    contradiction.
    congruence.
  Abort.

End Syntactic.
