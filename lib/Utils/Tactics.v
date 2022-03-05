Require Import Coq.Setoids.Setoid.

Lemma drop_antecedent:
  forall P Q: Prop, P -> (P -> Q) <-> Q.
Proof.
  tauto.
Qed.

Lemma drop_antecedent_3:
  forall (A B C D : Prop),
  A ->
  B ->
  C ->
  (A -> B -> C -> D) <-> D.
Proof.
  intros.
  do 3 (erewrite drop_antecedent; eauto).
  eapply iff_refl.
Qed.
