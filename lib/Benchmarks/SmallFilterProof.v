Require Import Leapfrog.Bisimulations.Semantic.
Require Import Leapfrog.Bisimulations.LeapsProofs.
Require Import Leapfrog.Bisimulations.WPLeapsProofs.
Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.SmallFilter.


Notation H := (IncrementalBits.header + BigBits.header).
Notation A := IncrementalSeparate.aut.
Notation conf := (P4automaton.configuration (P4A.interp A)).

Definition r_states :=
  Eval vm_compute in (Reachability.reachable_states
                        IncrementalSeparate.aut
                        IncrementalBits.Start
                        BigBits.Parse).

Declare ML Module "mirrorsolve".

(*
RegisterEnvCtors
  (IncrementalBits.Pref, FirstOrderConfRelSimplified.Bits 1)
  (IncrementalBits.Suf, FirstOrderConfRelSimplified.Bits 1)
  (BigBits.Pref, FirstOrderConfRelSimplified.Bits 1)
  (BigBits.Suf, FirstOrderConfRelSimplified.Bits 1).
*)


Lemma prebisim_incremental_sep:
  lang_equiv_state
    (P4A.interp IncrementalBits.aut)
    (P4A.interp BigBits.aut)
    IncrementalBits.Start
    BigBits.Parse
.
Proof.
  eapply Sum.sum_thing; [typeclasses eauto | typeclasses eauto |].
  unfold lang_equiv_state.
  intros.
  match goal with
  | |- lang_equiv ?c1t ?c2t =>
    set (cr0 := {| cr_st :=
                     {| cs_st1 := conf_to_state_template (a:=A) c1t;
                        cs_st2 := conf_to_state_template (a:=A) c2t; |};
                   cr_ctx := BCEmp;
                   cr_rel := btrue; |});
      unfold conf_to_state_template in cr0; simpl in cr0;
      set (c1 := c1t);
      set (c2 := c2t)
  end.
  assert (interp_conf_rel' cr0 c1 c2).
  {
    unfold interp_conf_rel'.
    cbv; intuition.
    autorewrite with interp_store_rel.
    tauto.
  }
  generalize dependent c1.
  generalize dependent c2.
  subst cr0.
  intros.
  apply bisimilar_implies_equiv.
  apply bisimilar_iff_bisimilar_with_leaps.
  eapply wp_leaps_implies_bisim_leaps with
    (s1 := IncrementalBits.Start)
    (s2 := BigBits.Parse).
  2:{
    (* The second goal is fairly easy to discharge; this should be doable
       for proofs like this in general. *)
    unfold WPLeapsProofs.top.
    vm_compute Reachability.reachable_states.
    inversion H.
    inversion H0.
    erewrite !Reachability.interp_state_template_definite by eauto.
    vm_compute conf_to_state_template.
    do 6 right.
    left.
    reflexivity.
  }
  vm_compute Reachability.reachable_states.
  vm_compute mk_init.
  time "build phase" repeat (time "single step" run_bisim).
  time "close phase" close_bisim.
  (* TODO Now how to handle the pre-bisimulation goal...? *)
Admitted.
