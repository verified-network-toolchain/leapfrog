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

Require Import Leapfrog.Bisimulations.Semantic.
Require Import Leapfrog.Bisimulations.LeapsProofs.
Require Import Leapfrog.Bisimulations.WPLeapsProofs.

(* TODO: We need something like this for general sums of automata. Basically,
   if two states in the sum automaton have the same language, then those
   states have the same language in their original automaton. *)
Lemma sum_thing:
  forall (q1: IncrementalBits.state) (q2: BigBits.state),
    lang_equiv_state
      (a1 := P4A.interp A)
      (a2 := P4A.interp A)
      (inl q1)
      (inr q2) ->
    lang_equiv_state
      (a1 := P4A.interp IncrementalBits.aut)
      (a2 := P4A.interp BigBits.aut)
      q1
      q2.
Proof.
Admitted.

Lemma prebisim_incremental_sep:
  lang_equiv_state
    (a1 := P4A.interp IncrementalBits.aut)
    (a2 := P4A.interp BigBits.aut)
    IncrementalBits.Start
    BigBits.Parse
.
Proof.
  apply sum_thing.
  unfold lang_equiv_state.
  intros.
  match goal with
  | |- lang_equiv ?c1t ?c2t =>
    set (c1 := c1t);
    set (c2 := c2t)
  end.
  apply bisimilar_implies_equiv.
  apply bisimilar_iff_bisimilar_with_leaps.
  eapply wp_leaps_implies_bisim_leaps with
    (s1 := IncrementalBits.Start)
    (s2 := BigBits.Parse).
  2:{
    (* The second goal is fairly easy to discharge; this should be doable
       for proofs like this in general. *)
    unfold top.
    vm_compute r.
    subst c1.
    subst c2.
    vm_compute conf_to_state_template.
    do 6 right.
    left.
    reflexivity.
  }
  (* TODO Now how to handle the pre-bisimulation goal...? *)
Abort.

Lemma prebisim_incremental_sep:
  forall q1 q2,
    interp_conf_rel' {| cr_st := {|
                        cs_st1 := {|
                          st_state := inl (inl (IncrementalBits.Start));
                          st_buf_len := 0;
                        |};
                        cs_st2 := {|
                          st_state := inl (inr (BigBits.Parse));
                          st_buf_len := 0;
                        |};
                      |};
                      cr_ctx := BCEmp;
                      cr_rel := btrue;
                   |} q1 q2 ->
  pre_bisimulation A
                   r_states
                   (wp (a := A))
                   []
                   (mk_init _ _ _ _ A IncrementalBits.Start BigBits.Parse)
                   q1 q2.
Proof.
  idtac "running smallfilter bisimulation".

  intros.
  set (rel0 := (mk_init _ _ _ _ _ _ _)).
  vm_compute in rel0.
  subst rel0.

  (* This is broken now because of the imports above. *)
  (*
  time "build phase" repeat (time "single step" run_bisim).
  Fail time "close phase" close_bisim.
  *)
Abort.
