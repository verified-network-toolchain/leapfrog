Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.SloppyStrict.

Notation H := (Sloppy.header + Strict.header).
Notation A := SloppyStrict.aut.
Notation conf := (P4automaton.configuration (P4A.interp A)).
Notation start_left := (Sloppy.ParseEthernet).
Notation start_right := (Strict.ParseEthernet).

Definition r_states : {r : Reachability.state_pairs A & Reachability.reachable_states_wit start_left start_right r}.
  econstructor.
  unfold Reachability.reachable_states_wit.
  solve_fp_wit.
Defined.

Lemma init_states_wf:
  Reachability.valid_state_pair (Reachability.build_state_pair A start_left start_right).
Proof.
  vm_compute; Lia.lia.
Qed.

Declare ML Module "mirrorsolve".

Definition not_equally_accepting (s: Reachability.state_pair A) : bool :=
  let '(s1, s2) := s in
  match s1.(st_state), s2.(st_state) with
  | inr true, inr true => false
  | inr true, _ => true
  | _, inr true => true
  | _, _ => false
  end.

Definition mk_rel '((s1, s2): Reachability.state_pair A)
  : conf_rel A :=
  {| cr_st := {| cs_st1 := s1;
                  cs_st2 := s2 |};
      cr_ctx := BCEmp;
      cr_rel := BRImpl
                    (BROr (BREq (BESlice (BEHdr _ Left (P4A.HRVar (inl Sloppy.HdrEthernet))) 111 96)
                                  (BELit _ _ [true; false; false; false;
                                          false; true; true; false;
                                          false; false; false; false;
                                          false; false; false; false]))
                          (BREq (BESlice (BEHdr _ Left (P4A.HRVar (inl Sloppy.HdrEthernet))) 111 96)
                                  (BELit _ _ [true; false; false; false;
                                          false; true; true; false;
                                          true; true; false; true;
                                          true; true; false; true])))
                    bfalse
      |}.

Definition mk_partition (r: Reachability.state_pairs A) : crel A :=
  List.map mk_rel (List.filter not_equally_accepting r).

Definition mk_init' s1 s2 :=
  List.nodup (@conf_rel_eq_dec _ _ _ _ _ _ _ _ A)
              (mk_partition (Reachability.reachable_states A s1 s2)).

Lemma prebisim_sloppystrict_filtering:
  forall q1 q2,
    interp_conf_rel' {| cr_st := {|
                        cs_st1 := {|
                          st_state := inl (inl (Sloppy.ParseEthernet));
                          st_buf_len := 0;
                        |};
                        cs_st2 := {|
                          st_state := inl (inr (Strict.ParseEthernet));
                          st_buf_len := 0;
                        |};
                      |};
                      cr_ctx := BCEmp;
                      cr_rel := btrue;
                   |} q1 q2 ->
  pre_bisimulation A
                   (projT1 r_states)
                   (wp (a := A))
                   []
                   (mk_init' start_left start_right)
                   q1 q2.

Proof.
  idtac "running sloppystrict bisimulation (language equivalence modulo filtering)".

  intros.

  pose proof (Reachability.reachable_states_wit_conv init_states_wf (projT2 r_states)) as Hr.

  unfold mk_init'.
  rewrite Hr.
  clear Hr.

  set (foo := (List.nodup (conf_rel_eq_dec (a:=A)) (mk_partition _))).
  vm_compute in foo.
  subst foo.

  time "build phase"
       repeat (time "single step" run_bisim_axiom Sloppy.state_eqdec Strict.state_eqdec false).
  time "close phase" close_bisim_axiom.
Time Qed.