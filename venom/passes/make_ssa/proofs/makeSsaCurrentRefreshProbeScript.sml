Theory makeSsaCurrentRefreshProbe
Ancestors makeSsaCurrentCleanupRuntime venomExecSemantics venomState finite_map list

(* An abstract finite store segment, not a source reachability predicate.
   Every preservation obligation is explicit, including the destination. *)
Definition current_refresh_segment_def:
  (current_refresh_segment v x y [] a b a' b' <=> a' = a /\ b' = b) /\
  (current_refresh_segment v x y ((c,d)::rest) a b a' b' <=>
    lookup_var v c = lookup_var v a /\
    lookup_var y d = lookup_var y b /\
    lookup_var x d = lookup_var x b /\
    current_refresh_segment v x y rest c d a' b')
End

Theorem current_refresh_segment_lookups:
  !states a b a' b'. current_refresh_segment v x y states a b a' b' ==>
    lookup_var v a' = lookup_var v a /\
    lookup_var y b' = lookup_var y b /\
    lookup_var x b' = lookup_var x b
Proof
  Induct >- simp[current_refresh_segment_def] >>
  gen_tac >> PairCases_on `h` >> simp[current_refresh_segment_def] >> metis_tac[]
QED

Theorem current_cleanup_refresh:
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var y] /\
  inst.inst_outputs = [x] /\ lookup_var v a = SOME value /\
  lookup_var y b = SOME value ==>
  step_inst_base inst b = OK (update_var x value b) /\
  lookup_var x (update_var x value b) = SOME value /\
  lookup_var y (update_var x value b) = SOME value
Proof
  strip_tac >> drule_all current_cleanup_assign_step >>
  disch_then (qspec_then `b` mp_tac) >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  Cases_on `x = y` >> gvs[lookup_var_def]
QED

Theorem current_cleanup_refresh_return:
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var y] /\
  inst.inst_outputs = [x] /\ lookup_var v a = SOME value /\
  lookup_var y b = SOME value /\
  current_refresh_segment v x y states a (update_var x value b) a' b' ==>
  lookup_var v a' = SOME value /\ lookup_var x b' = SOME value /\
  lookup_var y b' = SOME value /\
  step_inst_base inst b' = OK (update_var x value b') /\
  lookup_var x (update_var x value b') = SOME value /\
  lookup_var y (update_var x value b') = SOME value
Proof
  strip_tac >> drule current_refresh_segment_lookups >> strip_tac >>
  `lookup_var x (update_var x value b) = SOME value /\
    lookup_var y (update_var x value b) = SOME value` by
    metis_tac[current_cleanup_refresh] >>
  metis_tac[current_cleanup_refresh]
QED

(* Stress tests: old refresh equality alone is not a return invariant. *)
Theorem current_refresh_copy_source_clobber:
  x <> y /\ value <> other ==>
  lookup_var x (update_var y other (update_var x value b)) = SOME value /\
  lookup_var y (update_var y other (update_var x value b)) = SOME other /\
  lookup_var x (update_var y other (update_var x value b)) <>
    lookup_var y (update_var y other (update_var x value b))
Proof
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem current_refresh_owner_clobber:
  value <> other ==>
  lookup_var v (update_var v other a) <>
    lookup_var x (update_var x value b)
Proof
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem current_refresh_destination_clobber:
  x <> y /\ lookup_var y b = SOME value /\ value <> other ==>
  lookup_var x (update_var x other b) <> lookup_var y (update_var x other b)
Proof
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

(* Companion static-interface audit (candidate obligations, NOT theorems).

   Established here: current_cleanup_refresh is the first non-self arrival
   boundary and also covers x=y. current_cleanup_refresh_return is the
   self-return boundary, CONDITIONAL on all three lookup preservations.
   The three clobber tests above show why none may just be omitted. In
   particular a body redefinition of v breaks an old refresh even if target
   x and y remain equal. These tests are not counterexamples to MakeSSA.

   Actual selector interface:
     current_certificate_inserted_edge_resolve identifies the incoming name
     as latest_current_name (current_event_exit_rs ev) v.
     current_certificate_inserted_replay_occurrence identifies the actual
     pre-cleanup PHI and its operand fold. current_phi_slots_assign_iff says
     FILTER (\n. n <> x) (MAP SND slots) is nonempty and constant for a
     collapsed copy; its head is y. Thus y <> x for an actual collapsed
     insertion, although the generic execution lemma does not need that.
     current_certificate_inserted_nonself_name gives SOME non-self CFG
     predecessor, not a non-self predecessor on every first execution path.
     Static events occur once in the dom walk; they are NOT dynamic visits.

   Exact proposed first-arrival signature, with a shared premise bundle P:
     P comprises current_structural_certificate s fn fn' s' A H events,
     all frozen source/supply hypotheses, entry_block fn = SOME eb,
     current_actual_inserted fn v h,
     current_token_name H (CurrentInserted v h) = SOME x,
     MEM ev events, current_event_label ev = before.vs_prev_bb,
     fn_cfg_edge fn before.vs_prev_bb h, before.vs_current_bb = h.

     P /\ fn_entry_state fn seed /\
     current_actual_prefix fn ctx (CurrentEntry fuel) seed phases
       (SOME (CurrentEntry rem)) (OK before) before /\
     (!phis. ~MEM (CurrentBatch h phis) phases) ==>
       latest_current_name (current_event_exit_rs ev) v <> x

   This is UNPROVED. In particular is_fn_path alone does not encode the
   no-prior-dispatch requirement. The actual_prefix formulation does, using
   CurrentBatch, and does not assume any target execution or availability.
   A demanded-only variant may be sufficient; removing the demand guard
   must be justified, not silently assumed.

   Exact source no-write candidate (P as above):
     P /\ start.vs_current_bb = h /\
     current_actual_prefix fn ctx (CurrentBody f bb) start phases
       (SOME (CurrentEntry rem)) (OK before) before /\
     lookup_block h fn.fn_blocks = SOME bb /\
     start.vs_inst_idx = phi_prefix_length bb.bb_instructions /\
     (!phis. ~MEM (CurrentBatch h phis) phases) /\
     latest_current_name (current_event_exit_rs ev) v = x ==>
       (!l i inst. MEM (CurrentOrdinary l i inst) phases ==>
          ~MEM v inst.inst_outputs) /\
       (!l phis inst. MEM (CurrentBatch l phis) phases /\ MEM inst phis ==>
          ~MEM v inst.inst_outputs)

   This is also UNPROVED and excludes retained same-header original PHIs
   from the segment by starting after the source PHI batch. Those PHIs
   must be handled by the separate retained-batch argument. Re-entry at h
   ends this epoch. A source definition on a return may instead force a
   non-self incoming name; that is a static exclusion to prove, not an
   operational fact supplied by current_refresh_segment.

   Exact target nonclobber output needed from a FUTURE occurrence-matching
   construction (no global matching construction is defined by this probe):
     current_semantic_history f ctx' target_phases b writes (OK b') b' ==>
       (!n value. MEM (n,value) writes ==> n <> x /\ n <> y)
   This implication needs premises relating target_phases to the actual
   source segment and certificate; on its own it is FALSE. Do not export
   it as a theorem with only the displayed antecedent. x requires unique
   allocation/ownership plus absence of a later h refresh. y additionally
   requires excluding executions of its defining original/inserted owner,
   INCLUDING cleanup writes for other insertions. The source no-write
   candidate by itself does not prove this exclusion for y.

   Alias closure warning: if another cleanup writes y <- z in this epoch,
   preserving x=y needs either no such write, or equality of x and z at
   that write (plus definedness of z). A value invariant must therefore be
   closed under these effective alias writes, or the certificate must rule
   them out. No broader alias-closure theorem is claimed by this probe.
   current_refresh_segment is intentionally a store predicate, not an
   execution relation. The next integration must derive it from actual
   paired execution, never insert it into source reachability constructors.
*)
