(* A saved observer sees memory only below its own allocation frontier. *)
Theory readonlyInvokeCopyFwdCopyFrontier
Ancestors
  readonlyInvokeCopyFwdCopySteps readonlyInvokeCopyFwdMemory
  readonlyInvokeCopyFwdRel occurrenceGeometry regularCallEmitSim
  o1LowerDloadJointMemoryRead o1LowerDloadRangeTransport codegenRel
  taintAgree venomExecSemantics venomState
  finite_map list pred_set ptrDiscipline internalReturnCopyFwdSim words

(* A current-activation occurrence lies above every suspended observer cut. *)
Theorem ricf_copy_saved_observer_geometry:
  occurrence_natural_geometry lo a U B stk s /\
  FLOOKUP B id = SOME (db,z) /\ FST id = a ==>
  !j i. j < LENGTH stk /\ db <= i /\ i < db+len /\
    i < (EL j stk).cf_state.vs_alloca_next ==>
    i IN ircf_dead ids (EL j stk).cf_state (DROP (SUC j) stk)
Proof
  rw[occurrence_natural_geometry_def] >>
  `(EL j stk).cf_state.vs_alloca_next <= db` by metis_tac[] >>
  decide_tac
QED

(* The caller has no allocations; the callee owns the destination.  Its
   nonidentity copy is invisible to the caller even though it is not dead
   in that caller.  In particular full saved-dead containment is false. *)
Theorem ricf_nested_copy_frontier_probe:
  !s a D.
  let current = ricf_copy_probe_state s;
      saved = a with <| vs_allocas := FEMPTY; vs_alloca_next := 0;
                        vs_vars := FEMPTY; vs_params := [] |> in
  ricf_frame_agree D (ircf_dead {7} saved []) FEMPTY [] FEMPTY entry_taint
    (mcopy 0 1 1 (merge_callee_state saved current))
    (merge_callee_state saved current) /\
  ~({i | 0 <= i /\ i < 0+1} SUBSET ircf_dead {7} saved []) /\
  FLOOKUP current.vs_allocas 7 = SOME (0,1) /\
  read_byte 0 (mcopy 0 1 1 current).vs_memory = 9w /\
  read_byte 0 current.vs_memory = 7w
Proof
  rpt gen_tac >> simp_tac bool_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac `merge_callee_state saved current` >>
  `ricf_frame_agree D (ircf_dead {7} saved []) FEMPTY [] FEMPTY entry_taint
     (merge_callee_state saved current) (merge_callee_state saved current)` by
    (irule ricf_frame_agree_identity >>
     simp[taint_agree_def, o1LowerDloadSharedTheory.ld_shared_agree_refl,
       word_agree_except_def, merge_callee_state_def,
       Abbr `saved`]) >>
  conj_tac
  >- (match_mp_tac (ricf_frame_source_mcopy |>
        Q.INST [`tn` |-> `entry_taint`]) >>
      simp[Abbr `saved`, merge_callee_state_def, SUBSET_DEF,
           entry_taint_def, ricf_site_triples_def] >>
      fs[merge_callee_state_def]) >>
  simp[Abbr `saved`, Abbr `current`, ricf_copy_probe_state_def,
       ircf_dead_def, site_bytes_def, SUBSET_DEF, FLOOKUP_UPDATE,
       mcopy_def, write_memory_with_expansion_def, read_byte_def]
QED
