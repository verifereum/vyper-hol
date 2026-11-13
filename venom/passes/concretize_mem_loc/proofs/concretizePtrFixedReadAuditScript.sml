Theory concretizePtrFixedReadAudit
Ancestors concretizePtrOwnedReadAudit concretizePtrStageReserved
  concretizePtrExactWriteTransport concretizePtrHistoricalWriteClassification
  concretizePtrHistoryOrigin concretizePtrActiveWriteOwner
  concretizePtrActualByteFrame concretizePtrPairedFields
  ptrDiscipline list pred_set arithmetic finite_map

(* Diagnostic only. Each val is a parsed, typechecked HOL quotation, not
   an assertion, definition, axiom, or exported theorem.
   FixedReadRecovery now proves the endpoint candidate with the additional
   restrictions ~in_revert_forward endpoint.po_fn endpoint.po_state and
   endpoint.po_inst.inst_opcode <> ASSIGN. The unrestricted quote below
   remains an audit obligation, not a checked theorem. *)
val fixed_read_recovery_candidate = ``
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\
  x < lo /\ x NOTIN endpoint.po_taint.t_mem ==>
  read_byte x endpoint.po_state.vs_memory = read_byte x at.po_state.vs_memory``;

(* Finite maximum of ACTUAL source writes, with backward purity only
   along the actual-nonwrite suffix. No allocation birth is required. *)
val fixed_last_actual_writer_candidate = ``
  ptr_chrono_history vs C h endpoint /\ x NOTIN endpoint.po_taint.t_mem ==>
  ((!n. SUC n < LENGTH h ==>
      x NOTIN range_bytes (step_writes (EL n h).po_inst
        (EL n h).po_state (EL (SUC n) h).po_state)) \/
   (?w. SUC w < LENGTH h /\
     x IN range_bytes (step_writes (EL w h).po_inst
       (EL w h).po_state (EL (SUC w) h).po_state) /\
     x NOTIN (EL (SUC w) h).po_taint.t_mem /\
     (!n. w < n /\ SUC n < LENGTH h ==>
       x NOTIN range_bytes (step_writes (EL n h).po_inst
         (EL n h).po_state (EL (SUC n) h).po_state))))``;

(* This is a proposed geometry boundary, NOT a consequence of x<lo alone.
   Birth slices and all active frame lower bounds must be supplied from
   historical source ownership and ptr_discipline. *)
val fixed_write_owner_identity_candidate = ``
  ptr_paired_write_owner lo positions (reloc:num -> num) xs
    (tokens,registry,births,PT,TG,saved,entries) /\
  x IN xs /\ x < lo /\ ptr_birth_slices post tokens births /\
  LENGTH tokens = SUC (LENGTH post.po_stack) /\
  (!d. d <= LENGTH post.po_stack ==>
     allocas_from lo (ptr_owner_view d post).cf_state) ==>
  reloc x = x``;

(* FixedWriteReflection proves this conclusion with an additional disjunct:
   in_revert_forward at the matching source event. The stronger quotation
   below is not proved. FixedReadRecovery rules out that disjunct throughout
   an ordinary non-revert history before using reflection contrapositively.
   Ledger inclusion alone still does not give reflection. *)
val fixed_actual_write_reflection_candidate = ``
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ x < lo /\ q < LENGTH done /\
  x IN range_bytes (step_writes (EL q ht).po_inst
    (EL q ht).po_state (EL (SUC q) ht).po_state) ==>
  x IN range_bytes (step_writes (EL (EL q done) h).po_inst
    (EL (EL q done) h).po_state (EL (SUC (EL q done)) h).po_state)``;

(* Entry identity must follow from chronological entry semantics, not from
   the initial-sentinel theorem viewed as endpoint memory agreement. *)
val history_initial_memory_candidate = ``
  ptr_chrono_history vs C h endpoint ==>
  (HD h).po_state.vs_memory = vs.vs_memory``;
