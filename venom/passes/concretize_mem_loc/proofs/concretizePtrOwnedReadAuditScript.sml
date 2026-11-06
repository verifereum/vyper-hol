Theory concretizePtrOwnedReadAudit
Ancestors concretizePtrHistoricalWriteExclusion concretizePtrOperationalBytes
  concretizePtrPairedFields concretizePtrPrefixLedger words
  venomCallOracleDefs extCallOracle venomState venomInst venomExecSemantics
  ptrDiscipline codegenRel copyFwdEquiv allocaRemapDefs finite_map
Libs wordsLib

val () = augment_srw_ss [wordsLib.SIZES_ss, wordsLib.WORD_GROUND_ss];

(* Diagnostic quotation only: this is NOT a theorem or an assumption. *)
val owned_read_recovery_candidate = ``
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w /\
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
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) ==>
  read_byte (b+k) endpoint.po_state.vs_memory =
    read_byte (pa+k) at.po_state.vs_memory``;

(* Conditional local probe: the oracle-selection equation is NOT discharged. *)
Theorem audit_call_clipped_byte:
  inst.inst_opcode = CALL /\
  inst.inst_operands = [g;ad;v;ao;az;ro;rz] /\
  inst.inst_outputs = [out] /\
  eval_operand g s = SOME gas /\ eval_operand ad s = SOME addr /\
  eval_operand v s = SOME value /\ eval_operand ao s = SOME aoff /\
  eval_operand az s = SOME asize /\ eval_operand ro s = SOME 0w /\
  eval_operand rz s = SOME 2w /\
  rq = venom_call_request s addr value aoff asize st /\
  take_outcome rq s.vs_outcomes = (outcome,rest) /\
  outcome.co_returnData = [byte] /\
  exec_ext_call inst s gas addr value aoff asize (0w:bytes32) (2w:bytes32) st = OK post ==>
  source_memory_write_ranges inst s = [(0,2)] /\
  step_writes inst s post = [(0,1)] /\
  1 IN range_bytes (source_memory_write_ranges inst s) /\
  1 NOTIN range_bytes (step_writes inst s post) /\
  read_byte 1 post.vs_memory = read_byte 1 s.vs_memory /\
  (1 IN (step_taint inst s post tn).t_mem <=> 1 IN tn.t_mem)
Proof
  strip_tac >>
  `post.vs_returndata = [byte] /\
   post.vs_memory = (write_memory_with_expansion 0 [byte] s).vs_memory /\
   post.vs_allocas = s.vs_allocas /\ post.vs_fmp = s.vs_fmp` by
    (gvs[exec_ext_call_def, consume_call_outcome_eq, update_var_def]) >>
  `source_memory_write_ranges inst s = [(0,2)]` by
    simp[source_memory_write_ranges_def] >>
  `step_writes inst s post = [(0,1)]` by simp[step_writes_def] >>
  simp[range_bytes_def] >>
  conj_tac
  >- (pure_rewrite_tac[read_byte_def, GSYM mem_byte_at_def] >>
      asm_rewrite_tac[] >> irule wmwe_byte_at_outside >> simp[]) >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def,
       written_taint_def, range_bytes_def, FLOOKUP_DEF] >> metis_tac[]
QED

(* Same antecedent as ptr_chrono_initializing_writer_seed; proposed stronger
   actual-byte selection conclusion. Quotation only, NOT a theorem. *)
val actual_initializer_candidate = ``
  ptr_chrono_history vs0 ctx h endpoint /\
  h = pre ++ [a] ++ tail /\ tail <> [] /\
  a.po_inst.inst_opcode = ALLOCA /\
  step_inst fuel ctx a.po_inst a.po_state = OK sa' /\
  x IN new_site_bytes a.po_state sa' /\ x NOTIN endpoint.po_taint.t_mem /\
  ptr_discipline lo ctx vs0 /\ lo <= x /\
  EVERY (\obs. ~in_revert_forward obs.po_fn obs.po_state) h /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) ctx.ctx_functions /\
  EVERY wf_function ctx.ctx_functions /\
  EVERY all_reachable ctx.ctx_functions /\
  EVERY ssa_form ctx.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) ctx.ctx_functions ==>
  ?k. LENGTH pre < k /\ SUC k < LENGTH h /\
    x IN range_bytes (step_writes (EL k h).po_inst (EL k h).po_state
      (EL (SUC k) h).po_state) /\
    x NOTIN (EL (SUC k) h).po_taint.t_mem``;

(* Predicate-level ambiguity only; not a reachable history or TASK counterexample. *)
Theorem audit_retained_write_owner_ambiguity:
  ptr_paired_write_owner 0
    (FEMPTY |+ (Allocation 10,(100,1)) |+ (Allocation 20,(200,1)))
    (\x. 200) {0}
    (tokens,registry,
     FEMPTY |+ ((0,10),(0,1)) |+ ((1,20),(0,1)),PT,TG,saved,entries) /\
  FLOOKUP (FEMPTY |+ ((0,10),(0,1)) |+ ((1,20),(0,1))) (0,10) = SOME (0,1) /\
  FLOOKUP (FEMPTY |+ (Allocation 10,(100,1)) |+ (Allocation 20,(200,1)))
    (Allocation 10) = SOME (100,1) /\
  (\x:num. 200:num) 0 <> 100
Proof
  simp[ptr_paired_write_owner_def, FLOOKUP_UPDATE] >>
  qexistsl [`1`,`20`,`1`] >> simp[]
QED
