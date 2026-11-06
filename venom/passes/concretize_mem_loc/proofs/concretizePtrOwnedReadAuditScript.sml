Theory concretizePtrOwnedReadAudit
Ancestors concretizePtrHistoricalWriteExclusion concretizePtrOperationalBytes
  concretizePtrActualByteFrame concretizePtrPairedPrefix
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrChronologicalHistory concretizePtrTokenInterval
  concretizePtrDemandWriteExclusion list rich_list arithmetic
  concretizePtrPairedFields concretizePtrPrefixLedger
  concretizePtrOwnedActualInitializer concretizePtrProtectedLivesets
  concretizePtrActiveWriteOwner concretizePtrMstoreProducer words
  venomCallOracleDefs extCallOracle venomState venomInst venomExecSemantics
  ptrDiscipline codegenRel copyFwdEquiv allocaRemapDefs finite_map
Libs wordsLib

val () = augment_srw_ss [wordsLib.SIZES_ss, wordsLib.WORD_GROUND_ss];

(* Diagnostic quotation only: this is NOT a theorem or an assumption. *)
val owned_read_recovery_candidate = ``
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  vs.vs_allocas = FEMPTY /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions /\
  EVERY wf_function C.ctx_functions /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  (!obs. MEM obs h ==> access_ok lo obs.po_prov obs.po_fn obs.po_inst obs.po_state) /\
  ~in_revert_forward endpoint.po_fn endpoint.po_state /\
  endpoint.po_inst.inst_opcode <> ASSIGN /\ d <= LENGTH endpoint.po_stack /\
  FLOOKUP (ptr_owner_view d endpoint).cf_state.vs_allocas aid = SOME (b,sz) /\
  lo <= b+k /\ k < sz /\ b+k NOTIN endpoint.po_taint.t_mem /\
  MEM (Var v) endpoint.po_inst.inst_operands /\
  (inst_read_op endpoint.po_inst = SOME (Var v) \/ endpoint.po_inst.inst_opcode = INVOKE) /\
  FLOOKUP endpoint.po_prov v = SOME (b,sz) /\
  fn = (ptr_owner_view d endpoint).cf_fn /\
  bp = bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn /\
  mems = (\nm. incr_ssort alloc_to (MAP FST (callee_mems_used observed.cu_context nm))) /\
  lookup_function fn.fn_name C.ctx_functions = SOME fn /\
  lookup_function fn.fn_name C'.ctx_functions = SOME out.fpo_function /\
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
  ctx_fn_names observed.cu_context = ctx_fn_names C /\
  o1_walk_view rpolicy 2 C' fn observed /\ EVERY fn_inst_wf C.ctx_functions /\
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

(* Historical former owner formula, before active-token membership was added.
   Predicate-level ambiguity only; not a reachable history or TASK counterexample. *)
Theorem audit_retained_write_owner_ambiguity:
  (!x:num. x IN {0} ==>
    (x < 0 /\ (\x:num. 200:num) x = x) \/
    (?token aid base sz pos k. k < sz /\ x = base + k /\ 200 = pos + k /\
      FLOOKUP (FEMPTY |+ ((0,10),(0,1)) |+ ((1,20),(0,1)))
        (token,aid) = SOME (base,sz) /\
      FLOOKUP (FEMPTY |+ (Allocation 10,(100,1)) |+ (Allocation 20,(200,1)))
        (Allocation aid) = SOME (pos,sz))) /\
  FLOOKUP (FEMPTY |+ ((0,10),(0,1)) |+ ((1,20),(0,1))) (0,10) = SOME (0,1) /\
  FLOOKUP (FEMPTY |+ (Allocation 10,(100,1)) |+ (Allocation 20,(200,1)))
    (Allocation 10) = SOME (100,1) /\
  (\x:num. 200:num) 0 <> 100
Proof
  simp[ptr_paired_write_owner_def, FLOOKUP_UPDATE] >>
  qexistsl [`1`,`20`,`1`] >> simp[]
QED

(* .40 proposed nonempty producer obligation only; not a proved theorem.
   The existential snapshot must be the actual source successor, not an
   independently supplied owner certificate. *)
val mstore_write_producer_candidate = ``
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
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
  a.po_inst.inst_opcode = MSTORE /\ ptr_chrono_step C' at zt ==>
  ?z snapshot reloc.
    ptr_structural_transcript R vs C C' (h ++ [z]) z (ht ++ [zt]) zt
      (done ++ [LENGTH h - 1]) tokens registry births PT TG saved entries
      (H ++ [snapshot]) /\
    ptr_paired_write lo positions C C' (h ++ [z]) (ht ++ [zt])
      (done ++ [LENGTH h - 1]) (H ++ [snapshot])
      (LENGTH h - 1,LENGTH done,reloc)``;

(* .46 missing semantic boundaries. Quotations only; no theorem is asserted. *)
val actual_chrono_byte_frame_candidate = ``
  !ctx a z x. ptr_chrono_step ctx a z /\
    x NOTIN range_bytes (step_writes a.po_inst a.po_state z.po_state) ==>
    read_byte x z.po_state.vs_memory = read_byte x a.po_state.vs_memory``;

val actual_interval_byte_frame_candidate = ``
  !vs ctx h endpoint x i j.
    ptr_chrono_history vs ctx h endpoint /\ i <= j /\ j < LENGTH h /\
    (!n. i <= n /\ n < j ==>
      x NOTIN range_bytes (step_writes (EL n h).po_inst (EL n h).po_state
        (EL (SUC n) h).po_state)) ==>
    read_byte x (EL j h).po_state.vs_memory =
      read_byte x (EL i h).po_state.vs_memory``;

val actual_writer_retention_candidate = ``
  !R vs C Ct h a ht at done tokens registry births PT TG saved entries w x.
    ptr_structural_trace R vs C Ct h a ht at done tokens registry births
      PT TG saved entries /\ SUC w < LENGTH h /\
    x IN range_bytes (step_writes (EL w h).po_inst (EL w h).po_state
      (EL (SUC w) h).po_state) ==>
    ?q. q < LENGTH done /\ EL q done = w``;

(* The supplied w is the SAME protected actual initializer. *)
Theorem ptr_paired_actual_protected_write_exclusion:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  vs.vs_allocas = FEMPTY /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions /\
  EVERY wf_function C.ctx_functions /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\
  (!obs. MEM obs h ==> access_ok lo obs.po_prov obs.po_fn obs.po_inst obs.po_state) /\
  ~in_revert_forward endpoint.po_fn endpoint.po_state /\
  endpoint.po_inst.inst_opcode <> ASSIGN /\ d <= LENGTH endpoint.po_stack /\
  FLOOKUP (ptr_owner_view d endpoint).cf_state.vs_allocas aid = SOME (b,sz) /\
  lo <= b+k /\ k < sz /\ b+k NOTIN endpoint.po_taint.t_mem /\
  MEM (Var v) endpoint.po_inst.inst_operands /\
  (inst_read_op endpoint.po_inst = SOME (Var v) \/ endpoint.po_inst.inst_opcode = INVOKE) /\
  FLOOKUP endpoint.po_prov v = SOME (b,sz) /\
  fn = (ptr_owner_view d endpoint).cf_fn /\
  bp = bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn /\
  mems = (\nm. incr_ssort alloc_to (MAP FST (callee_mems_used observed.cu_context nm))) /\
  lookup_function fn.fn_name C.ctx_functions = SOME fn /\
  lookup_function fn.fn_name C'.ctx_functions = SOME out.fpo_function /\
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
  ctx_fn_names observed.cu_context = ctx_fn_names C /\ o1_walk_view rpolicy 2 C' fn observed /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\ mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
  SUC w < LENGTH h /\
  b+k IN range_bytes (step_writes (EL w h).po_inst (EL w h).po_state
    (EL (SUC w) h).po_state) /\ b+k NOTIN (EL (SUC w) h).po_taint.t_mem /\
  (!n. w < n /\ SUC n < LENGTH h ==>
    b+k NOTIN range_bytes (step_writes (EL n h).po_inst (EL n h).po_state
      (EL (SUC n) h).po_state)) /\
  (!t. w < t /\ t < LENGTH h ==>
    ?xs. FLOOKUP (context_mem_livesets (concretize_memloc_fuel fn)
      observed.cu_context fn bp (cfg_analyze fn)) (Allocation aid) = SOME xs /\
      MEM ((ptr_owner_view d (EL t h)).cf_state.vs_current_bb,
           (ptr_owner_view d (EL t h)).cf_state.vs_inst_idx) xs) /\
  (!n. w <= n /\ n < LENGTH h ==>
    d <= LENGTH (EL n h).po_stack /\
    FLOOKUP (ptr_owner_view d (EL n h)).cf_state.vs_allocas aid = SOME (b,sz) /\
    ~in_revert_forward (EL n h).po_fn (EL n h).po_state) /\
  ml_used_gen (Allocation aid) bp mems (ptr_owner_view d (EL w h)).cf_inst /\
  ml_read_gen (Allocation aid) bp mems (ptr_owner_view d endpoint).cf_inst /\
  q < LENGTH done /\ w < EL q done ==>
  pa+k NOTIN range_bytes (step_writes (EL q ht).po_inst (EL q ht).po_state
    (EL (SUC q) ht).po_state)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_chrono_history_end >> strip_tac >>
  drule ptr_structural_transcript_endpoint >> strip_tac >>
  `LENGTH h-1 < LENGTH h /\ EL (LENGTH h-1) h = endpoint /\
   EL (LENGTH h-1) H = (tokens,registry,births,PT,TG,saved,entries)` by
    (Cases_on `h` >> Cases_on `H` >> gvs[LAST_EL]) >>
  qmatch_goalsub_abbrev_tac `step_writes ti ts tz` >>
  qabbrev_tac `token = EL (LENGTH endpoint.po_stack-d) tokens` >>
  `!j. w <= j /\ j < LENGTH h ==>
    EL (LENGTH (EL j h).po_stack-d) (FST (EL j H)) = token` by
    (`!j. w <= j /\ j <= LENGTH h-1 ==>
       ?tsj rj bj PTj TGj sj ej.
         EL j H = (tsj,rj,bj,PTj,TGj,sj,ej) /\
         EL (LENGTH (EL j h).po_stack-d) tsj = token` by
       (drule ptr_transcript_bottom_token_interval >>
        disch_then (qspecl_then [`w`,`LENGTH h-1`,`d`] mp_tac) >>
        simp[Abbr `token`]) >>
     rpt strip_tac >> first_x_assum (qspec_then `j` mp_tac) >>
     (impl_tac >- decide_tac) >> strip_tac >> simp[]) >>
  `ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w` by
    (simp[ptr_demand_interval_def, Abbr `token`, ADD1] >> metis_tac[]) >>
  unabbrev_all_tac >> drule_all ptr_paired_historical_owned_write_exclusion >> simp[]
QED
