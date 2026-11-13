Theory concretizePtrOwnedReadAudit
Ancestors concretizePtrHistoricalWriteExclusion concretizePtrOperationalBytes
  concretizePtrActualByteFrame concretizePtrPairedPrefix
  concretizePtrOperationalOpcodes pred_set
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrChronologicalHistory concretizePtrTokenInterval
  concretizePtrDemandWriteExclusion list rich_list arithmetic
  concretizePtrPairedFields concretizePtrPrefixLedger
  concretizePtrOwnedActualInitializer concretizePtrProtectedLivesets
  concretizePtrActiveWriteOwner concretizePtrMstoreProducer words
  concretizePtrSourceOwnership concretizePtrActivationBirths
  concretizePtrActivationChronology concretizePtrAllocationOwnership
  venomCallOracleDefs extCallOracle venomState venomInst venomExecSemantics
  ptrDiscipline codegenRel copyFwdEquiv allocaRemapDefs finite_map
Libs wordsLib

val () = augment_srw_ss [wordsLib.SIZES_ss, wordsLib.WORD_GROUND_ss];

Theorem ptr_paired_owned_read_recovery:
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
    read_byte (pa+k) at.po_state.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  `b <= b+k /\ b+k < b+sz` by decide_tac >>
  drule_all ptr_endpoint_actual_protected_livesets >> strip_tac >>
  `SUC w < LENGTH h` by decide_tac >>
  drule ptr_structural_trace_actual_writer_retained >>
  disch_then (qspecl_then [`w`,`b+k`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `ptr_observation_reachable vs C (EL w h)` by
    (drule ptr_chrono_history_reachable >> simp[EVERY_EL] >>
     strip_tac >> first_x_assum irule >> decide_tac) >>
  `(EL w h).po_inst.inst_opcode <> DRET` by
    (irule ptr_stage_observation_no_dret >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `~is_terminator (EL w h).po_inst.inst_opcode /\
   (EL w h).po_inst.inst_opcode <> INVOKE` by
    (qpat_assum `(EL w h).po_inst.inst_opcode <> DRET` mp_tac >>
     Cases_on `(EL w h).po_inst.inst_opcode` >>
     simp[is_terminator_def] >>
     qpat_x_assum `b+k IN range_bytes _` mp_tac >>
     qpat_assum `(EL w h).po_inst.inst_opcode = _`
       (fn th => simp_tac (srw_ss())
         [th,step_writes_def,source_memory_write_ranges_def,range_bytes_def]) >>
     qpat_x_assum `DRET <> DRET` mp_tac >> simp[]) >>
  drule ptr_paired_prefix_writes >> strip_tac >>
  `?rho. MEM (w,q,rho) ws` by
    (qpat_assum `ptr_paired_writes _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ptr_paired_writes_def] >> strip_tac >>
     first_x_assum (qspec_then `q` mp_tac) >>
     asm_rewrite_tac[] >>
     `range_bytes (step_writes (EL w h).po_inst (EL w h).po_state
       (EL (SUC w) h).po_state) <> {}` by metis_tac[NOT_IN_EMPTY] >>
     metis_tac[]) >>
  drule_all ptr_paired_write_event >>
  simp[ptr_paired_write_def] >> strip_tac >>
  drule ptr_structural_transcript_ownership >>
  disch_then (qspec_then `SUC w` mp_tac) >> simp[] >>
  qabbrev_tac `snap = EL (SUC w) H` >> PairCases_on `snap` >>
  simp[ptr_snapshot_ownership_def] >> strip_tac >>
  drule ptr_source_ownership_caches >> strip_tac >>
  drule_all ptr_source_birth_caches_slices >> strip_tac >>
  drule ptr_source_birth_caches_activations >> strip_tac >>
  drule ptr_source_activations_length >> strip_tac >>
  `ptr_observation_reachable vs C (EL (SUC w) h)` by
    (drule ptr_chrono_history_reachable >> simp[EVERY_EL] >>
     strip_tac >> first_x_assum irule >> decide_tac) >>
  `ptr_active_alloc_geometry ((EL (SUC w) h).po_state ::
      MAP (\f. f.cf_state) (EL (SUC w) h).po_stack)` by
    (irule ptr_frame_alloc_geometry >>
     qpat_x_assum `ptr_observation_reachable vs C (EL (SUC w) h)` mp_tac >>
     simp[ptr_observation_reachable_def] >> metis_tac[]) >>
  `d <= LENGTH (EL (SUC w) h).po_stack /\
   FLOOKUP (ptr_owner_view d (EL (SUC w) h)).cf_state.vs_allocas aid = SOME (b,sz)` by
    (qpat_x_assum `!n. w <= n /\ n < LENGTH h ==> _` (qspec_then `SUC w` mp_tac) >>
     simp[]) >>
  `rho' (b+k) = pa+k` by
    (drule_all ptr_paired_write_owner_relocation >> simp[]) >>
  `read_byte (b+k) (EL (SUC w) h).po_state.vs_memory =
   read_byte (pa+k) (EL (SUC q) ht).po_state.vs_memory` by
    (qpat_x_assum `ptr_ledger_write_pair _ _ _ _ _ _ _` mp_tac >>
     simp[ptr_ledger_write_pair_def, concretizePtrBytesTheory.ptr_bytes_agree_def] >>
     strip_tac >> first_x_assum (qspec_then `b+k` mp_tac) >> simp[]) >>
  drule ptr_chrono_history_end >> strip_tac >>
  `LENGTH h-1 < LENGTH h /\ EL (LENGTH h-1) h = endpoint` by
    (Cases_on `h` >> gvs[LAST_EL]) >>
  `read_byte (b+k) endpoint.po_state.vs_memory =
   read_byte (b+k) (EL (SUC w) h).po_state.vs_memory` by
    (`read_byte (b+k) (EL (LENGTH h-1) h).po_state.vs_memory =
      read_byte (b+k) (EL (SUC w) h).po_state.vs_memory` suffices_by simp[] >>
     irule ptr_chrono_history_actual_interval_byte_frame >>
     conj_tac >- (rpt gen_tac >> strip_tac >>
       qpat_x_assum `!n. w < n /\ n+1 < LENGTH h ==> _`
         (qspec_then `k'` mp_tac) >> simp[] >> decide_tac) >>
     simp[] >> metis_tac[]) >>
  suspend "target_frame"
QED

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

Resume ptr_paired_owned_read_recovery[target_frame]:
  drule ptr_structural_trace_target >> strip_tac >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  `!j. q < j /\ j < LENGTH done ==> w < EL j done` by
    (qpat_x_assum `ptr_event_embedding _ _ _` mp_tac >>
     pure_rewrite_tac[concretizePtrEventEmbeddingTheory.ptr_event_embedding_def] >>
     strip_tac >> rpt strip_tac >>
     first_x_assum (qspecl_then [`q`,`j`] mp_tac) >>
     simp[EL_APPEND_EQN]) >>
  `!j. SUC q <= j /\ j < LENGTH ht-1 ==>
    pa+k NOTIN range_bytes (step_writes (EL j ht).po_inst
      (EL j ht).po_state (EL (SUC j) ht).po_state)` by
    (rpt gen_tac >> strip_tac >>
     `j < LENGTH done /\ w < EL j done` by
       (conj_tac >- decide_tac >> first_x_assum irule >> decide_tac) >>
     irule ptr_paired_actual_protected_write_exclusion >>
     goal_assum (drule_at (Pat `ptr_paired_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `FLOOKUP positions (Allocation _) = _`)) >>
     goal_assum (drule_at (Pat `FLOOKUP (ptr_owner_view _ endpoint).cf_state.vs_allocas _ = _`)) >>
     goal_assum (drule_at (Pat `fn_pass_step _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `ml_used_gen _ _ _ _`)) >>
     simp[ADD1] >> metis_tac[]) >>
  drule ptr_chrono_history_end >> strip_tac >>
  `LENGTH ht-1 < LENGTH ht /\ EL (LENGTH ht-1) ht = at` by
    (Cases_on `ht` >> gvs[LAST_EL]) >>
  `read_byte (pa+k) at.po_state.vs_memory =
   read_byte (pa+k) (EL (SUC q) ht).po_state.vs_memory` by
    (`read_byte (pa+k) (EL (LENGTH ht-1) ht).po_state.vs_memory =
      read_byte (pa+k) (EL (SUC q) ht).po_state.vs_memory` suffices_by simp[] >>
     irule ptr_chrono_history_actual_interval_byte_frame >>
     conj_tac >- simp[] >> simp[] >> metis_tac[]) >>
  metis_tac[ADD_COMM]
QED

Finalise ptr_paired_owned_read_recovery
