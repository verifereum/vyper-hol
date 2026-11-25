(* Entry resources at the data-pointer cut of a raw CREATE snapshot. *)
Theory createSizeRawSnapshotEntryMods
Ancestors
  createSizeRawSnapshotEntry createExprSizeExitDefsMods
  bodyFullUnwrapSlotPost exprPtrUnwrapAllocSemantic exprPtrUnwrapAllocEntry
  bodyMemoryDefs bodyPtrDefs ptrDiscipline decoderAllocationBoundsPtr exprSimCopy exprPtrUnwrapRetained
  exprPtrUnwrapAllocSeparation bodyFullHashKeccakFixed
  exprLowering exprLoweringProps emitHelperProps compileEnv loweringPosts
  bufferAllocationExecution allocaHistory venomState venomMemDefs
  venomExecSemantics venomMemProps venomInst finite_map pred_set words arithmetic
  exprSimAlloc exprSimStorageCopy exprPtrUnwrapAllocation
  createSizeRawMemoryFootprint createSizeRawImmutableFootprint
  createSizeRawScalarFrame createSizeRawCutHistory createSizeSlotTraversal
  exprPtrUnwrapRuntimeFrame createBlueprintRawCopyLayoutMods bodyPtrMakeArrayExternalCaller
  exprPtrUnwrapMarked externalEntryShape loweringShapeDefs abiBufferAllocationCode
  loweringHalt valueTypingMemoryProps exprSimAggregateLayout vfmConstants
  exprBodyPreProps exprSimSource exprSimHyps abiEncodeArgsCase vyperInterpreter vyperTyping valueEncodingProps valueEncodingDefs
  fragGasOrigin fragExec context copyExecution slotCopyExecution relation list rich_list
  vyperTypeSystem stateRelProj bodyPtrAttributeSource freshWrites reasonEndpointResourcesPtr
  createCtorSnapshotTypingMods bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit
  exprSimIfExpCompat exprBodyPreTypingProps bodySimStmtFacts exprSimHypsDefs
  vyperTypeEvalCaseProofs loweringStateRelDefs createSizeRawHeaderGeometry
  createSizeSnapshotSlotCutMods
Libs BasicProvers

(* These are entry ghosts, not a claimed ghost execution. In particular,
   the bytes in the snapshot window are conservatively allowed to be tainted. *)

Theorem raw_snapshot_entry_ghost_mods[local]:
  ghost_inv_at_mods D lo d ce cx es G tn u /\ local_ptrs_reserved ce a /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at a x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at a x) /\
  local_ptrs_rel func ce es.scopes u /\
  (!name b n. local_region ce es.scopes u name b n ==>
     (snapshot_base:num) + cap <= b \/ b + n <= snapshot_base) /\
  (!x. not_fresh_at a x ==> lookup_var x r = lookup_var x u) /\
  (!off n. off + n <= snapshot_base \/ snapshot_base + cap <= off ==>
     mem_bytes_at off n r.vs_memory = mem_bytes_at off n u.vs_memory) /\
  ~not_fresh_at a len /\ ~not_fresh_at a data /\ lo <= snapshot_base /\
  r.vs_accounts = u.vs_accounts /\ r.vs_transient = u.vs_transient /\
  r.vs_immutables = u.vs_immutables /\ r.vs_call_ctx = u.vs_call_ctx /\
  allocas_from lo r /\ lo <= r.vs_alloca_next ==>
  ghost_inv_at_mods D lo d ce cx es (G |+ (data,snapshot_base,cap))
    (tn with <|t_var := tn.t_var |+ (len,{}) |+ (data,{});
               t_mem := tn.t_mem UNION {i | snapshot_base <= i /\ i < snapshot_base + cap}|>) r
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `Gr = G |+ (data,snapshot_base,cap)` >>
  qabbrev_tac `tr = tn with <|t_var := tn.t_var |+ (len,{}) |+ (data,{});
               t_mem := tn.t_mem UNION {i | snapshot_base <= i /\ i < snapshot_base + cap}|>` >>
  qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def]) >>
  `ghost_inv_at D 0 d ce cx es G tn u` by
    (simp[ghost_inv_at_def, allocas_from_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at a x ==> FLOOKUP Gr x = FLOOKUP G x /\
                           op_taint tr (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> `x <> data /\ x <> len` by metis_tac[] >>
     simp[Abbr `Gr`, Abbr `tr`, op_taint_def, FLOOKUP_UPDATE]) >>
  `!j. j < snapshot_base \/ snapshot_base + cap <= j ==>
       (j IN tr.t_mem <=> j IN tn.t_mem)` by
    (rpt gen_tac >> strip_tac >> simp[Abbr `tr`] >> decide_tac) >>
  `ghost_inv_at D 0 d ce cx es Gr tr r` by
    (irule unwrap_slot_copy_ghost_inv_at >>
     `stor_taint_ok_at D tr r` by fs[stor_taint_ok_at_def, Abbr `tr`] >>
     simp[allocas_from_def] >>
     qexistsl_tac [`G`,`func`,`cap`,`u`,`a`,`snapshot_base`,`tn`] >>
     `cap + snapshot_base = snapshot_base + cap` by decide_tac >>
     asm_rewrite_tac[] >> rpt conj_tac >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at a x ==> _` drule >> simp[]) >>
  `mem_bytes_at 0 lo r.vs_memory = mem_bytes_at 0 lo u.vs_memory` by
    (first_x_assum irule >> simp[]) >>
  `!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==>
       FLOOKUP Gr x = NONE /\ op_taint tr (Var x) = {}` by
    (gen_tac >> strip_tac >>
     `not_fresh_at a x` by metis_tac[local_ptrs_reserved_imm_base] >>
     metis_tac[]) >>
  `!i. i < lo /\ i IN tr.t_mem ==>
    imm_section_dead_mods ce (mem_bytes_at 0 lo r.vs_memory) i` by
    (gen_tac >> strip_tac >> `i < snapshot_base` by decide_tac >> metis_tac[]) >>
  qpat_assum `ghost_inv_at D 0 d ce cx es Gr tr r`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
  rewrite_tac[bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem raw_snapshot_finish_entry_mods[local]:
  compile_alloc_buffer cap a = (buf,m) /\ fn_has_code a m func /\
  buf.buf_operand = Var root /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce a /\ cap < dimword (:256) /\
  step_inst_base (mk_inst a.cs_next_id ALLOCA [Lit (n2w cap)] [root]) u = OK v /\
  snapshot_base = buffer_allocation_base u a.cs_next_id /\
  u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
  alloca_history func u /\ ~u.vs_halted /\
  (?H. valid_horizon cx st0 H p.storage_trace) /\
  (!H. valid_horizon cx st0 H p.storage_trace ==>
     stmt_state_rel H ctx func ce cx (p with gas_obs := []) u /\
     immutable_frame_mods func ce cx (p with gas_obs := []) u /\
     storage_well_formed_on cx (p with gas_obs := []) (FST H) /\
     ghost_inv_at_mods (DF H) lo d ce cx (p with gas_obs := []) G tn u) /\
  return_buf_frame d ce a u /\ a.cs_next_var <= ac.cs_next_var /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at a x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at a x) /\
  copy_static r = copy_static v /\ LENGTH v.vs_memory <= LENGTH r.vs_memory /\
  (!x. not_fresh_at a x ==> lookup_var x r = lookup_var x v) /\
  (!off k. off+k <= snapshot_base \/ snapshot_base+cap <= off ==>
    mem_bytes_at off k r.vs_memory = mem_bytes_at off k v.vs_memory) /\
  alloca_history func r /\
  r.vs_current_bb = ac.cs_current_bb /\ r.vs_inst_idx = LENGTH ac.cs_current_insts /\
  ~not_fresh_at a len /\ ~not_fresh_at a data /\
  not_fresh_at ac len /\ not_fresh_at ac data /\
  lookup_var len r = SOME (n2w (LENGTH code)) /\
  lookup_var data r = SOME (n2w (snapshot_base+32)) /\ LENGTH code + 32 <= cap ==>
  ?Gr tnr.
    (!H. valid_horizon cx st0 H p.storage_trace ==>
       stmt_state_rel H ctx func ce cx (p with gas_obs := []) r /\
       immutable_frame_mods func ce cx (p with gas_obs := []) r /\
       storage_well_formed_on cx (p with gas_obs := []) (FST H) /\
       ghost_inv_at_mods (DF H) lo d ce cx (p with gas_obs := []) Gr tnr r) /\
    return_buf_frame d ce ac r /\ alloca_history func r /\ ~r.vs_halted /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp r) /\
    r.vs_current_bb = ac.cs_current_bb /\ r.vs_inst_idx = LENGTH ac.cs_current_insts /\
    FLOOKUP r.vs_allocas a.cs_next_id = SOME (snapshot_base,cap) /\
    lookup_var len r = SOME (n2w (LENGTH code)) /\
    lookup_var data r = SOME (n2w (snapshot_base+32)) /\
    not_fresh_at ac len /\ not_fresh_at ac data /\
    op_taint tnr (Var len) = {} /\ ptr_covers Gr tnr data r (LENGTH code) /\
    w2n (n2w (snapshot_base+32) : bytes32) + LENGTH code <= r.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `ee = p with gas_obs := []` >> fs[GSYM markerTheory.Abbrev_def] >>
  `stmt_state_rel H ctx func ce cx ee u /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn u` by
    (qpat_assum `!H. valid_horizon _ _ _ _ ==> _` drule >> simp[]) >>
  `snapshot_base + cap < dimword (:256)` by
    (drule_all unwrap_alloc_site_bound >> simp[]) >>
  `snapshot_base + 32 < dimword (:256) /\ snapshot_base < dimword (:256)` by decide_tac >>
  qabbrev_tac `i = mk_inst a.cs_next_id ALLOCA [Lit (n2w cap)] [root]` >>
  `exec_alloca i u (n2w cap:bytes32) = OK v` by
    (qpat_assum `step_inst_base _ u = _` mp_tac >>
     simp_tac (srw_ss()) [Abbr `i`, step_inst_base_opcode_eqs, mk_inst_def]) >>
  `v = update_var root (n2w snapshot_base) (buffer_allocation_fields u a.cs_next_id cap)` by
    (drule_all unwrap_alloc_generated_step >>
     disch_then (qspec_then `u` strip_assume_tac) >> gvs[]) >>
  `MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\ i.inst_id = a.cs_next_id` by
    (drule unwrap_alloc_generated_code >> strip_tac >>
     `root = STRING #"%" (toString a.cs_next_var)` by fs[] >>
     drule_all buffer_alloc_code >> fs[Abbr `i`, mk_inst_def]) >>
  qunabbrev_tac `i` >>
  `!H. valid_horizon cx st0 H p.storage_trace ==> stmt_state_rel H ctx func ce cx ee v` by
    (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ _ _ ==> _ /\ _` drule >> strip_tac >>
     drule_all unwrap_alloc_semantic_frames >> simp[]) >>
  `FLOOKUP v.vs_allocas a.cs_next_id = SOME (snapshot_base,cap) /\
   v.vs_memory = u.vs_memory /\
   (!x. not_fresh_at a x ==> lookup_var x v = lookup_var x u)` by
    (drule_all unwrap_alloc_semantic_frames >> simp[w2n_n2w, LESS_MOD]) >>
  `!name b n. local_region ce ee.scopes u name b n ==>
     snapshot_base+cap <= b \/ b+n <= snapshot_base` by
    (rpt strip_tac >> drule_all unwrap_alloc_local_separation >> simp[]) >>
  `!name b n. local_region ce ee.scopes v name b n ==>
     snapshot_base+cap <= b \/ b+n <= snapshot_base` by
    (rpt strip_tac >> drule_all unwrap_alloc_semantic_frames >> strip_tac >>
     qpat_assum `!name b k. local_region _ _ v _ _ _ ==> _` drule >>
     simp_tac (srw_ss()) [loweringStateRelDefsTheory.regions_disjoint_def, w2n_n2w, ADD_COMM] >>
     `snapshot_base MOD dimword (:256) = snapshot_base` by simp[LESS_MOD] >>
     simp[]) >>
  `u.vs_alloca_next <= v.vs_alloca_next /\ allocas_from lo v` by
    (qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
     `allocas_from lo v` by (drule_all exec_alloca_preserves_allocas_from >> simp[]) >>
     drule exec_alloca_alloca_next_mono >> simp[]) >>
  `!H. valid_horizon cx st0 H p.storage_trace ==> stmt_state_rel H ctx func ce cx ee r` by
    (qx_gen_tac `h` >> disch_tac >>
     `stmt_state_rel h ctx func ce cx ee v` by
       (qpat_assum `!h. valid_horizon _ _ h _ ==> stmt_state_rel h _ _ _ _ _ v`
          (qspec_then `h` mp_tac) >> simp[]) >>
     irule copy_buffer_state_rel_frame >>
     qexistsl_tac [`snapshot_base`,`mk_inst a.cs_next_id ALLOCA [Lit (n2w cap)] [root]`,`v`,`a`,`cap`] >>
     rpt conj_tac
     >- qpat_assum `!name b n. local_region ce ee.scopes v name b n ==> _` ACCEPT_TAC
     >- qpat_assum `!x. not_fresh_at a x ==> lookup_var x r = lookup_var x v` ACCEPT_TAC
     >- (rpt gen_tac >> disch_tac >>
         qpat_assum `!off k. _ ==> mem_bytes_at off k r.vs_memory = _` irule >>
         decide_tac)
     >- qpat_assum `LENGTH v.vs_memory <= LENGTH r.vs_memory` ACCEPT_TAC
     >- qpat_assum `(mk_inst _ _ _ _).inst_opcode = ALLOCA` ACCEPT_TAC
     >- (qpat_assum `(mk_inst _ _ _ _).inst_id = _` (fn th => pure_rewrite_tac[th]) >>
         qpat_assum `FLOOKUP v.vs_allocas _ = SOME _` ACCEPT_TAC)
     >- qpat_assum `copy_static r = copy_static v` ACCEPT_TAC
     >- qpat_assum `MEM (mk_inst _ _ _ _) (fn_insts func)` ACCEPT_TAC
     >- qpat_assum `local_ptrs_reserved ce a` ACCEPT_TAC >>
     qpat_assum `stmt_state_rel h ctx func ce cx ee v` ACCEPT_TAC) >>
  `!x. not_fresh_at a x ==> lookup_var x r = lookup_var x u` by metis_tac[] >>
  `return_buf_frame d ce ac r` by
    (drule copy_static_fields >> strip_tac >> irule return_buf_frame_frame >>
     qexistsl_tac [`ce`,`u`,`a`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[GREATER_EQ]) >>
  suspend "entry"
QED

Resume raw_snapshot_finish_entry_mods[entry]:
  drule copy_static_fields >> strip_tac >>
  `r.vs_immutables = v.vs_immutables` by
    (qpat_assum `copy_static r = _` (mp_tac o AP_TERM ``\s. s.vs_immutables``) >>
     simp_tac (srw_ss()) [copy_static_def]) >>
  `immutable_frame_mods func ce cx ee r` by suspend "immutable" >>
  `!H. valid_horizon cx st0 H p.storage_trace ==>
    ghost_inv_at_mods (DF H) lo d ce cx ee (G |+ (data,snapshot_base,cap))
      (tn with <|t_var := tn.t_var |+ (len,{}) |+ (data,{});
                 t_mem := tn.t_mem UNION {i | snapshot_base <= i /\ i < snapshot_base + cap}|>) r` by
    suspend "ghost" >>
  `alloca_inv r` by
    (qpat_assum `!H. valid_horizon _ _ _ _ ==> stmt_state_rel _ _ _ _ _ _ r` drule >>
     metis_tac[stmt_state_rel_local_ptrs_alloca]) >>
  `snapshot_base + cap <= r.vs_alloca_next` by
    (qpat_assum `alloca_inv r`
       (strip_assume_tac o REWRITE_RULE [alloca_inv_def, alloca_next_valid_def]) >>
     qpat_assum `!aid base sz. FLOOKUP r.vs_allocas aid = _ ==> _` irule >>
     qexists_tac `a.cs_next_id` >> metis_tac[]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp r)` by
    (qpat_assum `!H. valid_horizon _ _ _ _ ==> stmt_state_rel _ _ _ _ _ _ r` drule >>
     metis_tac[stmt_state_rel_allocas_below_fmp]) >>
  qexistsl_tac [`G |+ (data,snapshot_base,cap)`,
    `tn with <|t_var := tn.t_var |+ (len,{}) |+ (data,{});
               t_mem := tn.t_mem UNION {i | snapshot_base <= i /\ i < snapshot_base + cap}|>`] >>
  suspend "conclude"
QED

Resume raw_snapshot_finish_entry_mods[immutable]:
  `immutable_frame_mods func ce cx ee u` by
    (qpat_assum `!H. valid_horizon _ _ _ _ ==> _ /\ immutable_frame_mods _ _ _ _ _ /\ _` drule >> simp[]) >>
  `!src name b n. local_region (ce with ce_module := src) ee.scopes v name b n <=>
                   local_region (ce with ce_module := src) ee.scopes u name b n` by
    (rpt gen_tac >>
     `local_region ce ee.scopes v name b n <=> local_region ce ee.scopes u name b n` by
       (irule copy_buffer_local_region_frame >> qexists_tac `a` >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `local_region ce ee.scopes v name b n <=> _`
       (fn th => simp_tac (srw_ss()) [local_region_def, REWRITE_RULE [local_region_def] th])) >>
  `!src name b n. local_region (ce with ce_module := src) ee.scopes r name b n <=>
                   local_region (ce with ce_module := src) ee.scopes v name b n` by
    (rpt gen_tac >>
     `local_region ce ee.scopes r name b n <=> local_region ce ee.scopes v name b n` by
       (irule copy_buffer_local_region_frame >> qexists_tac `a` >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `local_region ce ee.scopes r name b n <=> _`
       (fn th => simp_tac (srw_ss()) [local_region_def, REWRITE_RULE [local_region_def] th])) >>
  qpat_x_assum `immutable_frame_mods _ _ _ _ u`
    (strip_assume_tac o REWRITE_RULE [immutable_frame_mods_def,
       immutable_alloca_sep_mods_def, immutables_rel_mods_def]) >>
  `!src tops. ALOOKUP ce.ce_modules src = SOME tops ==>
              immutable_alloca_sep func (ce with ce_module := src) cx ee v` by
    (rpt gen_tac >> strip_tac >> irule immutable_alloca_sep_exec_alloca >>
     goal_assum (drule_at (Pat `exec_alloca _ _ _ = _`)) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
  simp[immutable_frame_mods_def, immutable_alloca_sep_mods_def, immutables_rel_mods_def] >>
  reverse conj_tac
  >- (rpt gen_tac >> strip_tac >> irule immutable_alloca_sep_fields >>
      qexistsl_tac [`v`,`ee`] >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!src tops. _ ==> immutables_rel _ _ _ _ _ u` (drule_then assume_tac) >>
  Cases_on `ce.ce_is_ctor`
  >- suspend "immutable_ctor" >>
  `v.vs_data_section = u.vs_data_section` by
    (qpat_assum `v = update_var _ _ _` SUBST1_TAC >>
     Cases_on `FLOOKUP u.vs_allocas a.cs_next_id` >> simp[update_var_def,buffer_allocation_fields_def]) >>
  fs[immutables_rel_def] >> first_assum ACCEPT_TAC
QED

Resume raw_snapshot_finish_entry_mods[immutable_ctor]:
  qpat_x_assum `immutables_rel _ _ src _ _ u`
    (assume_tac o SIMP_RULE (srw_ss()) [immutables_rel_def, LET_THM]) >>
  simp[immutables_rel_def] >> rpt gen_tac >> strip_tac >>
  qpat_assum `!name tv v byte_offset. FLOOKUP ce.ce_module_vars _ = _ /\ _ ==> _`
    (drule_all_then (fn facts =>
       qpat_assum `ce.ce_is_ctor` (fn ctor =>
         strip_assume_tac (SIMP_RULE (srw_ss()) [ctor] facts)))) >>
  `regions_disjoint byte_offset (type_memory_size tv) snapshot_base cap` by
    (qpat_assum `!src tops. _ ==> immutable_alloca_sep _ _ _ _ v`
       (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [immutable_alloca_sep_def])) >>
     qpat_x_assum `ce.ce_is_ctor ==> _` (drule_then assume_tac) >>
     qpat_assum `!name tv v off. FLOOKUP ce.ce_module_vars _ = _ /\ _ ==> _ /\ _`
       (drule_all_then strip_assume_tac) >>
     qpat_assum `!inst b sz. _ ==> regions_disjoint _ _ _ _`
       (qspec_then `mk_inst a.cs_next_id ALLOCA [Lit (n2w cap)] [root]` mp_tac) >>
     simp[mk_inst_def] >> metis_tac[]) >>
  `mem_bytes_at byte_offset (type_memory_size tv) r.vs_memory =
   mem_bytes_at byte_offset (type_memory_size tv) u.vs_memory` by
    (qpat_assum `v.vs_memory = u.vs_memory` (fn th => pure_once_rewrite_tac [GSYM th]) >>
     qpat_assum `!off n. _ ==> mem_bytes_at off n r.vs_memory = _` irule >>
     qpat_assum `regions_disjoint _ _ _ _` (mp_tac o REWRITE_RULE [regions_disjoint_def]) >>
     asm_rewrite_tac[] >> decide_tac) >>
  simp[] >> irule val_in_memory_mem_agree >>
  conj_tac >- metis_tac[loweringSliceTheory.immutable_admissible_val_wf] >>
  qexistsl_tac [`type_memory_size tv`, `u.vs_memory`] >> simp[]
QED

Resume raw_snapshot_finish_entry_mods[ghost]:
  rpt strip_tac >> irule raw_snapshot_entry_ghost_mods >>
  `lo <= u.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `lo <= r.vs_alloca_next` by decide_tac >>
  `allocas_from lo r` by (pure_rewrite_tac [allocas_from_def] >> metis_tac[allocas_from_def]) >>
  `FLOOKUP r.vs_allocas a.cs_next_id = SOME (snapshot_base,cap)` by metis_tac[] >>
  `lo <= snapshot_base` by metis_tac[allocas_from_def] >>
  `v.vs_accounts = u.vs_accounts /\ v.vs_transient = u.vs_transient /\
   v.vs_immutables = u.vs_immutables /\ v.vs_call_ctx = u.vs_call_ctx` by
    (qpat_assum `v = update_var _ _ _` SUBST1_TAC >>
     Cases_on `FLOOKUP u.vs_allocas a.cs_next_id` >>
     simp[update_var_def,buffer_allocation_fields_def]) >>
  `local_ptrs_rel func ce ee.scopes u` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> qexistsl_tac [`a`,`func`,`u`] >>
  rename1 `valid_horizon cx st0 h p.storage_trace` >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _ /\ immutable_frame_mods _ _ _ _ _ /\ _`
    (qspec_then `h` (strip_assume_tac o UNDISCH)) >>
  `cap + snapshot_base = snapshot_base + cap` by decide_tac >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  metis_tac[ADD_COMM]
QED

Resume raw_snapshot_finish_entry_mods[conclude]:
  `w2n (n2w (snapshot_base + 32) : bytes32) = snapshot_base+32` by
    simp[w2n_n2w,LESS_MOD] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt strip_tac >> first_assum irule >> first_assum ACCEPT_TAC)
  >- (qpat_assum `r.vs_halted <=> v.vs_halted` (fn th => PURE_REWRITE_TAC[th]) >>
      qpat_assum `v = update_var _ _ _` SUBST1_TAC >>
      Cases_on `FLOOKUP u.vs_allocas a.cs_next_id` >>
      simp[update_var_def,buffer_allocation_fields_def])
  >- metis_tac[]
  >- simp[op_taint_def, FLOOKUP_UPDATE]
  >- (simp_tac (srw_ss()) [ptr_covers_def,op_taint_def,FLOOKUP_UPDATE] >>
      qexists_tac `n2w (snapshot_base + 32)` >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  `w2n (n2w (buffer_allocation_base u a.cs_next_id + 32) : bytes32) = snapshot_base + 32` by metis_tac[] >>
  qpat_assum `w2n (n2w (buffer_allocation_base u a.cs_next_id + 32):bytes32) = _`
    (fn th => PURE_REWRITE_TAC [REWRITE_RULE [w2n_n2w] th]) >>
  decide_tac
QED
Finalise raw_snapshot_finish_entry_mods[local]

Theorem raw_snapshot_typed_capacity_mods[local]:
  expr_body_pre_mods mods ce cx env e es /\ expr_type e = BaseT (BytesT (Dynamic k)) /\ k <= 49152 /\
  compile_expr ce (expr_type e) e sa = (vv,a) /\
  eval_expr cx e (es with gas_obs := obs) = (INL tv,p) /\
  read_result cx tv p = (INL (BytesV code),p) /\
  vv_post_mods H ctx func ce cx e es sa a s0 (p with gas_obs := []) tv vv u ==>
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) = SOME (BaseTV (BytesT (Dynamic k))) /\
  LENGTH code + 32 <= type_memory_bytes ce (lowered_value_type ce e) /\
  type_memory_bytes ce (lowered_value_type ce e) < dimword (:256) /\
  32 * ((type_memory_bytes ce (lowered_value_type ce e) + 31) DIV 32) =
    type_memory_bytes ce (lowered_value_type ce e) /\
  (vv_location vv = SOME LocCode ==>
    type_memory_bytes ce (vv_type vv) = type_memory_bytes ce (lowered_value_type ce e))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre_mods mods ce cx env e (es with gas_obs := obs)` by simp[] >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) = (INL (BytesV code),p)` by
    simp[vyperStateTheory.bind_def] >>
  drule_all create_blueprint_raw_copy_layout_mods >> strip_tac >>
  rename1 `lowered_value_type ce e = BaseT (BytesT (Dynamic kl))` >>
  `type_memory_bytes ce (lowered_value_type ce e) = type_memory_size (BaseTV (BytesT (Dynamic kl)))` by
    metis_tac[typeLayoutPropsTheory.type_memory_bytes_base_evaluated] >>
  drule expr_body_pre_mods_inv >> strip_tac >>
  drule expr_sim_inv_mods_env >> strip_tac >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  drule expr_body_pre_mods_well_typed >> strip_tac >>
  `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
    metis_tac[env_consistent_var_type_evaluates, well_formed_type_def] >>
  `!fid sg. FLOOKUP env.fn_sigs fid = SOME sg ==>
       ce.ce_func_return_type (nsid_to_string fid) = sg.ret_ty` by
    metis_tac[expr_sim_inv_mods_return_type] >>
  `sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by fs[expr_sim_inv_mods_def] >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    (drule_all ifexp_lowered_type_classify >> strip_tac >>
     gvs[ifexp_arg_type_fits_refl] >> PairCases_on `fid` >>
     gvs[well_typed_expr_def, lowered_value_type_def, vyperASTTheory.expr_type_def] >>
     qpat_assum `!fid sg. FLOOKUP env.fn_sigs fid = _ ==> _` (drule_then assume_tac) >>
     gvs[ifexp_arg_type_fits_refl, type_widens_to_def]) >>
  `type_memory_bytes ce (lowered_value_type ce e) <= type_memory_bytes ce (expr_type e)` by
    (irule (cj 1 abi_args_fits_memory_bytes) >> simp[]) >>
  `LENGTH code <= 32 * word_size (LENGTH code)` by simp[word_size_capacity] >>
  `LENGTH code + 32 <= type_memory_bytes ce (lowered_value_type ce e)` by
    (qpat_assum `val_store_size _ _ <= type_memory_size (BaseTV (BytesT (Dynamic kl)))` mp_tac >>
     qpat_assum `type_memory_bytes ce (lowered_value_type ce e) = type_memory_size _`
       (fn th => pure_rewrite_tac[GSYM th]) >>
     simp[exprSimPropsTheory.val_store_size_def]) >>
  `type_memory_bytes ce (expr_type e) <= type_memory_bytes ce (BaseT (BytesT (Dynamic 49152)))` by
    (`(k+31) DIV 32 <= (49152+31) DIV 32` by
       (irule DIV_LE_MONOTONE >> decide_tac) >>
     fs[type_memory_bytes_def] >> decide_tac) >>
  `type_memory_bytes ce (BaseT (BytesT (Dynamic 49152))) < dimword (:256)` by
    simp[dimword_def,type_memory_bytes_def] >>
  `type_memory_bytes ce (lowered_value_type ce e) < dimword (:256)` by decide_tac >>
  simp[] >> conj_tac
  >- (qpat_assum `type_memory_bytes ce (lowered_value_type ce e) = type_memory_size _`
        (fn th => pure_rewrite_tac[th,type_memory_size_slots]) >>
      simp[Once MULT_COMM, ADD_DIV_ADD_DIV]) >>
  strip_tac >> Cases_on `vv` >> fs[vv_location_def, vv_type_def] >>
  `lowered_value_type ce e = expr_type e` by
    (irule external_located_lowered_type >>
     goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >> simp[]) >>
  gvs[vv_post_mods_def, vv_holds_mods_def, post_value_type_lowered]
QED

Theorem raw_snapshot_memory_header_mods[local]:
  vv_holds_mods ce cx (BaseT (BytesT (Dynamic k))) tv vv ee u /\
  read_result cx tv ee = (INL (BytesV code),ee) /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) = SOME (BaseTV (BytesT (Dynamic k))) /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) ==>
  ?s. eval_operand (vv_operand vv) u = SOME s /\ mload (w2n s) u = n2w (LENGTH code)
Proof
  Cases_on `vv` >>
  simp[bodyFullPostsModsTheory.vv_holds_mods_def, vv_holds_def, vv_operand_def,
       vv_location_def, expr_val_rel_def, is_word_type_def] >>
  strip_tac >> gvs[val_in_memory_def, mem_word_at_eq_mload] >> metis_tac[]
QED

Theorem raw_snapshot_copy_footprint_mods[local]:
  compile_alloc_buffer cap a = (buf,m) /\
  compile_create_snapshot ce vv ty a = (snap,b) /\ cap = type_memory_bytes ce ty /\
  fn_has_code a b func /\ B = buffer_allocation_base u a.cs_next_id /\
  B + cap < dimword (:256) /\ LENGTH code + 32 <= cap /\
  32 * ((cap + 31) DIV 32) = cap /\
  (vv_location vv = SOME LocCode ==> type_memory_bytes ce (vv_type vv) = cap) /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/ vv_location vv = SOME LocCode \/
    ?tr. vv_location vv = SOME (slot_loc tr)) /\
  local_ptrs_reserved ce a /\ stmt_state_rel H ctx func ce cx ee u /\
  vv_holds_mods ce cx (BaseT (BytesT (Dynamic k))) tv vv ee u /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) = SOME (BaseTV (BytesT (Dynamic k))) /\
  read_result cx tv ee = (INL (BytesV code),ee) /\ copy_old_operand a (vv_operand vv) /\
  u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
  v.vs_current_bb = u.vs_current_bb /\ v.vs_memory = u.vs_memory /\ v.vs_inst_idx = u.vs_inst_idx /\
  run_inst_seq (emitted_insts a m) u = OK v /\
  m.cs_current_insts = a.cs_current_insts ++ emitted_insts a m /\
  m.cs_current_bb = a.cs_current_bb /\ LENGTH m.cs_current_insts = SUC (LENGTH a.cs_current_insts) /\
  buf.buf_operand = Var root /\
  copy_old_operand m buf.buf_operand /\ eval_operand buf.buf_operand v = SOME (n2w B) /\
  (!op. copy_old_operand a op ==> copy_old_operand m op /\ eval_operand op v = eval_operand op u) /\
  ((vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/ vv_location vv = SOME LocCode) ==>
    run_inst_seq (emitted_insts a b) u = OK (z with vs_inst_idx := u.vs_inst_idx)) /\
  ((!tr. vv_location vv = SOME (slot_loc tr) ==>
    ?y exit. lookup_block b.cs_current_bb func.fn_blocks = SOME exit /\
      phi_prefix_length exit.bb_instructions = 0 /\
      fn_has_code m b func /\
      y.vs_current_bb = m.cs_current_bb /\ y.vs_inst_idx = LENGTH m.cs_current_insts /\
      z.vs_current_bb = b.cs_current_bb /\ z.vs_inst_idx = 0 /\
      run_inst_seq (emitted_insts a m) u = OK (y with vs_inst_idx := u.vs_inst_idx) /\
      RTC (\x t. (x.vs_current_bb <> b.cs_current_bb \/ x.vs_inst_idx <> 0) /\
                 ?ms. gas_origin_edge F explicit ctx func x ms (OK t)) y z)) ==>
  copy_static z = copy_static v /\ LENGTH v.vs_memory <= LENGTH z.vs_memory /\
  copy_old_operand b snap /\ eval_operand snap z = SOME (n2w B) /\
  (!x. not_fresh_at m x ==> lookup_var x z = lookup_var x v) /\
  (!off n. off+n <= B \/ B+cap <= off ==>
    mem_bytes_at off n z.vs_memory = mem_bytes_at off n v.vs_memory)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_alloc_buffer (type_memory_bytes ce ty) a = (buf,m)` by metis_tac[] >>
  drule_all create_raw_snapshot_alloc_interval >> strip_tac >>
  `w2n (n2w B : bytes32) = B` by (simp_tac (srw_ss()) [w2n_n2w,LESS_MOD] >> decide_tac) >>
  `copy_old_operand m snap /\ eval_operand snap v = SOME (n2w B)` by metis_tac[] >>
  `b.cs_current_insts = m.cs_current_insts ++ emitted_insts m b /\
        run_inst_seq (emitted_insts a b) u = OK (z with vs_inst_idx := u.vs_inst_idx) ==>
        run_inst_seq (emitted_insts m b) v = OK (z with vs_inst_idx := v.vs_inst_idx)` by
    (rpt strip_tac >> drule_all emitted_insts_append >> strip_tac >> metis_tac[run_inst_seq_append]) >>
  `?w. eval_operand (vv_operand vv) v = SOME w /\ copy_old_operand m (vv_operand vv)` by
    (Cases_on `vv` >> fs[vv_holds_mods_def, vv_holds_def, vv_operand_def, expr_val_rel_def] >>
     metis_tac[]) >>
  `copy_static z = copy_static v /\ LENGTH v.vs_memory <= LENGTH z.vs_memory /\
   m.cs_next_var <= b.cs_next_var /\
   (!x. not_fresh_at m x ==> lookup_var x z = lookup_var x v) /\
   (!off n. off+n <= B \/ B+cap <= off ==>
     mem_bytes_at off n z.vs_memory = mem_bytes_at off n v.vs_memory)` by suspend "copied" >>
  `copy_old_operand b snap` by metis_tac[copy_old_operand_mono] >>
  `eval_operand snap z = SOME (n2w B)` by
    (`snap = Var root` by metis_tac[] >>
     `not_fresh_at m root` by metis_tac[copy_old_operand_def] >>
     `lookup_var root z = lookup_var root v` by metis_tac[] >>
     `eval_operand (Var root) v = SOME (n2w B)` by metis_tac[] >>
     `eval_operand (Var root) z = SOME (n2w B)` by fs[eval_operand_def] >>
     metis_tac[]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume raw_snapshot_copy_footprint_mods[copied]:
  Cases_on `vv_location vv = NONE \/ vv_location vv = SOME LocMemory`
  >- suspend "memory" >>
  Cases_on `vv_location vv = SOME LocCode`
  >- suspend "code" >>
  suspend "slot"
QED

Resume raw_snapshot_copy_footprint_mods[memory]:
  `?cnt len bl bc. emit_op MLOAD [vv_operand vv] m = (len,bl) /\
    emit_op ADD [len; Lit 32w] bl = (cnt,bc) /\
    compile_copy_memory_dynamic snap (vv_operand vv) cnt bc = ((),b)` by
    (qpat_assum `compile_create_snapshot _ _ _ _ = _` mp_tac >>
     qpat_assum `compile_alloc_buffer (type_memory_bytes ce ty) a = _` (fn th =>
       simp_tac (srw_ss()) [th,LET_THM,compile_create_snapshot_def,comp_bind_def,comp_return_def,comp_ignore_bind_def]) >>
     qpat_assum `vv_location vv = NONE \/ vv_location vv = SOME LocMemory` strip_assume_tac >>
     qpat_assum `vv_location vv = _` (fn th =>
       simp_tac (srw_ss()) [th,comp_bind_def,comp_return_def,comp_ignore_bind_def]) >>
     Cases_on `emit_op MLOAD [vv_operand vv] m` >>
     rename1 `emit_op MLOAD _ m = (len,bl)` >>
     qpat_assum `emit_op MLOAD _ m = _` (fn th => simp_tac (srw_ss()) [th]) >>
     Cases_on `emit_op ADD [len; Lit 32w] bl` >>
     rename1 `emit_op ADD _ bl = (cnt,bc)` >>
     qpat_assum `emit_op ADD _ bl = _` (fn th => simp_tac (srw_ss()) [th]) >>
     Cases_on `compile_copy_memory_dynamic buf.buf_operand (vv_operand vv) cnt bc` >>
     qpat_assum `compile_copy_memory_dynamic _ _ cnt bc = _` (fn th => simp_tac (srw_ss()) [th]) >>
     strip_tac >> gvs[]) >>
  pop_assum strip_assume_tac >>
  `b.cs_current_insts = m.cs_current_insts ++ emitted_insts m b` by
    (`emit_void MCOPY [snap;vv_operand vv;cnt] bc = ((),b)` by
       (pure_rewrite_tac [GSYM compile_copy_memory_dynamic_def] >> first_assum ACCEPT_TAC) >>
     imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
     pure_rewrite_tac[emitted_insts_def] >>
     map_every (fn pat => qpat_assum pat (fn th => pure_rewrite_tac [th]))
       [`b.cs_current_insts = _`,`bc.cs_current_insts = _`,`bl.cs_current_insts = _`] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC,DROP_LENGTH_APPEND] >> simp_tac (srw_ss()) []) >>
  `run_inst_seq (emitted_insts m b) v = OK (z with vs_inst_idx := v.vs_inst_idx)` by metis_tac[] >>
  drule_all raw_snapshot_memory_header_mods >> strip_tac >>
  `mload (w2n s) v = n2w (LENGTH code)` by fs[mload_def,read_memory_def] >>
  `LENGTH code + 32 < dimword (:256)` by decide_tac >>
  `eval_operand (vv_operand vv) v = SOME s` by metis_tac[] >>
  drule_all create_raw_memory_copy_frame >> strip_tac >>
  `ci_mono m b` by
    metis_tac[ci_mono_emit_op,ci_mono_compile_copy_memory_dynamic,ci_mono_trans,pairTheory.SND] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- fs[ci_mono_def] >>
  rpt strip_tac >> qpat_assum `!off n. _ ==> mem_bytes_at off n z.vs_memory = _` irule >>
  decide_tac
QED

Resume raw_snapshot_copy_footprint_mods[code]:
  `compile_imm_copy_to_memory ce.ce_is_ctor ce.ce_imm_alloca (vv_operand vv) snap
     ((type_memory_bytes ce (vv_type vv) + 31) DIV 32) 0 m = ((),b)` by
    (qpat_assum `compile_create_snapshot _ _ _ _ = _` mp_tac >>
     qpat_assum `compile_alloc_buffer (type_memory_bytes ce ty) a = _` (fn alloc =>
       qpat_assum `vv_location vv = SOME LocCode` (fn loc =>
         simp_tac (srw_ss()) [alloc,loc,LET_THM,compile_create_snapshot_def,
                              comp_bind_def,comp_return_def,comp_ignore_bind_def])) >>
     qpat_assum `snap = buf.buf_operand` SUBST1_TAC >>
     qmatch_goalsub_rename_tac `compile_imm_copy_to_memory ctor imm src dst n 0 m` >>
     Cases_on `compile_imm_copy_to_memory ctor imm src dst n 0 m` >> simp[]) >>
  `cs_extends m b /\ added_labels m b = []` by
    (qmatch_asmsub_abbrev_tac `compile_imm_copy_to_memory _ _ src dst n 0 m` >>
     qspecl_then [`n`,`ce.ce_is_ctor`,`ce.ce_imm_alloca`,`src`,`dst`,`0`,`m`,`K F`]
       mp_tac compile_imm_copy_to_memory_labels >>
     simp[] >> Cases_on `added_labels m b` >> simp[]) >>
  `b.cs_current_insts = m.cs_current_insts ++ emitted_insts m b` by
    (qpat_assum `cs_extends m b` (strip_assume_tac o REWRITE_RULE [cs_extends_def]) >>
     `new = []` by
       (qpat_x_assum `added_labels _ _ = _` mp_tac >>
        Cases_on `new` >> simp[added_labels_def,all_blocks_def,LENGTH_NIL]) >>
     qpat_assum `new = []` (fn th =>
       qpat_assum `if new = [] then _ else _`
         (mp_tac o REWRITE_RULE [th])) >>
     simp_tac (srw_ss()) [rich_listTheory.IS_PREFIX_APPEND,emitted_insts_def] >>
     strip_tac >> qpat_assum `b.cs_current_insts = m.cs_current_insts ++ _`
       (fn th => simp_tac (srw_ss()) [th,DROP_LENGTH_APPEND])) >>
  `run_inst_seq (emitted_insts m b) v = OK (z with vs_inst_idx := v.vs_inst_idx)` by metis_tac[] >>
  `(ce.ce_is_ctor ==> !op. ce.ce_imm_alloca = SOME op ==>
      copy_old_operand m op /\ eval_operand op v = SOME 0w)` by
    (rpt strip_tac >>
     `copy_old_operand a op` by (simp[copy_old_operand_def] >> metis_tac[local_ptrs_reserved_imm_base]) >>
     drule stmt_state_rel_immutable_base_zero >> simp[immutable_base_zero_def] >> metis_tac[]) >>
  `32 * ((type_memory_bytes ce (vv_type vv) + 31) DIV 32) = cap` by metis_tac[] >>
  `w2n (n2w B : bytes32) + 32 * ((type_memory_bytes ce (vv_type vv) + 31) DIV 32)
     < dimword (:256)` by metis_tac[] >>
  drule_all create_raw_immutable_copy_frame >> strip_tac >>
  `ci_mono m b` by metis_tac[ci_mono_compile_imm_copy_to_memory,pairTheory.SND] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- fs[ci_mono_def] >>
  rpt strip_tac >> qpat_assum `!off n. _ ==> mem_bytes_at off n z.vs_memory = _` irule >> simp[]
QED

Resume raw_snapshot_copy_footprint_mods[slot]:
  `?tr. vv_location vv = SOME (slot_loc tr)` by metis_tac[] >> pop_assum strip_assume_tac >>
  `b = slot_copy_final m (vv_operand vv) snap ((cap + 31) DIV 32) (if tr then TLOAD else SLOAD)` by
    (drule_all create_snapshot_slot_compile_cut >> strip_tac >>
     metis_tac[]) >>
  qpat_assum `!tr. vv_location vv = SOME (slot_loc tr) ==> _` (drule_then strip_assume_tac) >>
  `v = y with vs_inst_idx := u.vs_inst_idx` by metis_tac[exec_result_11] >>
  `eval_operand (vv_operand vv) y = SOME w /\ eval_operand snap y = SOME (n2w B)` by
    (qpat_assum `v = y with vs_inst_idx := _` (fn th =>
       qpat_assum `eval_operand (vv_operand vv) v = SOME w` (mp_tac o REWRITE_RULE [th]) >>
       qpat_assum `eval_operand snap v = SOME (n2w B)` (mp_tac o REWRITE_RULE [th])) >> simp[]) >>
  `slot_copy_external m (vv_operand vv) /\ slot_copy_external m snap` by
    (`!op. copy_old_operand m op ==> slot_copy_external m op` by
       (Cases >> simp[copy_old_operand_def,slot_copy_external_def] >>
        metis_tac[slot_copy_not_fresh_external,slot_copy_external_def]) >> metis_tac[]) >>
  qabbrev_tac `n = (cap + 31) DIV 32` >>
  qabbrev_tac `load = if tr then TLOAD else SLOAD` >>
  `m.cs_next_var <= b.cs_next_var /\ b.cs_current_bb = slot_copy_exit m` by
    (qpat_assum `b = slot_copy_final _ _ _ _ _` SUBST1_TAC >> simp[slot_copy_final_def]) >>
  Q.SUBGOAL_THEN `load = SLOAD \/ load = TLOAD` assume_tac
  >- (Cases_on `tr` >> simp[Abbr `load`]) >>
  `32*n = cap` by simp[Abbr `n`] >>
  `w2n (n2w B : bytes32) + 32*n < 2 ** 256 /\ n < 2 ** 256` by
    (RULE_ASSUM_TAC (REWRITE_RULE [dimword_def,dimindex_256]) >> decide_tac) >>
  `slot_copy_runtime_frame m (n2w B : bytes32) n y z` by
    (`fn_has_code m (slot_copy_final m (vv_operand vv) snap n load) func` by metis_tac[] >>
     qpat_assum `b.cs_current_bb = slot_copy_exit m` (fn th =>
       qpat_assum `RTC _ y z` (assume_tac o REWRITE_RULE [th]) >>
       qpat_assum `lookup_block b.cs_current_bb _ = _` (assume_tac o REWRITE_RULE [th])) >>
     `z.vs_current_bb = slot_copy_exit m` by metis_tac[] >>
     Q.SUBGOAL_THEN `m.cs_current_bb <> slot_copy_exit m \/ 0 < LENGTH m.cs_current_insts` assume_tac
     >- simp[] >>
     drule_all create_slot_copy_actual_exit_frame >> strip_tac >> first_assum ACCEPT_TAC) >>
  `32*n <= cap` by decide_tac >>
  drule_all slot_copy_semantic_frame >> strip_tac >>
  `copy_static y = copy_static v /\ y.vs_memory = v.vs_memory /\
   (!x. lookup_var x y = lookup_var x v)` by
    (qpat_assum `v = y with vs_inst_idx := _` SUBST1_TAC >> simp[copy_static_def,lookup_var_def]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- metis_tac[]
  >- metis_tac[]
  >- (rpt strip_tac >> metis_tac[]) >>
  rpt strip_tac >>
  `off+n' <= w2n (n2w B : bytes32) \/ w2n (n2w B : bytes32) + cap <= off` by metis_tac[] >>
  metis_tac[]
QED
Finalise raw_snapshot_copy_footprint_mods[local]

Theorem create_raw_snapshot_payload_entry_mods:
  expr_body_pre_mods mods ce cx env e es /\ expr_type e = BaseT (BytesT (Dynamic k)) /\ k <= 49152 /\
  compile_expr ce (expr_type e) e sa = (vv,a) /\
  eval_expr cx e (es with gas_obs := obs) = (INL tv,p) /\
  read_result cx tv p = (INL (BytesV code),p) /\
  read_result cx tv (p with gas_obs := []) = (INL (BytesV code),p with gas_obs := []) /\
  valid_horizon cx st0 H p.storage_trace /\
  vv_post_mods H ctx func ce cx e es sa a s0 (p with gas_obs := []) tv vv u /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
      stmt_state_rel h ctx func ce cx (p with gas_obs := []) u /\
      storage_well_formed_on cx (p with gas_obs := []) (FST h) /\
      ghost_inv_at_mods (DF h) lo d ce cx (p with gas_obs := []) G tn u) /\
  return_buf_frame d ce a u /\ alloca_history func u /\ ~u.vs_halted /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce a /\ fn_inst_ids_distinct func /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at a x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at a x) /\
  compile_create_snapshot ce vv (lowered_value_type ce e) a = (snap,b) /\
  emit_op MLOAD [snap] b = (len_op,c) /\ emit_op ADD [snap; Lit 32w] c = (data_op,ac) /\
  fn_has_code a b func /\
  u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
  r.vs_current_bb = ac.cs_current_bb /\ r.vs_inst_idx = LENGTH ac.cs_current_insts /\
  ((vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/ vv_location vv = SOME LocCode) ==>
    run_inst_seq (emitted_insts a b) u = OK (z with vs_inst_idx := u.vs_inst_idx)) /\
  (!tr. vv_location vv = SOME (slot_loc tr) ==>
    ?buf m y exit. compile_alloc_buffer (type_memory_bytes ce (lowered_value_type ce e)) a = (buf,m) /\
      fn_has_code m b func /\ lookup_block b.cs_current_bb func.fn_blocks = SOME exit /\
      phi_prefix_length exit.bb_instructions = 0 /\
      y.vs_current_bb = m.cs_current_bb /\ y.vs_inst_idx = LENGTH m.cs_current_insts /\
      z.vs_current_bb = b.cs_current_bb /\ z.vs_inst_idx = 0 /\
      run_inst_seq (emitted_insts a m) u = OK (y with vs_inst_idx := u.vs_inst_idx) /\
      RTC (\x t. (x.vs_current_bb <> b.cs_current_bb \/ x.vs_inst_idx <> 0) /\
                 ?ms. gas_origin_edge F explicit ctx func x ms (OK t)) y z) /\
  run_inst_seq (emitted_insts b c) z = OK (l with vs_inst_idx := z.vs_inst_idx) /\
  run_inst_seq (emitted_insts c ac) l = OK (r with vs_inst_idx := l.vs_inst_idx) /\
  RTC (\x t. ?ms. gas_origin_edge F explicit ctx func x ms (OK t)) u r /\
  eval_operand len_op l = SOME (n2w (LENGTH code)) ==>
  ?Gr tnr len data.
    len_op = Var len /\ data_op = Var data /\
    (!h. valid_horizon cx st0 h p.storage_trace ==>
       stmt_state_rel h ctx func ce cx (p with gas_obs := []) r /\
       immutable_frame_mods func ce cx (p with gas_obs := []) r /\
       storage_well_formed_on cx (p with gas_obs := []) (FST h) /\
       ghost_inv_at_mods (DF h) lo d ce cx (p with gas_obs := []) Gr tnr r) /\
    return_buf_frame d ce ac r /\ alloca_history func r /\ ~r.vs_halted /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp r) /\
    r.vs_current_bb = ac.cs_current_bb /\ r.vs_inst_idx = LENGTH ac.cs_current_insts /\
    FLOOKUP r.vs_allocas a.cs_next_id =
      SOME (buffer_allocation_base u a.cs_next_id,type_memory_bytes ce (lowered_value_type ce e)) /\
    lookup_var len r = SOME (n2w (LENGTH code)) /\
    lookup_var data r = SOME (n2w (buffer_allocation_base u a.cs_next_id + 32)) /\
    not_fresh_at ac len /\ not_fresh_at ac data /\
    op_taint tnr (Var len) = {} /\ ptr_covers Gr tnr data r (LENGTH code) /\
    w2n (n2w (buffer_allocation_base u a.cs_next_id + 32) : bytes32) + LENGTH code <= r.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all raw_snapshot_typed_capacity_mods >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all reasonEndpointResourcesPtrTheory.compile_expr_old_operand >> strip_tac >>
  `vv_holds_mods ce cx (BaseT (BytesT (Dynamic k))) tv vv (p with gas_obs := []) u` by
    (`post_value_type ce e = BaseT (BytesT (Dynamic k))` by
       (irule EQ_TRANS >> qexists_tac `expr_type e` >>
        simp[post_value_type_bytestring,is_bytestring_type_def]) >>
     fs[vv_post_mods_def]) >>
  Q.SUBGOAL_THEN
    `vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/ vv_location vv = SOME LocCode \/
     ?tr. vv_location vv = SOME (slot_loc tr)` assume_tac
  >- (Cases_on `vv` >> simp[vv_location_def] >>
      qmatch_goalsub_rename_tac `pp.ptr_location = LocMemory` >>
      Cases_on `pp.ptr_location` >> simp[slot_loc_def]
      >- (qexists_tac `F` >> simp[])
      >- (qexists_tac `T` >> simp[]) >>
      qpat_x_assum `vv_holds_mods _ _ _ _ (LocatedValue _ pp) _ _` mp_tac >>
      simp[vv_holds_mods_def, vv_holds_def]) >>
  qabbrev_tac `cap = type_memory_bytes ce (lowered_value_type ce e)` >>
  qabbrev_tac `B = buffer_allocation_base u a.cs_next_id` >>
  Cases_on `compile_alloc_buffer cap a` >> rename1 `_ = (buf,m)` >>
  `fn_has_code a m func` by
    (`compile_alloc_buffer (type_memory_bytes ce (lowered_value_type ce e)) a = (buf,m)` by
       metis_tac[markerTheory.Abbrev_def] >>
     drule_all create_raw_snapshot_alloc_interval >> simp[]) >>
  `?root v. buf.buf_operand = Var root /\
    step_inst_base (mk_inst a.cs_next_id ALLOCA [Lit (n2w cap)] [root]) u = OK v /\
    run_inst_seq (emitted_insts a m) u = OK v /\
    m.cs_current_insts = a.cs_current_insts ++ emitted_insts a m /\
    m.cs_current_bb = a.cs_current_bb /\ LENGTH m.cs_current_insts = SUC (LENGTH a.cs_current_insts) /\
    m.cs_next_var = a.cs_next_var + 1 /\
    v.vs_current_bb = u.vs_current_bb /\ v.vs_memory = u.vs_memory /\ v.vs_inst_idx = u.vs_inst_idx /\
    copy_old_operand m buf.buf_operand /\ eval_operand buf.buf_operand v = SOME (n2w B) /\
    (!op. copy_old_operand a op ==> copy_old_operand m op /\ eval_operand op v = eval_operand op u)` by
    suspend "alloc" >>
  `immutable_frame_mods func ce cx (p with gas_obs := []) u` by fs[vv_post_mods_def] >>
  qpat_assum `!h. valid_horizon _ _ h _ ==> _ /\ _` (drule_then strip_assume_tac) >>
  `B + cap < dimword (:256)` by (drule_all unwrap_alloc_site_bound >> simp[Abbr `B`]) >>
  `alloca_inv u` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `alloca_history func r` by (drule_all create_raw_ok_rtc_alloca_history >> simp[]) >>
  suspend "frame"
QED

Resume create_raw_snapshot_payload_entry_mods[alloc]:
  drule compile_alloc_buffer_parts >> strip_tac >>
  drule abiBufferAllocationCodeTheory.compile_alloc_buffer_code >> strip_tac >>
  drule_all unwrap_alloc_generated_step >> disch_then (qspec_then `u` strip_assume_tac) >>
  gvs[Abbr `B`] >> simp[run_inst_seq_def, copy_old_operand_def] >>
  Cases_on `FLOOKUP u.vs_allocas a.cs_next_id` >>
  simp[buffer_allocation_fields_def, update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  gen_tac >> Cases_on `op` >>
  rw[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Resume create_raw_snapshot_payload_entry_mods[frame]:
  `cap = type_memory_bytes ce (lowered_value_type ce e) /\ B = buffer_allocation_base u a.cs_next_id` by
    simp[Abbr `cap`,Abbr `B`] >>
  `!tr. vv_location vv = SOME (slot_loc tr) ==>
    ?y exit. lookup_block b.cs_current_bb func.fn_blocks = SOME exit /\
      phi_prefix_length exit.bb_instructions = 0 /\ fn_has_code m b func /\
      y.vs_current_bb = m.cs_current_bb /\ y.vs_inst_idx = LENGTH m.cs_current_insts /\
      z.vs_current_bb = b.cs_current_bb /\ z.vs_inst_idx = 0 /\
      run_inst_seq (emitted_insts a m) u = OK (y with vs_inst_idx := u.vs_inst_idx) /\
      RTC (\x t. (x.vs_current_bb <> b.cs_current_bb \/ x.vs_inst_idx <> 0) /\
                 ?ms. gas_origin_edge F explicit ctx func x ms (OK t)) y z` by
    (gen_tac >> disch_tac >>
     qpat_assum `!tr. vv_location vv = SOME (slot_loc tr) ==> _` (drule_then strip_assume_tac) >>
     qpat_x_assum `(buf,m) = (_,_)`
       (map_every (SUBST_ALL_TAC o SYM) o CONJUNCTS o REWRITE_RULE [pairTheory.PAIR_EQ]) >>
     qexistsl_tac [`y`,`exit`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all raw_snapshot_copy_footprint_mods >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all create_raw_snapshot_scalar_frame >> strip_tac >>
  `a.cs_next_var <= m.cs_next_var` by simp[] >>
  `a.cs_next_var <= b.cs_next_var` by
    metis_tac[ci_mono_compile_create_snapshot,ci_mono_def,pairTheory.SND] >>
  `b.cs_next_var <= ac.cs_next_var` by
    metis_tac[ci_mono_emit_op,ci_mono_trans,ci_mono_def,pairTheory.SND] >>
  suspend "join"
QED

Resume create_raw_snapshot_payload_entry_mods[join]:
  `a.cs_next_var <= ac.cs_next_var` by decide_tac >>
  `~not_fresh_at a len /\ ~not_fresh_at a data` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `copy_static r = copy_static v /\ LENGTH v.vs_memory <= LENGTH r.vs_memory` by
    metis_tac[] >>
  `!x. not_fresh_at a x ==> lookup_var x r = lookup_var x v` by
    (rpt strip_tac >>
     `not_fresh_at m x /\ not_fresh_at b x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     metis_tac[]) >>
  `!off n. off+n <= B \/ B+cap <= off ==>
    mem_bytes_at off n r.vs_memory = mem_bytes_at off n v.vs_memory` by metis_tac[] >>
  Q.SUBGOAL_THEN `?h. valid_horizon cx st0 h p.storage_trace` assume_tac
  >- (qexists_tac `H` >> first_assum ACCEPT_TAC) >>
  `!h. valid_horizon cx st0 h p.storage_trace ==>
      stmt_state_rel h ctx func ce cx (p with gas_obs := []) u /\
      immutable_frame_mods func ce cx (p with gas_obs := []) u /\
      storage_well_formed_on cx (p with gas_obs := []) (FST h) /\
      ghost_inv_at_mods (DF h) lo d ce cx (p with gas_obs := []) G tn u` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!h. valid_horizon _ _ h _ ==> stmt_state_rel _ _ _ _ _ _ u /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  drule_all raw_snapshot_finish_entry_mods >> strip_tac >>
  qexistsl_tac [`Gr`,`tnr`,`len`,`data`] >> asm_rewrite_tac[]
QED
Finalise create_raw_snapshot_payload_entry_mods
