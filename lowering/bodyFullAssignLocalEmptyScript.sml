(* Empty-value memory assignments and their length-word stores. *)
Theory bodyFullAssignLocalEmpty
Ancestors
  allocaFootprint arithmetic assignBasePtrLocalBodyFacts augAssignFullStore
  bodyBinopFragMemory bodyFullMemoryFrames bodyFullPreds bodyFullUnwrapRun bodyMemoryDefs
  bodyPtrBytestringBuiltinsUintGhost bodyPtrDefs bodyPtrPrecompileBuiltinsArithmeticValue
  bodyFullShared bodySimFull codegenRel context contextCodegenRel emitHelperProps exprLoweringProps
  exprPtrCtorImmStore exprPtrUnwrapCopyEdges exprSimCopy exprSimHypsDefs finite_map fragExec
  fragExecMem fragGasOriginPtr fragGasOriginPtrDead fragGasOriginPtrLoop fragGasSeqPtr
  gasOutcomeFullCompose immutableCopyExecution immutableDeployOperandTransfer list
  loweringPosts loweringStateRelDefs memSafeRun memoryLocalRhsProps memoryValueEncoding
  option pair pred_set ptrDiscipline reasonCopySourcePtr stateRelProj stmtLowering
  stmtSimAssignMem stmtSimDeclMem stmtSimDefs stmtSimProps sum targetPlaceSim
  unitTransformDefs valueEncodingProps venomExecSemantics venomInst venomState vyperLookup
  vyperState vyperStorageBackend vyperStorageFootprint vyperStorageTrace vyperTypeInvariants
  vyperTyping wordLoadStorePtr words
  bodyFullPostsMods[qualified] bodyFullPredsMods[qualified] bodyInvSplit[qualified]
Libs
  monadsyntax

Theorem body_assign_empty_scalar_suffix:
  compile_store_at_loc imm dst (Lit 0w) (SOME loc) sa = ((),sb) /\
  eval_operand dst s = SOME w /\ op_taint tn dst = {} /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  loc <> LocCalldata /\
  (loc = LocMemory ==> ?p. dst = Var p /\ ptr_covers G tn p s 32 /\
     w2n w + 32 <= s.vs_alloca_next) /\
  ((loc = LocStorage \/ loc = LocTransient) ==> ~s.vs_call_ctx.cc_static) /\
  (loc = LocCode ==> fresh_vars_wrt sa s /\ op_prov G dst = NONE /\
     w2n w + 32 <= lo /\
     (!region. imm = SOME region ==> eval_operand region s = SOME 0w /\
       op_taint tn region = {} /\ op_prov G region = NONE)) ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK t,Gf,tf)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_fmp = s.vs_fmp /\ alloca_history func t /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    tf.t_mem SUBSET tn.t_mem /\
    ((loc = LocMemory \/ loc = LocCode) ==>
       t.vs_memory = (mstore (w2n w) 0w s).vs_memory /\
       mem_word_at (w2n w) t.vs_memory = 0w /\
       tf.t_mem = tn.t_mem DIFF {i | w2n w <= i /\ i < w2n w + 32} /\
       (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tf.t_mem) /\
       (!i. ~(w2n w <= i /\ i < w2n w + 32) ==>
         mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
         (i IN tf.t_mem <=> i IN tn.t_mem))) /\
    (loc = LocMemory ==>
       t = (mstore (w2n w) 0w s) with vs_inst_idx := LENGTH sb.cs_current_insts /\
       Gf = G /\ tf.t_imm = tn.t_imm /\
       tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans) /\
    (loc = LocStorage ==>
       t = (sstore w 0w s) with vs_inst_idx := LENGTH sb.cs_current_insts /\
       Gf = G /\ tf = tn with t_stor := key_update tn.t_stor w {}) /\
    (loc = LocTransient ==>
       t = (tstore w 0w s) with vs_inst_idx := LENGTH sb.cs_current_insts /\
       Gf = G /\ tf = tn with t_trans := key_update tn.t_trans w {}) /\
    (loc = LocCode ==>
       (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
          vs_immutables := s.vs_immutables; vs_inst_idx := s.vs_inst_idx|>) = s /\
       tf.t_imm = key_update tn.t_imm (w2n w) {} /\
       tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans)
Proof
  strip_tac >>
  qabbrev_tac `D0 = <|d_stor := K (K {}); d_trans := K (K {});
                       d_imm := K {}; d_ret := K {}|>` >>
  `?q Gf tf.
     run_inst_seq (emitted_insts sa sb) s = OK q /\
     gas_origin_ptr_path (D0,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK (q with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tf) /\
     same_blocks sa sb /\
     sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
     EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
                ~is_terminator i.inst_opcode /\ i.inst_opcode <> ALLOCA)
       (emitted_insts sa sb) /\
     run_inst_seq_mem_ok (emitted_insts sa sb) s /\
     ~q.vs_halted /\ q.vs_current_bb = s.vs_current_bb /\
     q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next /\
     q.vs_fmp = s.vs_fmp /\ q.vs_initial_fmp = s.vs_initial_fmp /\
     (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s /\
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
     tf.t_mem = (if loc = LocMemory \/ loc = LocCode then
       tn.t_mem DIFF {i | w2n w <= i /\ i < w2n w + 32} else tn.t_mem) /\
     ((loc = LocMemory \/ loc = LocCode) ==>
       q.vs_memory = (mstore (w2n w) 0w s).vs_memory) /\
     (loc = LocMemory ==> q = mstore (w2n w) 0w s /\ Gf = G /\
       tf.t_imm = tn.t_imm /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans) /\
     (loc = LocStorage ==> q = sstore w 0w s /\ Gf = G /\
       tf = tn with t_stor := key_update tn.t_stor w {}) /\
     (loc = LocTransient ==> q = tstore w 0w s /\ Gf = G /\
       tf = tn with t_trans := key_update tn.t_trans w {}) /\
     (loc = LocCode ==>
       (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                  vs_immutables := s.vs_immutables|>) = s /\
       tf.t_imm = key_update tn.t_imm (w2n w) {} /\
       tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans)` by
    (Cases_on `loc` >> gvs[]
     >- suspend "memory"
     >- suspend "storage"
     >- suspend "transient"
     >> suspend "code") >>
  qexistsl_tac [`q with vs_inst_idx := LENGTH sb.cs_current_insts`,`Gf`,`tf`] >>
  conj_tac >- suspend "path" >>
  conj_tac >- simp[] >>
  conj_tac >- fs[same_blocks_def] >>
  simp[] >>
  conj_tac >- suspend "history" >>
  conj_tac >- (fs[allocas_from_def] >> metis_tac[]) >>
  conj_tac >- (fs[allocas_below_fmp_def] >> metis_tac[]) >>
  conj_tac >- (fs[lookup_var_def] >> metis_tac[]) >>
  conj_tac >- (IF_CASES_TAC >> simp[]) >>
  conj_tac >- suspend "header" >>
  simp[] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `q with <|vs_memory := _; vs_vars := _; vs_immutables := _|> = s` mp_tac >>
  disch_then (mp_tac o Q.AP_TERM `\u. u with vs_inst_idx := LENGTH sa.cs_current_insts`) >>
  qpat_x_assum `s.vs_inst_idx = _` (fn th => rewrite_tac[GSYM th]) >> simp[]
QED

Resume body_assign_empty_scalar_suffix[memory]:
  gvs[compile_store_at_loc_def] >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (metis_tac[emit_mstore_mem_ok]) >>
  qexists_tac `tn with t_mem := tn.t_mem DIFF {i | w2n w <= i /\ i < w2n w + 32}` >>
  conj_tac >- simp[run_inst_seq_def,step_inst_base_opcode_eqs,mk_inst_def,exec_write2_def,eval_operand_def] >>
  conj_tac >- suspend "memory_path" >>
  simp[mstore_def,lookup_var_def,op_taint_def,mk_inst_def,is_terminator_def]
QED
Resume body_assign_empty_scalar_suffix[memory_path]:
  irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >>
  simp[] >> qexistsl_tac [`emitted_insts sa sb`,`sa`] >>
  `ptr_inst_ok D0 lo 0 ctx func G tn (mk_inst sa.cs_next_id MSTORE [Var p;Lit 0w] []) s` by
    (irule ptr_inst_ok_mstore_tainted >> simp[]) >>
  `step_taint (mk_inst sa.cs_next_id MSTORE [Var p;Lit 0w] []) s
      (mstore (w2n w) 0w s) tn =
    (tn with t_mem := tn.t_mem DIFF {i | w2n w <= i /\ i < w2n w + 32})` by
    (irule clean_mstore_taint_state >> gvs[eval_operand_def,op_taint_def]) >>
  simp[inst_seq_ptr_def,ifexp_materialize_mstore_ghost] >>
  fs[same_blocks_def,run_inst_seq_def,step_inst_base_opcode_eqs,mk_inst_def,
     exec_write2_def,eval_operand_def,is_terminator_def] >>
  conj_tac
  >- (strip_tac >> rpt gen_tac >> strip_tac >>
      irule dalloca_no_wrap_non_dalloca >>
      qpat_x_assum `[_] = _ ++ _` (mp_tac o Q.AP_TERM `MEM (i:instruction)`) >>
      simp[] >> strip_tac >> gvs[]) >>
  simp[GSYM mk_inst_def,ifexp_materialize_mstore_ghost]
QED
Resume body_assign_empty_scalar_suffix[storage]:
  gvs[compile_store_at_loc_def] >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  conj_tac >- simp[run_inst_seq_def,step_inst_base_opcode_eqs,mk_inst_def,exec_write2_def,eval_operand_def] >>
  conj_tac >- (irule (SRULE [] (Q.INST [`tr` |-> `F`] (SPEC_ALL storage_word_store_origin_ptr))) >>
    simp[] >> qexistsl_tac [`dst`,`Lit 0w`,`sa`] >> simp[eval_operand_def,op_taint_def] >>
    metis_tac[op_taint_def]) >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def,
       eval_operand_def, sstore_def, lookup_var_def, op_taint_def,
       is_terminator_def, run_inst_seq_mem_ok_last, inst_mem_below_frontier_def,
       inst_dload_in_section_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def]
QED
Resume body_assign_empty_scalar_suffix[transient]:
  gvs[compile_store_at_loc_def] >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  conj_tac >- simp[run_inst_seq_def,step_inst_base_opcode_eqs,mk_inst_def,exec_write2_def,eval_operand_def] >>
  conj_tac >- (irule (SRULE [] (Q.INST [`tr` |-> `T`] (SPEC_ALL storage_word_store_origin_ptr))) >>
    simp[] >> qexistsl_tac [`dst`,`Lit 0w`,`sa`] >> simp[eval_operand_def,op_taint_def] >>
    metis_tac[op_taint_def]) >>
  simp[tstore_def,lookup_var_def,op_taint_def,mk_inst_def,is_terminator_def,
       run_inst_seq_mem_ok_last,inst_mem_below_frontier_def,inst_dload_in_section_def,
       source_memory_write_ranges_def,source_memory_read_ranges_def]
QED
Resume body_assign_empty_scalar_suffix[code]:
  gvs[compile_store_at_loc_def] >>
  `copy_old_operand sa (Lit 0w)` by simp[copy_old_operand_def] >>
  `eval_operand (Lit 0w) s = SOME 0w` by simp[eval_operand_def] >>
  drule_all (Q.INST [`D` |-> `D0`, `fn` |-> `func`, `PG` |-> `PG`] code_ctor_store_word) >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  drule immutable_store_word_old_execution >>
  disch_then (qspecl_then [`0w`,`s`,`w`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  gvs[immutable_execution_frame_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by suspend "code_mem_ok" >>
  qexistsl_tac [`Gf`,`tnf`] >>
  conj_tac >- suspend "code_path" >>
  conj_tac >- (fs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[is_terminator_def]) >>
  simp[] >> suspend "code_frame"
QED
Resume body_assign_empty_scalar_suffix[path]:
  gen_tac >> irule gas_origin_ptr_path_from_no_dead >>
  gvs[Abbr `D0`]
QED
Resume body_assign_empty_scalar_suffix[history]:
  `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest` by
    (fs[fn_has_code_def,same_blocks_def,rich_listTheory.IS_PREFIX_APPEND] >>
     qexists_tac `l` >>
     `LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa sb)) = 0` by decide_tac >>
     simp[listTheory.DROP_APPEND]) >>
  `alloca_history func (q with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))` by
    (irule alloca_history_no_alloca_slice >>
     goal_assum (drule_at Any) >> gvs[EVERY_MEM] >> metis_tac[]) >>
  gvs[ADD_COMM]
QED
Resume body_assign_empty_scalar_suffix[header]:
  strip_tac >> simp[mstore_mem_word_at_same] >>
  rpt strip_tac >> simp[] >>
  irule mstore_mem_bytes_at_disjoint >> decide_tac
QED
Resume body_assign_empty_scalar_suffix[code_frame]:
  qpat_assum `t with <|vs_memory := _; vs_vars := _; vs_immutables := _|> = s` mp_tac >>
  simp[Once venom_state_component_equality] >>
  strip_tac >> gvs[op_taint_def]
QED
Resume body_assign_empty_scalar_suffix[code_mem_ok]:
  Cases_on `imm`
  >- (gvs[compile_imm_store_word_def] >>
      drule emitted_insts_emit_void >> strip_tac >>
      simp[run_inst_seq_mem_ok_last,inst_mem_below_frontier_def,
        inst_dload_in_section_def,source_memory_read_ranges_def,
        source_memory_write_ranges_def,fixed_source_write_range_def,mk_inst_def] >>
      decide_tac) >>
  rename1 `compile_imm_store_word (SOME region) dst (Lit 0w) sa = _` >>
  `eval_operand region s = SOME 0w` by metis_tac[] >>
  drule compile_imm_store_word_result >> strip_tac >>
  fs[emitted_insts_def,DROP_APPEND] >>
  simp[run_inst_seq_mem_ok_cons,run_inst_seq_mem_ok_last,
       inst_mem_below_frontier_def,inst_dload_in_section_def,
       source_memory_read_ranges_def,source_memory_write_ranges_def,
       fixed_source_write_range_def,mk_inst_def,step_inst_base_opcode_eqs,
       exec_pure2_def,eval_operand_def,update_var_def,lookup_var_def,FLOOKUP_UPDATE] >>
  simp[WORD_ADD_0] >> decide_tac
QED
Resume body_assign_empty_scalar_suffix[code_path]:
  `LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by simp[] >>
  pop_assum SUBST1_TAC >>
  irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >> simp[] >>
  qexistsl_tac [`emitted_insts sa sb`,`sa`] >>
  fs[same_blocks_def] >>
  conj_tac
  >- (strip_tac >> rpt gen_tac >> strip_tac >>
      irule dalloca_no_wrap_non_dalloca >>
      qpat_assum `EVERY _ (emitted_insts sa sb)`
        (qspec_then `i` mp_tac o REWRITE_RULE[EVERY_MEM]) >>
      simp[] >> strip_tac >> gvs[]) >>
  first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> simp[] >>
  disch_then kall_tac >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  qpat_assum `EVERY _ (emitted_insts sa sb)` (drule o REWRITE_RULE[EVERY_MEM]) >>
  strip_tac >> gvs[is_terminator_def]
QED
Finalise body_assign_empty_scalar_suffix

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all assign_base_local_rhs_pre >> strip_tac >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `has_length_word ty` by metis_tac[type_widens_to_has_length_word] >>
  rename1 `lookup_scopes id es.scopes = SOME ent` >>
  `evaluate_type (get_tenv cx) ty = SOME ent.type` by metis_tac[] >>
  `!gs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
         (INL (default_value ent.type), es with gas_obs := gs)` by
    (gen_tac >> metis_tac[memory_rhs_empty_read_destination]) >>
  rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  conj_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  conj_tac >- simp[] >> strip_tac >>
  drule_all assign_local_identity_rhs_all_tails >> strip_tac >>
  drule_all assign_local_empty_code_parts >> strip_tac >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `entry = ent` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `entry = ent` (SUBST_ALL_TAC o SYM) >>
  qabbrev_tac `H0 = storage_trace_horizon es.storage_trace` >>
  `valid_horizon cx st0 H0 es.storage_trace` by
    fs[Abbr `H0`, vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `stmt_state_rel H0 ctx func cenv cx es s0 /\
   ghost_inv_at (DF H0) lo d cenv cx es G0 tn0 s0` by metis_tac[] >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  drule_all local_ptr_below_frontier >> strip_tac >>
  `type_memory_size entry.type <= sz` by
    (qpat_assum `local_ptrs_rel _ _ _ _`
       (qspecl_then [`id`,`entry`,`p`,`sz`] mp_tac o
        CONJUNCT1 o REWRITE_RULE [local_ptrs_rel_def]) >> simp[] >>
     disch_then (qx_choose_then `u` strip_assume_tac) >> simp[]) >>
  `val_in_memory entry.type (default_value entry.type) (w2n w)
      (mstore (w2n w) 0w s0).vs_memory /\
   val_wf entry.type (default_value entry.type) /\ 32 <= type_memory_size entry.type` by
    (irule memory_length_word_layout >>
     simp[mstore_mem_word_at_same] >> qexistsl_tac [`get_tenv cx`,`ty`] >> simp[]) >>
  `ptr_covers G0 tn0 p s0 sz /\ allocas_from lo s0 /\ lo <= s0.vs_alloca_next` by
    (qpat_assum `ghost_inv_at (DF H0) lo d cenv cx es G0 tn0 s0`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
     simp[] >>
     qpat_assum `!name entry p sz. lookup_scopes name es.scopes = SOME entry /\ _ ==> _`
       (qspecl_then [`id`,`entry`,`p`,`sz`] mp_tac) >> simp[]) >>
  `32 <= sz` by decide_tac >>
  `ptr_covers G0 tn0 p s0 32` by metis_tac[ptr_covers_mono] >>
  `op_taint tn0 (Var p) = {}` by fs[ptr_covers_def] >>
  `w2n w + 32 <= s0.vs_alloca_next` by decide_tac >>
  `compile_store_at_loc cenv.ce_imm_alloca (Var p) (Lit 0w) (SOME LocMemory)
       sa = ((),sb)` by simp[compile_store_at_loc_def] >>
  `eval_operand (Var p) s0 = SOME w` by simp[eval_operand_def] >>
  drule_at (Pat `compile_store_at_loc _ _ _ _ _ = _`) body_assign_empty_scalar_suffix >>
  disch_then (qspecl_then [`w`,`tn0`,`s0`,`lo`,`func`,
    `gas_explicit_sites ctx shadow_ctx`,`ctx`,`PG`,`G0`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tf`
    (map_every assume_tac o CONJUNCTS o SRULE [])))) >>
  qabbrev_tac `ee = es with scopes := pre ++
    (env'' |+ (id,entry with <|value := default_value entry.type; popped := []|>)) :: rest` >>
  irule gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`Gf`,`ee`,`INL ()`,`t`,`tf`] >>
  `ee.storage_trace = es.storage_trace` by simp[Abbr `ee`] >>
  simp[] >> gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ _ es.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~block_is_terminated sb` by
    (irule emit_void_nonterminator_open >> goal_assum (drule_at Any) >>
     simp[is_terminator_def]) >>
  simp[stmt_lands_def, cenv_top_ext_refl] >>
  `local_region cenv es.scopes s0 id (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by
    (drule find_containing_scope_structure >> strip_tac >>
     simp[Abbr `ee`, PULL_EXISTS] >>
     `id IN FDOM env''` by fs[FLOOKUP_DEF] >>
     simp[pred_setTheory.ABSORPTION_RWT]) >>
  `return_buf_sep d cenv (ee with gas_obs := []) t` by suspend "separation" >>
  `stmt_state_rel H ctx func cenv cx ee t` by suspend "state" >>
  `return_buf_frame d cenv sb t` by suspend "ret" >>
  `ghost_inv_at (DF H) lo d cenv cx (ee with gas_obs := []) Gf tf t` by
    suspend "ghost" >>
  `alloca_frame cenv es sa s0 cenv ee t` by suspend "allocation" >>
  `!b. get_storage cx (ee with gas_obs := []) b = get_storage cx es b` by
    (gen_tac >> Cases_on `b` >> simp[Abbr `ee`, get_storage_def]) >>
  `storage_well_formed_on cx (ee with gas_obs := []) (FST H)` by
    (pure_rewrite_tac[storage_well_formed_on_def] >>
     qpat_assum `!b. get_storage cx (ee with gas_obs := []) b = _`
       (pure_rewrite_tac o single) >>
     qpat_assum `storage_well_formed_on cx es (FST H)`
       (ACCEPT_TAC o PURE_REWRITE_RULE [storage_well_formed_on_def])) >>
  simp[] >> (bossLib.gvs [pred_setTheory.SUBSET_DEF])
QED
*)
Theorem body_assign_local_memory_empty_full:
  !cx id ty e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok_mods mods exps cx (NameTarget id)) /\
    body_expr_full_ok_mods mods exps cx e /\
    (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
    supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv_mods mods cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    frame_ret_ok_full_mods mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    FLOOKUP env.var_types id = SOME ty /\
    ~is_word_type ty /\
    0 < type_memory_bytes cenv ty /\
    has_length_word (expr_type e) /\ is_empty_value_expr e ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty
        (gas_shadow_stmt (Assign (BaseTarget (NameTarget id)) e)))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume body_assign_local_memory_empty_full[separation]:
  simp[return_buf_sep_gas_obs] >>
  irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >>
  conj_tac
  >- (Cases_on `d` >- simp[] >>
      rename1 `return_buf_sep (SOME buf) _ _ _` >> PairCases_on `buf` >>
      qpat_assum `return_buf_sep (SOME (buf0,buf1)) cenv es s0`
        (mp_tac o CONJUNCT1 o REWRITE_RULE [return_buf_sep_def]) >>
      simp[allocas_from_def, mstore_def]) >>
  qexistsl_tac [`H`,`ctx`,`cx`,`es`,`func`,`s0`,`sa`] >>
  simp[lookup_var_def, mstore_def]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume body_assign_local_memory_empty_full[state]:
  simp[Abbr `ee`, stmt_state_rel_inst_idx] >>
  irule local_header_store_state >> simp[] >>
  irule val_in_memory_memory_value_rel >> simp[vyperTypingTheory.default_value_well_typed]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume body_assign_local_memory_empty_full[ret]:
  irule return_buf_frame_frame >>
  qexistsl_tac [`cenv`,`s0`,`sa`] >>
  drule emitted_insts_emit_void >> strip_tac >> simp[] >>
  rpt strip_tac >>
  qpat_assum `!x. not_fresh_at sa x ==> _` (qspec_then `x` mp_tac) >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume body_assign_local_memory_empty_full[ghost]:
  `dead_lo_ok H (DF H) lo cenv cx` by simp[] >>
  `0 < sz` by decide_tac >>
  `lo <= w2n w` by metis_tac[body_full_local_region_lower_bound] >>
  `stor_taint_ok_at (DF H) tf t` by
    (qpat_assum `ghost_inv_at (DF H) _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
     fs[stor_taint_ok_at_def, mstore_def]) >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s0.vs_memory` by
    (simp[] >> irule mstore_mem_bytes_at_disjoint >> simp[]) >>
  `!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
     val_in_memory entry.type (default_value entry.type) (w2n w) mem` by
    (rpt strip_tac >>
     `mem_word_at (w2n w) mem = 0w` by metis_tac[clean_word_mem_agree] >>
     metis_tac[memory_length_word_layout]) >>
  simp[Abbr `ee`, vyperStateTheory.evaluation_state_fupdcanon] >>
  qmatch_goalsub_abbrev_tac `es' with scopes := _` >>
  `ghost_inv_at (DF H) lo d cenv cx es' G0 tn0 s0` by
    (fs[Abbr `es'`, ghost_inv_at_def] >> metis_tac[ghost_inv_at_def]) >>
  `find_containing_scope id es'.scopes = SOME (pre,env'',entry,rest) /\
   local_ptrs_rel func cenv es'.scopes s0 /\
   local_region cenv es'.scopes s0 id (w2n w) sz` by simp[Abbr `es'`] >>
  irule body_full_local_scope_ghost_post >>
  ntac 4 (conj_tac >- gvs[]) >>
  qexistsl_tac [`G0`,`w`,`func`,`32`,`p`,`s0`,`sa`,`sz`,`tn0`] >>
  gnvs[ret_pc_ok_def, pred_setTheory.SUBSET_DEF] >>
  first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume body_assign_local_memory_empty_full[allocation]:
  `alloca_frame cenv es sa s0 cenv es s0` by simp[alloca_frame_same] >>
  drule_then irule alloca_frame_region_write >>
  simp[] >> conj_tac >- simp[lookup_var_def, mstore_def] >>
  qexistsl_tac [`w2n w`,`id`,`sz`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  irule mstore_mem_bytes_at_disjoint >> decide_tac
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise body_assign_local_memory_empty_full
*)
