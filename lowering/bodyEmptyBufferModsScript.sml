(* Empty at a nonword type materializes its default value in a fresh buffer. *)
Theory bodyEmptyBufferMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyAggregateReadMods bodyAssignNameLinkedSetup
  bodyFullEmptyCertificate bodyFullAllocGeneric bodyMethodIdScratchFrameMods
  exprBodyPreProps exprSimHyps exprSimHypsDefs exprSimAggregateLayout exprSimBufferEmpty exprSimBufferEmptyExec
  exprLowering compileEnv allocLimits valueEncoding vyperAST vyperValue
  vyperTypeSystem vyperTypeInvariants context words
  typeBuiltinPrereqs exprSimAlloc loweringHalt bufferAllocationExecution
  allocationPtr bodyPtrPrecompileBuiltinsAllocationFrame bodyFullEmptyOrigin
  fragExec fragGasSeqPtr instSeqPtrLo instIdxIndep list bodyPtrDefs exprLoweringProps
  ptrDiscipline venomState venomInst finite_map pred_set
  bodyFullShadowBodyInv bodyInvSplit loweringStateRelDefs loweringSlice
  ghostPcTransportPtr valueEncodingProofs exprSimProps exprSimBuffer exprSimMemDefs
  loweringPosts bodyMemAggregateBounds rawCallBufferPtr stateRelProj exprSimCopy
  gasOutcomeFullPostMods gasShadowCompileStmtHelpers gasShadow gasShadowState
  vyperInterpreter vyperStorageFootprint vyperStorageTrace vyperState vyperContext
  bodyPtrEnvBuiltinsSelectorBuffer venomMemProofs valueEncodingDefs
  stmtReasonMemory bodyFullUnwrapRun bodyAggregateReadPostMods rich_list bodyForRangeScalarFrameMods
Libs monadsyntax

Theorem empty_buffer_ready[local]:
  ~is_word_type typ /\
  expr_body_pre_mods mods cenv cx env (TypeBuiltin ann Empty typ xs) es ==>
  xs = [] /\ ann = typ /\ type_memory_bytes cenv typ < dimword (:256) /\
  ?rt. evaluate_type (get_tenv cx) typ = SOME rt /\
       type_memory_bytes cenv typ = type_memory_size rt
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  `env.type_defs = get_tenv cx` by
    fs[env_consistent_def, env_context_consistent_def] >>
  `ann = typ /\ xs = []` by
    fs[well_typed_expr_def, well_typed_type_builtin_args_def, type_builtin_result_ok_def] >>
  qpat_x_assum `ann = typ` SUBST_ALL_TAC >> gvs[] >>
  `type_memory_bytes cenv typ < dimword (:256)` by
    (qpat_assum `expr_body_pre_mods _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_body_pre_mods_def]) >>
     drule alloc_limits_expr_type_alloc_ok >>
     simp[expr_type_def, type_alloc_ok_def, dimword_def] >> decide_tac) >>
  gvs[well_typed_expr_def, well_typed_type_builtin_args_def,
      type_builtin_result_ok_def, well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  drule_all_then assume_tac assign_name_memory_bytes_mods >> goal_assum drule >> simp[]
QED

Theorem empty_buffer_compile[local]:
  ~is_word_type typ /\
  compile_expr cenv ty (TypeBuiltin typ Empty typ []) sa = (vv,sb) ==>
  ?buf. compile_builtin_empty_complex (type_memory_bytes cenv typ)
          (is_bytestring_type typ \/ (case typ of ArrayT _ (Dynamic _) => T | _ => F))
          sa = (buf,sb) /\ vv = LocatedValue typ (base_ptr buf)
Proof
  simp[compile_expr_type_builtin_dispatch, Once compile_type_builtin_dispatch_component_eq,
       comp_bind_def] >> pairarg_tac >> strip_tac >> gvs[]
QED

Theorem empty_buffer_size[local]:
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  if is_bytestring_type ty \/ (case ty of ArrayT _ (Dynamic _) => T | _ => F)
  then 32 <= type_memory_size tv else type_memory_size tv MOD 32 = 0
Proof
  strip_tac >> IF_CASES_TAC
  >- (Cases_on `ty` >>
      gvs[is_bytestring_type_def, AllCaseEqs(), evaluate_type_def, type_memory_size_def]
      >~ [`ArrayTV tv' bd`] >- (Cases_on `bd` >> gvs[type_memory_size_def]) >>
      rename1 `BaseT bt` >> Cases_on `bt` >>
      gvs[is_bytestring_type_def, AllCaseEqs(), evaluate_type_def, type_memory_size_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[is_bytestring_type_def, evaluate_type_def, type_memory_size_def]) >>
  simp[type_memory_size_aligned]
QED

Theorem empty_buffer_default[local]:
  evaluate_type (get_tenv cx) ty = SOME tv /\
  (if is_bytestring_type ty \/ (case ty of ArrayT _ (Dynamic _) => T | _ => F)
   then mem_word_at off mem = 0w
   else mem_bytes_at off (type_memory_size tv) mem = REPLICATE (type_memory_size tv) 0w) ==>
  val_in_memory tv (default_value tv) off mem
Proof
  strip_tac >>
  Cases_on `is_bytestring_type ty \/ (case ty of ArrayT _ (Dynamic _) => T | _ => F)`
  >- (Cases_on `ty` >> gvs[is_bytestring_type_def, AllCaseEqs(), evaluate_type_def]
      >~ [`ArrayTV tv' bd`] >- (Cases_on `bd` >> gvs[default_memory_header]) >>
      simp[default_memory_header] >>
      rename1 `BaseT bt` >> Cases_on `bt` >>
      gvs[is_bytestring_type_def, AllCaseEqs(), evaluate_type_def] >>
      simp[default_memory_header] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[is_bytestring_type_def, evaluate_type_def, default_memory_header]) >>
  irule default_memory_zero_bytes >> gvs[]
QED

Theorem empty_alloc_site_effects[local]:
  compile_alloc_buffer sz sa = (buf,sm) /\
  run_inst_seq (emitted_insts sa sm) s = OK u /\ sz < dimword (:256) /\
  eval_operand buf.buf_operand u = SOME w /\
  FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz) ==>
  new_site_bytes s u SUBSET {a | s.vs_alloca_next <= a} /\
  (!aid b n. FLOOKUP u.vs_allocas aid = SOME (b,n) ==>
      FLOOKUP s.vs_allocas aid = SOME (b,n) \/ s.vs_alloca_next <= b)
Proof
  strip_tac >>
  drule compile_alloc_buffer_execution >> disch_then (qspec_then `s` strip_assume_tac) >>
  `w2n (n2w sz :256 word) = sz` by simp[w2n_n2w] >>
  qpat_x_assum `run_inst_seq _ _ = OK u` mp_tac >> simp[] >> strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >>
  gvs[buffer_allocation_fields_def, buffer_allocation_base_def, update_var_def,
      eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, AllCaseEqs()] >>
  simp[new_site_bytes_def, SUBSET_DEF, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[FLOOKUP_DEF] >> decide_tac
QED

Theorem empty_run_effects[local]:
  compile_builtin_empty_complex sz header sa = (buf,sb) /\
  fn_has_code sa sb func /\
  stmt_state_rel (H : (bool # 256 word # type_value) list # num list) ctx func cenv cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  sz < dimword (:256) /\ (if header then 32 <= sz else sz MOD 32 = 0) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s Gf tnf ==>
  (?p. buf.buf_operand = Var p /\
       MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func)) /\
  (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G x /\
                            op_taint tnf (Var x) = op_taint tn (Var x)) /\
  (!a. a < s.vs_alloca_next /\ a IN tnf.t_mem ==> a IN tn.t_mem) /\
  (!aid b n. FLOOKUP t.vs_allocas aid = SOME (b,n) ==>
      FLOOKUP s.vs_allocas aid = SOME (b,n) \/ s.vs_alloca_next <= b)
Proof
  strip_tac >> drule_all empty_buffer_compile_prefix >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK u` >>
  drule_all empty_alloc_site_effects >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func)` by gvs[] >>
  qmatch_asmsub_abbrev_tac `MEM inst (fn_insts func)` >>
  `step_inst_base inst s = OK u` by gvs[run_inst_seq_def, AllCaseEqs()] >>
  `ptr_covers (step_prov PG G inst u) (step_taint inst s u tn) p u sz` by
    (unabbrev_all_tac >> irule (INST_TYPE [alpha |-> ``:256``] alloca_step_ptr_covers) >>
     simp[] >> qexistsl_tac [`H`,`cenv`,`ctx`,`cx`,`es`,`func`] >> simp[]) >>
  qmatch_asmsub_abbrev_tac `ptr_covers Ga ta p u sz` >>
  qabbrev_tac `ua = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `lookup_var p ua = SOME w /\ ptr_covers Ga ta p ua sz` by
    gvs[Abbr `ua`, eval_operand_def, lookup_var_def] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp ua)` by
    ((strip_tac >>
     `allocas_below_fmp u` by
       (qpat_assum `stmt_state_rel _ _ _ _ _ _ u`
         (mp_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >> simp[]) >>
     fs[Abbr `ua`, allocas_below_fmp_def] >> (metis_tac[Abbr `ua`, allocas_below_fmp_def]))) >>
  `allocas_from 0 ua` by simp[allocas_from_def] >>
  drule_all empty_buffer_tail_effects >>
  disch_then (qspecl_then [`func`,`PG`] strip_assume_tac) >>
  suspend "landing"
QED
Resume empty_run_effects[landing]:
  rename1 `run_inst_seq (emitted_insts sm sb) ua = OK v` >>
  rename1 `lookup_var p v = SOME w` >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (drule compile_builtin_empty_complex_shape >> simp[EVERY_MEM] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts sm sb) u = OK t` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sb) s = OK t` mp_tac >>
     asm_rewrite_tac[run_inst_seq_def] >> simp[]) >>
  `v = t with vs_inst_idx := SUC s.vs_inst_idx` by
    (drule run_inst_seq_inst_idx >>
     disch_then (qspecl_then [`u`,`SUC s.vs_inst_idx`] mp_tac) >>
     gvs[Abbr `ua`, exec_result_map_def]) >>
  `t.vs_allocas = u.vs_allocas` by
    (qpat_assum `v with <|vs_vars := _; vs_memory := _|> = ua`
       (mp_tac o AP_TERM ``venom_state_vs_allocas``) >> simp[Abbr `ua`]) >>
  `inst_seq_ptr D 0 ctx func PG Ga ta (emitted_insts sm sb) ua Gf tnf` by
    (qpat_x_assum `inst_seq_ptr _ _ _ _ _ G tn _ s Gf tnf` mp_tac >>
     asm_rewrite_tac[inst_seq_ptr_def] >>
     simp[Abbr `ua`, Abbr `Ga`, Abbr `ta`]) >>
  rename1 `ttail.t_mem = ta.t_mem DIFF _` >>
  rename1 `ptr_covers Gtail ttail p v sz` >>
  `inst_seq_ptr D 0 ctx func PG Ga ta (emitted_insts sm sb) ua Gtail ttail` by
    (qpat_assum `!D lo. allocas_from lo ua /\ _ ==> inst_seq_ptr _ _ _ _ _ _ _ _ _ Gtail ttail`
      (qspecl_then [`D`,`0`] mp_tac) >> simp[]) >>
  `Gf = Gtail /\ tnf = ttail` by
    (qpat_assum `inst_seq_ptr D 0 ctx func PG Ga ta _ ua Gf tnf` mp_tac >>
     qpat_assum `inst_seq_ptr D 0 ctx func PG Ga ta _ ua Gtail ttail` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[inst_seq_ptr_ghost_unique]) >>
  qpat_x_assum `Gf = Gtail` SUBST_ALL_TAC >>
  qpat_x_assum `tnf = ttail` SUBST_ALL_TAC >>
  `ta.t_mem = tn.t_mem UNION new_site_bytes s u /\
   (!x. x <> p ==> FLOOKUP Ga x = FLOOKUP G x /\
                   op_taint ta (Var x) = op_taint tn (Var x))` by
    (simp[Abbr `Ga`,Abbr `ta`,Abbr `inst`,alloca_ghost_frames]) >>
  conj_tac >- (qexists_tac `p` >> gvs[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm x` by simp[] >>
      `x <> p` by
        (strip_tac >>
         qpat_assum `buf.buf_operand = Var p` mp_tac >>
         qpat_assum `buf.buf_operand = Var (STRING _ _)` (fn th => rewrite_tac[th]) >>
         strip_tac >> gvs[]) >>
      qpat_assum `!q. not_fresh_at sm q ==> lookup_var q v = _ /\ _`
        (qspec_then `x` (drule_then strip_assume_tac)) >> simp[]) >>
  rpt strip_tac >> gvs[SUBSET_DEF] >> metis_tac[arithmeticTheory.NOT_LESS_EQUAL]
QED
Finalise empty_run_effects

Theorem empty_linked_ghost[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn s /\
  ghost_inv_at D 0 d cenv cx es G' tn' t /\
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
                            op_taint tn' (Var x) = op_taint tn (Var x)) /\
  (!i. i < s.vs_alloca_next /\ i IN tn'.t_mem ==> i IN tn.t_mem) /\
  (!aid a sz. FLOOKUP t.vs_allocas aid = SOME (a,sz) ==>
      FLOOKUP s.vs_allocas aid = SOME (a,sz) \/ s.vs_alloca_next <= a) /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory ==>
  ghost_inv_at_mods D lo d cenv cx es G' tn' t
Proof
  strip_tac >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (fs[ghost_inv_at_mods_def, allocas_from_def] >> rpt strip_tac >>
     qpat_assum `!aid a sz. FLOOKUP t.vs_allocas aid = _ ==> _`
       (drule_then strip_assume_tac) >- metis_tac[] >> decide_tac) >>
  `!i. i < lo /\ i IN tn'.t_mem ==> i IN tn.t_mem` by
    (fs[ghost_inv_at_mods_def] >> rpt strip_tac >>
     qpat_assum `!i. i < s.vs_alloca_next /\ _ ==> _` irule >> simp[] >> decide_tac) >>
  `!i. i < lo /\ i IN tn'.t_mem ==>
       imm_section_dead_mods cenv (mem_bytes_at 0 lo t.vs_memory) i` by
    (fs[ghost_inv_at_mods_def] >> rpt gen_tac >> strip_tac >>
     qpat_assum `!i. i < lo /\ i IN tn.t_mem ==> imm_section_dead_mods _ _ _` irule >>
     simp[]) >>
  `!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==>
       FLOOKUP G' x = NONE /\ op_taint tn' (Var x) = {}` by
    (fs[ghost_inv_at_mods_def] >> rpt gen_tac >> strip_tac >>
     `not_fresh_at sa x` by fs[local_ptrs_reserved_def] >>
     qpat_assum `!x. not_fresh_at sa x ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  fs[ghost_inv_at_mods_def, ghost_inv_at_def] >> first_assum ACCEPT_TAC
QED

Theorem empty_linked_immutable[local]:
  immutable_frame_mods func cenv cx es s /\
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!aid a sz. FLOOKUP t.vs_allocas aid = SOME (a,sz) ==>
      FLOOKUP s.vs_allocas aid = SOME (a,sz) \/ s.vs_alloca_next <= a) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP t.vs_allocas inst.inst_id = SOME (b,n) /\
  t.vs_data_section = s.vs_data_section /\ LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (!a sz. a + sz <= b \/ b + n <= a ==>
      mem_bytes_at a sz t.vs_memory = mem_bytes_at a sz s.vs_memory) ==>
  immutable_frame_mods func cenv cx es t
Proof
  simp[immutable_frame_mods_def] >> strip_tac >> reverse conj_asm2_tac
  >- (fs[immutable_alloca_sep_mods_def] >> rpt gen_tac >> strip_tac >>
      irule immutable_alloca_sep_frame >> qexistsl_tac [`s`,`es`] >> simp[] >>
      rpt gen_tac >> strip_tac >> disj1_tac >>
      rename1 `local_region _ _ t id a sz` >> qexists_tac `id` >>
      fs[local_region_def, local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]) >>
  fs[immutables_rel_mods_def, immutable_alloca_sep_mods_def] >>
  rpt gen_tac >> strip_tac >> irule immutables_rel_mem_agree >>
  qexists_tac `s` >> simp[] >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `!a sz. a + sz <= b \/ _ ==> _` irule >>
  qpat_assum `!src tops. _ ==> immutable_alloca_sep _ _ _ _ _`
    (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [immutable_alloca_sep_def])) >>
  qpat_x_assum `cenv.ce_is_ctor ==> _` (drule_then assume_tac) >>
  pop_assum (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!i a sz. MEM i _ /\ _ ==> regions_disjoint _ _ a sz`
    (drule_all_then mp_tac) >> simp[regions_disjoint_def]
QED

Theorem empty_post_gas_obs[local]:
  (immutable_frame_mods func cenv cx (es with gas_obs := gs) s <=>
     immutable_frame_mods func cenv cx es s) /\
  (ghost_inv_at_mods D lo d cenv cx (es with gas_obs := gs) G tn s <=>
     ghost_inv_at_mods D lo d cenv cx es G tn s) /\
  (storage_well_formed_on cx (es with gas_obs := gs) A <=>
     storage_well_formed_on cx es A)
Proof
  conj_tac
  >- (PURE_REWRITE_TAC[immutable_frame_mods_def, immutables_rel_mods_def,
        immutable_alloca_sep_mods_def, immutable_alloca_sep_def,
        immutables_rel_def, evaluation_state_accfupds] >> simp[]) >>
  conj_tac
  >- (PURE_REWRITE_TAC[ghost_inv_at_mods_def, evaluation_state_accfupds] >> simp[]) >>
  irule storage_well_formed_on_backends >> simp[]
QED

Theorem empty_buffer_eval[local]:
  evaluate_type (get_tenv cx) typ = SOME rt ==>
  eval_expr cx (TypeBuiltin typ Empty typ []) es = (INL (Value (default_value rt)),es)
Proof
  strip_tac >>
  simp[Once evaluate_def, evaluate_type_builtin_def, bind_def, return_def,
       lift_option_def, lift_sum_def] >>
  simp[Once evaluate_def, ignore_bind_def, type_check_def,
       type_builtin_args_length_ok_def, bind_def, return_def, assert_def]
QED

Theorem empty_buffer_pointer_post[local]:
  evaluate_type (get_tenv cx) typ = SOME rt /\ sz = type_memory_size rt /\
  type_memory_bytes cenv typ = sz /\ buf.buf_operand = Var p /\
  lookup_var p t = SOME w /\ ptr_covers G tn p t sz /\
  header = (is_bytestring_type typ \/ (case typ of ArrayT _ (Dynamic _) => T | _ => F)) /\
  (if header then mem_word_at (w2n w) t.vs_memory = 0w
   else mem_bytes_at (w2n w) sz t.vs_memory = REPLICATE sz 0w) /\
  (!i. w2n w <= i /\ i < w2n w + (if header then 32 else sz) ==> i NOTIN tn.t_mem) ==>
  ptr_vv_ok cx typ (Value (default_value rt)) (LocatedValue typ (base_ptr buf)) es G tn t /\
  ptr_buf_ok cenv (TypeBuiltin typ Empty typ []) buf.buf_operand G t
Proof
  strip_tac >>
  `!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
    val_in_memory rt (default_value rt) (w2n w) mem` by
    (rpt strip_tac >> irule empty_buffer_default >> goal_assum (drule_at Any) >>
     qpat_assum `header = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
     qpat_assum `sz = type_memory_size rt` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
     Cases_on `header` >> RULE_ASSUM_TAC (REWRITE_RULE [COND_CLAUSES]) >>
     REWRITE_TAC [COND_CLAUSES]
     >- (`mem_bytes_at (w2n w) 32 mem = mem_bytes_at (w2n w) 32 t.vs_memory` by
           (irule clean_memory_window >> qexists_tac `tn.t_mem` >> simp[]) >>
         fs[mem_word_at_def, mem_bytes_at_def]) >>
     `mem_bytes_at (w2n w) sz mem = mem_bytes_at (w2n w) sz t.vs_memory` by
       (irule clean_memory_window >> qexists_tac `tn.t_mem` >> simp[]) >>
     simp[]) >>
  conj_tac
  >- (gvs[ptr_vv_ok_def, base_ptr_def, ptr_mem_ok_def, ptr_covers_def,
           eval_operand_def, read_result_def, return_def] >>
      rpt strip_tac >>
      `val_store_size rt (default_value rt) <= type_memory_size rt` by
        simp[val_store_size_le, val_wf_default_value_proof] >> decide_tac) >>
  qpat_assum `buf.buf_operand = Var p` (fn th => rewrite_tac [th]) >>
  irule ptr_buf_ok_from_covers >>
  simp[expr_type_def, lowered_value_type_def] >>
  qexistsl_tac [`sz`,`tn`] >> simp[]
QED

Theorem empty_buffer_value_posts[local]:
  evaluate_type (get_tenv cx) typ = SOME rt /\ ~is_word_type typ /\
  sz = type_memory_size rt /\ val_in_memory rt (default_value rt) (w2n w) t.vs_memory /\
  stmt_state_rel H ctx func cenv cx es t /\ storage_well_formed_on cx es (FST H) /\
  eval_operand buf.buf_operand t = SOME w /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
  sa.cs_next_id < sb.cs_next_id /\ local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP t.vs_allocas aid = SOME entry) /\
  (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
     regions_disjoint (w2n w) sz b len) /\
  (!a len. a+len <= w2n w \/ w2n w+sz <= a ==>
     mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
  (!name b len. local_region cenv es.scopes s name b len ==>
     w2n w+sz <= b \/ b+len <= w2n w) /\ pure_frame cenv func es sa s t ==>
  vv_post H ctx func cenv cx (TypeBuiltin typ Empty typ []) es sa sb s es
    (Value (default_value rt)) (LocatedValue typ (base_ptr buf)) t /\
  vv_store_bound cx typ typ es (Value (default_value rt)) (LocatedValue typ (base_ptr buf)) t /\
  vv_own cenv cx typ sa sb es (Value (default_value rt)) (LocatedValue typ (base_ptr buf)) t
Proof
  strip_tac >> qpat_x_assum `sz = type_memory_size rt` SUBST_ALL_TAC >>
  `!n b len. local_region cenv es.scopes t n b len ==>
     w2n w + type_memory_size rt <= b \/ b+len <= w2n w` by
    (drule_all_then assume_tac copy_buffer_local_region_frame >>
     rpt strip_tac >> qpat_assum `!name b len. local_region _ _ s _ _ _ ==> _` irule >>
     qexists_tac `n` >> qpat_assum `!scopes name b sz. _ <=> _`
       (fn th => fs[GSYM th])) >>
  conj_asm1_tac
  >- (irule (SRULE [expr_type_def]
        (Q.SPECL [`func`,`cenv`,`cx`,`TypeBuiltin typ Empty typ []`] buffer_memory_vv_post)) >>
      simp[base_ptr_def] >> conj_tac
      >- (rpt strip_tac >> qpat_assum `!a len. _ ==> mem_bytes_at a len _ = _` irule >>
          qpat_assum `!name b len. local_region _ _ s _ _ _ ==> _` (drule_then mp_tac) >>
          simp[DISJ_COMM]) >>
      conj_tac
      >- (rpt strip_tac >> qpat_assum `!a len. _ ==> mem_bytes_at a len _ = _` irule >>
          qpat_assum `!aid b len. _ ==> regions_disjoint _ _ b len`
            (drule_all_then mp_tac) >> simp[regions_disjoint_def, DISJ_COMM]) >>
      simp[val_wf_default_value_proof, val_footprint_le] >>
      rpt strip_tac >> qpat_assum `!n b len. local_region _ _ t _ _ _ ==> _`
        (drule_then mp_tac) >> simp[]) >>
  conj_tac
  >- (drule_all aggregate_alloca_capacity_mem >> strip_tac >>
      irule (SRULE [expr_type_def, post_value_type_def, lowered_value_type_def]
        (Q.INST [`e` |-> `TypeBuiltin typ Empty typ []`] vv_store_bound_capacity)) >>
      conj_tac >- (qexistsl_tac [`rt`,`w`] >> simp[base_ptr_def]) >>
      simp[] >> goal_assum drule >> simp[]) >>
  simp[vv_own_def, base_ptr_def, read_result_def, return_def] >>
  disj1_tac >> qexistsl_tac [`sa.cs_next_id`,`w2n w`,`type_memory_size rt`] >>
  simp[val_footprint_le, val_wf_default_value_proof] >> rpt strip_tac >>
  qpat_assum `!n b len. local_region _ _ t _ _ _ ==> _` (drule_then mp_tac) >> simp[]
QED

Theorem empty_buffer_history[local]:
  compile_builtin_empty_complex sz header sa = (buf,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel H ctx func cenv cx es s /\ alloca_history func s /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >> drule_then strip_assume_tac compile_builtin_empty_complex_shape >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (qpat_x_assum `isPREFIX _ _` mp_tac >> rewrite_tac[IS_PREFIX_APPEND] >>
     strip_tac >> asm_rewrite_tac[emitted_insts_def, DROP_LENGTH_APPEND]) >>
  irule emitted_alloca_history >> simp[] >>
  qexistsl_tac [`emitted_insts sa sb`,`s`,`sa`] >> simp[] >>
  fs[EVERY_MEM] >> rpt strip_tac >> res_tac
QED

Theorem empty_buffer_run_frames[local]:
  compile_builtin_empty_complex sz header sa = (buf,sb) /\
  fn_has_code sa sb func /\
  stmt_state_rel (H : (bool # 256 word # type_value) list # num list) ctx func cenv cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  sz < dimword (:256) /\ (if header then 32 <= sz else sz MOD 32 = 0) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  immutable_frame_mods func cenv cx es s /\ ghost_inv_at_mods D lo d cenv cx es G tn s /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s Gf tnf /\
  s.vs_alloca_next <= t.vs_alloca_next ==>
  immutable_frame_mods func cenv cx es t /\
  ghost_inv_at_mods D lo d cenv cx es Gf tnf t /\ ghost_kept_at lo cenv es sa G tn s Gf tnf
Proof
  strip_tac >> drule_all empty_run_effects >> strip_tac >>
  drule_then assume_tac method_id_ghost_at_zero >>
  `ghost_inv_at D 0 d cenv cx es Gf tnf t /\ ghost_kept_at 0 cenv es sa G tn s Gf tnf` by
    (irule empty_buffer_indexed_frames >> simp[] >> goal_assum (drule_at Any) >>
     qexistsl_tac [`H`,`buf`,`header`,`sz`] >> simp[]) >>
  drule_all compile_builtin_empty_complex_run >> strip_tac >> gvs[] >>
  rename1 `FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz)` >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `lo <= w2n w` by
    (qpat_assum `!aid b n. FLOOKUP t.vs_allocas aid = _ ==> _`
      (drule_then strip_assume_tac) >- (fs[allocas_from_def] >> res_tac) >> decide_tac) >>
  conj_tac >- suspend "immutable" >>
  conj_tac
  >- (irule empty_linked_ghost >> simp[] >> goal_assum (drule_at Any) >>
      qexistsl_tac [`G`,`sa`,`tn`] >> simp[]) >>
  qpat_assum `ghost_kept_at 0 _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [ghost_kept_at_def]) >> rewrite_tac[ghost_kept_at_def]
QED
Resume empty_buffer_run_frames[immutable]:
  drule_then strip_assume_tac compile_builtin_empty_complex_shape >>
  drule_all_then strip_assume_tac run_inst_seq_data_section >>
  drule_then assume_tac run_inst_seq_memory_length >>
  irule empty_linked_immutable >> simp[] >>
  qexistsl_tac [`w2n w`,`mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]`,
                 `sz`,`s`,`sa`] >> simp[mk_inst_def] >>
  rpt strip_tac >> qpat_assum `!a len. _ ==> mem_bytes_at a len _ = _` irule >> simp[]
QED
Finalise empty_buffer_run_frames

Theorem empty_buffer_vv_sim[local]:
  ~is_word_type typ /\ evaluate_type (get_tenv cx) typ = SOME rt /\
  type_memory_bytes cenv typ = type_memory_size rt /\
  type_memory_bytes cenv typ < dimword (:256) ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TypeBuiltin typ Empty typ []) es
Proof
  strip_tac >> rewrite_tac[expr_vv_sim_full_mods_def] >> rpt gen_tac >> strip_tac >>
  drule_then assume_tac empty_buffer_eval >>
  drule_all empty_buffer_compile >> strip_tac >>
  Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- (fs[storage_trace_domain_def] >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
      suspend "allocate") >>
  irule gas_outcome_full_mods_bad_nil >> simp[empty_buffer_eval]
QED
Resume empty_buffer_vv_sim[allocate]:
  qmatch_asmsub_abbrev_tac `compile_builtin_empty_complex _ header sa` >>
  `if header then 32 <= type_memory_bytes cenv typ else type_memory_bytes cenv typ MOD 32 = 0` by
    (drule empty_buffer_size >> simp[Abbr `header`]) >>
  drule_all compile_builtin_empty_complex_run >> strip_tac >>
  drule_all empty_buffer_uniform_run >> disch_then (qspecl_then [`PG`,`G0`,`tn0`] strip_assume_tac) >>
  drule_all_then assume_tac empty_buffer_history >>
  irule gas_outcome_full_mods_pure >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gf`,`es`,`INL (Value (default_value rt))`,
                 `t with vs_inst_idx := LENGTH sb.cs_current_insts`,`tnf`] >>
  simp[empty_buffer_eval] >> gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `allocas_from lo s0 /\ lo <= s0.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  conj_tac
  >- (qpat_assum `!D lo explicit. allocas_from lo s0 /\ _ ==> gas_origin_ptr_path _ _ _ _`
        irule >> simp[]) >>
  simp[post_value_type_def, lowered_value_type_def, expr_type_def] >>
  suspend "finish"
QED
Resume empty_buffer_vv_sim[finish]:
  `inst_seq_ptr (DF H) 0 ctx func PG G0 tn0 (emitted_insts sa sb) s0 Gf tnf` by
    (qpat_assum `!D lo. allocas_from lo s0 /\ _ ==> inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
        irule >> simp[allocas_from_def]) >>
  drule_all empty_buffer_run_frames >> strip_tac >>
  drule_all compile_builtin_empty_complex_run >> strip_tac >>
  gvs[eval_operand_def] >>
  `eval_operand buf.buf_operand t = SOME w` by simp[eval_operand_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  `val_in_memory rt (default_value rt) (w2n w) t.vs_memory` by
    (irule empty_buffer_default >> goal_assum (drule_at Any) >> fs[Abbr `header`]) >>
  `vv_post H ctx func cenv cx (TypeBuiltin typ Empty typ []) es sa sb s0 es
      (Value (default_value rt)) (LocatedValue typ (base_ptr buf)) t /\
   vv_store_bound cx typ typ es (Value (default_value rt)) (LocatedValue typ (base_ptr buf)) t /\
   vv_own cenv cx typ sa sb es (Value (default_value rt)) (LocatedValue typ (base_ptr buf)) t` by
    (irule empty_buffer_value_posts >> simp[] >>
     rpt conj_tac >> rpt strip_tac >> first_assum (drule_then mp_tac) >> simp[]) >>
  `header = (is_bytestring_type typ \/ (case typ of ArrayT _ (Dynamic _) => T | _ => F))` by
    simp[Abbr `header`] >>
  `ptr_vv_ok cx typ (Value (default_value rt)) (LocatedValue typ (base_ptr buf)) es Gf tnf t /\
   ptr_buf_ok cenv (TypeBuiltin typ Empty typ []) buf.buf_operand Gf t` by
    (irule empty_buffer_pointer_post >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`header`,`p`,`type_memory_size rt`,`w`] >>
     rpt conj_tac >> (REFL_TAC ORELSE first_assum ACCEPT_TAC)) >>
  suspend "indexed_posts"
QED
Resume empty_buffer_vv_sim[indexed_posts]:
  qpat_x_assum `header <=> _` kall_tac >>
  qpat_x_assum `Abbrev (header <=> _)` kall_tac >>
  simp[vv_location_def, base_ptr_def, empty_post_gas_obs] >>
  conj_tac >- suspend "linked_post" >>
  conj_tac
  >- (qpat_x_assum `vv_store_bound _ _ _ es _ _ t`
        (mp_tac o REWRITE_RULE [vv_store_bound_def]) >>
      simp[vv_store_bound_def, base_ptr_def, read_result_def, return_def, eval_operand_def]) >>
  conj_tac
  >- (qpat_assum `stmt_state_rel H _ _ _ _ _ t`
        (mp_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
      DISCH_THEN ACCEPT_TAC) >>
  conj_tac
  >- (qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ es Gf tnf t` mp_tac >>
      Cases_on `d`
      >- (simp[ghost_inv_at_mods_def, ptr_covers_def, lookup_var_def, return_buf_ptr_def,
               stor_taint_ok_at_def, allocas_from_def] >>
          strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      rename1 `ghost_inv_at_mods _ _ (SOME pair) _ _ _ _ _ _` >> PairCases_on `pair` >>
      simp[ghost_inv_at_mods_def, ptr_covers_def, lookup_var_def, return_buf_ptr_def,
           stor_taint_ok_at_def, allocas_from_def] >>
      strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_x_assum `ptr_vv_ok _ _ _ _ es Gf tnf t` mp_tac >>
      simp[ptr_vv_ok_def, ptr_mem_ok_def, base_ptr_def, read_result_def, return_def]) >>
  conj_tac
  >- (qpat_x_assum `vv_own _ _ _ _ _ es _ _ t` mp_tac >>
      simp[vv_own_def, base_ptr_def, read_result_def, return_def, local_region_def, lookup_var_def]) >>
  qpat_assum `buf.buf_operand = Var p` (fn th => rewrite_tac[GSYM th]) >>
  first_assum ACCEPT_TAC
QED
Resume empty_buffer_vv_sim[linked_post]:
  `immutable_frame_mods func cenv cx es (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule immutable_frame_mods_exterior_frame >>
     qexistsl_tac [`es`,`t`,`sa`] >> simp_tac (srw_ss()) [lookup_var_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `vv_post H _ _ _ _ _ _ _ _ _ es _ _ t` mp_tac >>
  simp[vv_post_mods_def, vv_post_def, vv_holds_mods_def, vv_place_ptr_mods_def,
       post_value_type_def, expr_type_def, base_ptr_def, vv_holds_def, vv_at_def,
       vv_place_ptr_def, vv_storage_live_def, locals_kept_def, stmt_state_rel_inst_idx,
       read_result_def, return_def, empty_post_gas_obs, local_region_def, lookup_var_def,
       popped_kept_def, eval_operand_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >> conj_tac
  >- (rpt strip_tac >> fs[lookup_var_def]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise empty_buffer_vv_sim

Theorem empty_buffer_lower[local]:
  ~is_word_type typ /\
  compile_expr cenv ty e sa = (LocatedValue typ (base_ptr buf),sb) ==>
  lower_value compile_expr cenv ty e sa = (buf.buf_operand,sb)
Proof
  simp[lower_value_def, comp_bind_def] >> strip_tac >>
  simp[unwrap_value_def, base_ptr_def, comp_return_def]
QED

Theorem empty_buffer_cuts[local]:
  ~is_word_type typ /\ gas_shadow_state sa shadow_sa /\
  lower_value compile_expr cenv ty (TypeBuiltin typ Empty typ []) sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (TypeBuiltin typ Empty typ [])) shadow_sa = (op,shadow_sb) ==>
  ?buf. compile_expr cenv ty (TypeBuiltin typ Empty typ []) sa = (LocatedValue typ (base_ptr buf),sb) /\
        compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (TypeBuiltin typ Empty typ []))
          shadow_sa = (LocatedValue typ (base_ptr buf),shadow_sb) /\ op = buf.buf_operand
Proof
  strip_tac >>
  Cases_on `compile_expr cenv ty (TypeBuiltin typ Empty typ []) sa` >>
  drule_all empty_buffer_compile >> strip_tac >> gvs[] >>
  Cases_on `compile_expr (gas_shadow_env T cenv) ty
      (gas_shadow_expr (TypeBuiltin typ Empty typ [])) shadow_sa` >>
  `q = LocatedValue typ (base_ptr buf)` by
    (mp_tac (Q.INST [`sd` |-> `T`, `e` |-> `TypeBuiltin typ Empty typ []`]
        gas_shadow_stmt_compile_expr_env) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  qpat_x_assum `q = _` SUBST_ALL_TAC >>
  `lower_value compile_expr cenv ty (TypeBuiltin typ Empty typ []) sa =
     (buf.buf_operand,r)` by (irule empty_buffer_lower >> simp[]) >>
  `lower_value compile_expr (gas_shadow_env T cenv) ty
      (gas_shadow_expr (TypeBuiltin typ Empty typ [])) shadow_sa =
     (buf.buf_operand,r')` by (irule empty_buffer_lower >> simp[]) >>
  qexists_tac `buf` >> gvs[]
QED

Theorem empty_buffer_value_sim[local]:
  ~is_word_type typ /\ evaluate_type (get_tenv cx) typ = SOME rt /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TypeBuiltin typ Empty typ []) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TypeBuiltin typ Empty typ []) es
Proof
  strip_tac >> drule_then assume_tac empty_buffer_eval >>
  irule materialized_value_from_vv_mods >> simp[] >>
  rpt gen_tac >> strip_tac >> drule_all empty_buffer_cuts >> strip_tac >>
  qexists_tac `LocatedValue typ (base_ptr buf)` >> simp[] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `(base_ptr buf).ptr_location = LocMemory` by simp[base_ptr_def] >>
  `ptr_buf_ok cenv (TypeBuiltin typ Empty typ []) (base_ptr buf).ptr_operand G t`
    by (qpat_assum `_ ==> ptr_buf_ok _ _ _ _ _` irule >> simp[]) >>
  drule_all (SRULE [] (Q.INST [`e` |-> `TypeBuiltin typ Empty typ []`]
    memory_buffer_read_post_mods)) >>
  disch_then strip_assume_tac >> fs[base_ptr_def]
QED

Theorem empty_buffer_route_mods:
  !mods exps cx ann typ xs. ~is_word_type typ ==>
    body_expr_full_ok_mods mods exps cx (TypeBuiltin ann Empty typ xs)
Proof
  rpt gen_tac >> strip_tac >> simp[Once body_expr_full_ok_mods_def] >>
  rpt gen_tac >> strip_tac >> drule_all empty_buffer_ready >> strip_tac >> gvs[] >>
  reverse conj_asm2_tac
  >- (irule empty_buffer_vv_sim >> simp[] >> goal_assum drule >> simp[]) >>
  irule empty_buffer_value_sim >> simp[] >> goal_assum drule >> simp[]
QED
