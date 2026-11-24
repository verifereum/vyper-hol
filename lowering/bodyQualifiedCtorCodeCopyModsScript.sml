(* Force a qualified immutable at its constructor-memory offset. *)
Theory bodyQualifiedCtorCodeCopyMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit immutableRegionFrameProps
  bodyFullUnwrapCodeCtorRun context fragExec vyperStorageFootprint stateRelProj
  exprSimMemDefs vyperAST vyperTypeValues
  bodyFullUnwrapCodeCtorFrame bodyFullUnwrapSlotPost bodyFullHashKeccakFixed
  exprPtrUnwrapAllocationFrame exprPtrUnwrapAllocSemantic exprPtrUnwrapRetained
  bodyPtrEnvBuiltinsBoundary fragGasOriginPtrDead bodyFieldMemoryProps
  exprSimCopy exprSimAlloc exprSimProps exprLoweringProps exprLowering
  immutableCopyExecution immutableMemoryFrame exprPtrUnwrapAllocSeparation
  allocationPtr bufferAllocationExecution valueEncodingProps valueEncodingDefs
  exprPtrUnwrapCodeCopyShape exprPtrUnwrapAllocEntry exprSimStorageCopy freshWrites
  vyperExprEffects wordArgsPtr exprSimWordArgs loweringSlice bodyPtrDefs
  exprPtrUnwrapAllocation bodyPtrMakeArrayMemoryFrame emitHelper
  instIdxIndep loweringPosts loweringStateRelDefs ptrDiscipline finite_map
  venomState venomInst compileEnv arithmetic words pred_set

Theorem qualified_ctor_code_copy_read_mods:
  cenv.ce_is_ctor /\ ee.scopes = es.scopes /\ ee.immutables = es.immutables /\
  ~is_word_type ann /\ evaluate_type (get_tenv cx) ann = SOME rt /\
  value_has_type rt v /\ type_memory_bytes cenv ann = type_memory_size rt /\
  type_memory_size rt < 2**64 /\
  w2n (n2w off : bytes32) + type_memory_size rt <= lo /\
  w2n (n2w off : bytes32) + type_memory_size rt < dimword (:256) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory rt v (w2n (n2w off : bytes32)) mem) /\
  compile_expr cenv ty (TopLevelName ann (src,id)) sa =
    (LocatedValue ann (mk_ptr (Lit (n2w off)) LocCode),sa) /\
  lower_value compile_expr cenv ty (TopLevelName ann (src,id)) sa = (op,sb) /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    immutable_frame_mods func cenv cx ee s /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s) ==>
  ?z G' tn'. !H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,G',tn') /\
     expr_post_mods H ctx func cenv cx (TopLevelName ann (src,id)) es sa sb s ee v op z /\
     expr_store_bound cx (post_value_type cenv (TopLevelName ann (src,id))) v op z /\
     z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
     alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
     s.vs_alloca_next <= z.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G' tn' z /\
     ptr_val_ok cx (post_value_type cenv (TopLevelName ann (src,id))) v op G' tn' z /\
     ptr_buf_ok cenv (TopLevelName ann (src,id)) op G' z /\
     ghost_kept_at lo cenv es sa G tn s G' tn'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qabbrev_tac `nb = type_memory_size rt` >>
  qabbrev_tac `n = type_slot_size rt` >>
  `nb = 32*n` by simp[Abbr `nb`, Abbr `n`, type_memory_size_slots] >>
  `(nb + 31) DIV 32 = n` by simp[ADD_DIV_ADD_DIV] >>
  `nb < dimword (:256)` by (fs[Abbr `nb`, dimword_def] >> decide_tac) >>
  `?buf mid. compile_alloc_buffer nb sa = (buf,mid) /\
      compile_imm_copy_to_memory T cenv.ce_imm_alloca (Lit (n2w off)) buf.buf_operand n 0 mid =
        ((),sb) /\ op = buf.buf_operand` by
    (qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
     simp[lower_value_def, unwrap_value_def, mk_ptr_def, compile_ensure_in_memory_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> metis_tac[]) >>
  `ci_mono sa mid /\ ci_mono mid sb` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_compile_imm_copy_to_memory, pairTheory.SND] >>
  `fn_has_code sa mid func /\ fn_has_code mid sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[Abbr `H0`, storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  `n <> 0 ==> !region. cenv.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region /\
    op_taint tn region = {} /\ op_prov G region = NONE` by
    (disch_tac >> gen_tac >> disch_tac >> `lo <> 0` by decide_tac >>
     drule_then assume_tac stmt_state_rel_immutable_base_zero >>
     conj_tac >- fs[immutable_base_zero_def] >>
     Cases_on `region` >>
     fs[copy_old_operand_def, op_taint_def, op_prov_def, ghost_inv_at_mods_def] >>
     metis_tac[local_ptrs_reserved_imm_base]) >>
  qabbrev_tac `srcw:bytes32 = n2w off` >>
  `eval_operand (Lit srcw) s = SOME srcw /\ op_taint tn (Lit srcw) = {} /\
    op_prov G (Lit srcw) = NONE /\ (!x. Lit srcw = Var x ==> not_fresh_at sa x) /\
    w2n srcw + 32*n <= lo` by simp[eval_operand_def, op_taint_def, op_prov_def] >>
  drule_all ctor_code_copy_origin_execution >>
  disch_then (qspecl_then [`explicit`,`PG`,
     `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]
     strip_assume_tac) >>
  rename1 `copy_runtime_frame mid a sb z` >>
  rename1 `lookup_var root a = SOME dst` >>
  suspend "endpoint"
QED

Resume qualified_ctor_code_copy_read_mods[endpoint]:
  `a.vs_memory = s.vs_memory` by
    (drule unwrap_alloc_runtime_frame >> simp[] >> metis_tac[]) >>
  `buffer_allocation_base s sa.cs_next_id < dimword(:256)` by
    (drule_all unwrap_alloc_site_bound >> decide_tac) >>
  `w2n dst = buffer_allocation_base s sa.cs_next_id` by simp[] >>
  `lo <= w2n dst` by
    (simp[] >> Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >>
     fs[buffer_allocation_base_def, allocas_from_def] >>
     PairCases_on `x` >> fs[] >> metis_tac[]) >>
  `32*n <= nb` by decide_tac >>
  drule_all ctor_code_copy_exterior_frames >> strip_tac >>
  `not_fresh_at mid root` by
    (drule allocated_copy_operands_old >> disch_then (qspec_then `Lit srcw` mp_tac) >> simp[]) >>
  `copy_static z = copy_static u /\
   (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u)` by
    (qpat_assum `copy_runtime_frame _ _ _ _` mp_tac >>
     qpat_assum `a = u with vs_inst_idx := _` (fn th => PURE_REWRITE_TAC [th]) >>
     simp[copy_runtime_frame_def, lookup_var_def, copy_static_def]) >>
  `lookup_var root z = SOME dst` by
    (qpat_assum `!x. not_fresh_at mid x ==> lookup_var x z = _`
       (qspecl_then [`root`] mp_tac) >>
     qpat_assum `lookup_var root a = SOME dst` mp_tac >>
     qpat_assum `a = u with vs_inst_idx := _` (fn th => PURE_REWRITE_TAC [th]) >>
     simp[lookup_var_def]) >>
  `tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm` by
    fs[step_taint_def, mk_inst_def, adopt_reset_def, store_taint_def, imm_taint_def] >>
  `op = Var root` by metis_tac[] >>
  `z.vs_memory = (immutable_transfers F T srcw dst n 0 a).vs_memory` by
    suspend "raw_memory" >>
  `regions_disjoint (w2n srcw) nb (w2n dst) nb` by
    (rewrite_tac[regions_disjoint_def] >> decide_tac) >>
  `val_wf rt v` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  `val_footprint rt v <= nb /\ val_store_size rt v <= nb` by
    simp[Abbr `nb`, val_footprint_le, val_store_size_le] >>
  `ptr_val_ok cx ann v (Var root) HG tf (z with vs_inst_idx := LENGTH sb.cs_current_insts) /\
   val_in_memory rt v (w2n dst) z.vs_memory /\ LENGTH u.vs_memory <= LENGTH z.vs_memory` by
    suspend "copied_value" >>
  `u = update_var root dst (buffer_allocation_fields s sa.cs_next_id nb)` by simp[] >>
  `sa.cs_next_id < sb.cs_next_id /\ sa.cs_next_var <= mid.cs_next_var` by
    suspend "compiler_growth" >>
  qexistsl_tac [`z with vs_inst_idx := LENGTH sb.cs_current_insts`, `HG`, `tf`] >>
  gen_tac >> disch_tac >>
  conj_tac >- (irule gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC) >>
  suspend "linked_endpoint"
QED

(* Empty arrays still allocate; only the copy instruction interval is empty. *)
Resume qualified_ctor_code_copy_read_mods[raw_memory]:
  Cases_on `n = 0`
  >- gvs[compile_imm_copy_to_memory_def, comp_return_def,
         copy_runtime_frame_def, immutable_transfers_def, run_inst_seq_def] >>
  `!region. cenv.ce_imm_alloca = SOME region ==>
      eval_operand region a = SOME 0w /\ copy_old_operand mid region` by
    (gen_tac >> disch_tac >>
     `eval_operand region s = SOME 0w /\ copy_old_operand sa region` by metis_tac[] >>
     `!x. region = Var x ==> x <> root` by
       (fs[copy_old_operand_def] >> metis_tac[unwrap_alloc_old_operand_distinct]) >>
     conj_tac >- (drule_all unwrap_alloc_operand_frame >> simp[] >> metis_tac[]) >>
     metis_tac[copy_old_operand_mono, ci_mono_def]) >>
  `eval_operand (Var root) a = SOME dst` by simp[eval_operand_def] >>
  `copy_old_operand mid (Var root) /\ copy_old_operand mid (Lit srcw) /\
   eval_operand (Lit srcw) a = SOME srcw` by simp[copy_old_operand_def, eval_operand_def] >>
  `compile_imm_copy_to_memory T cenv.ce_imm_alloca (Lit srcw) (Var root) n 0 mid =
    ((),sb)` by
    (qpat_assum `buf.buf_operand = Var root` (fn eq =>
       qpat_assum `compile_imm_copy_to_memory T _ _ buf.buf_operand _ _ _ = _`
         (ACCEPT_TAC o PURE_REWRITE_RULE [eq]))) >>
  drule_all copy_ctor_run >> strip_tac >>
  `zz = z` by fs[copy_runtime_frame_def] >> gvs[]
QED

Resume qualified_ctor_code_copy_read_mods[copied_value]:
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) (fn_insts func)` by
    (drule unwrap_alloc_generated_code >> strip_tac >> drule_all buffer_alloc_code >> gvs[]) >>
  `!i. i < w2n dst \/ w2n dst + nb <= i ==> (i IN tm.t_mem <=> i IN tn.t_mem)` by
    (drule_all unwrap_alloc_taint_frame >> disch_then (qspec_then `tn` strip_assume_tac) >>
     qpat_assum `tm = _` SUBST1_TAC >>
     qpat_assum `w2n dst = _` SUBST1_TAC >>
     qpat_assum `!i. _ ==> (i IN (step_taint _ _ _ _).t_mem <=> _)` ACCEPT_TAC) >>
  `!mem. mem_agree_outside tm.t_mem a.vs_memory mem ==>
     val_in_memory rt v (w2n srcw) mem` by
    (gen_tac >> disch_tac >> irule robust_val_in_memory_shrinking_frame >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`tn.t_mem`,`tm.t_mem`,`s.vs_memory`,`a.vs_memory`,`nb`] >>
     simp[] >> rpt strip_tac >>
     `i < w2n dst` by decide_tac >> metis_tac[]) >>
  `!i. i < nb ==> (w2n dst+i IN tf.t_mem <=> w2n srcw+i IN tm.t_mem)` by
    (rpt strip_tac >>
     qpat_assum `!j. j IN tf.t_mem <=> _` (qspec_then `w2n dst+i` SUBST1_TAC) >>
     `w2n dst <= w2n dst+i /\ w2n dst+i < w2n dst+32*n /\
      w2n dst+i-w2n dst = i` by (gvs[] >> decide_tac) >> simp[]) >>
  `ptr_val_ok cx ann v (Var root) HG tf (z with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule ctor_code_copy_ptr_val_ok >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`a`, `dst`, `nb`, `srcw`, `tm`, `rt`] >>
     qpat_assum `Abbrev (nb = _)` (fn th =>
       qpat_assum `Abbrev (n = _)` (fn th' =>
         PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th),
                           GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th')])) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qpat_assum `ptr_val_ok _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [ptr_val_ok_def, ptr_mem_ok_def]) >>
      strip_tac >>
      qpat_assum `~is_word_type ann ==> !tv w. _` drule >>
      disch_then (qspecl_then [`rt`,`dst`] mp_tac) >>
      `eval_operand (Var root) (z with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME dst` by
        (pure_rewrite_tac[eval_operand_def, lookup_var_def, venom_state_accfupds] >>
         qpat_assum `lookup_var root z = _` (ACCEPT_TAC o REWRITE_RULE [lookup_var_def])) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      strip_tac >> first_assum irule >> simp[mem_agree_outside_def]) >>
  Cases_on `n = 0`
  >- fs[immutable_transfers_def, copy_static_def] >>
  `type_slot_size rt <> 0 /\ w2n srcw + type_memory_size rt < dimword (:256) /\
   w2n dst + type_memory_size rt < dimword (:256) /\
   regions_disjoint (w2n srcw) (type_memory_size rt) (w2n dst) (type_memory_size rt)` by
     (qpat_assum `Abbrev (nb = _)` (fn th =>
        qpat_assum `Abbrev (n = _)` (fn th' =>
          PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th),
                            GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th')])) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all copy_ctor_memory_snapshot >> disch_then (qspec_then `a` assume_tac) >>
  `u.vs_memory = a.vs_memory` by fs[] >>
  fs[Abbr `n`, immutableMemoryFrameTheory.immutable_write_memory_capacity]
QED

Resume qualified_ctor_code_copy_read_mods[compiler_growth]:
  `sa.cs_next_id < mid.cs_next_id` by
    (qpat_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[compile_alloc_buffer_def, emitHelperTheory.emit_op_def, fresh_var_def, fresh_id_def,
       emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >> rpt strip_tac >> gvs[]) >>
  fs[ci_mono_def] >> decide_tac
QED

Resume qualified_ctor_code_copy_read_mods[linked_endpoint]:
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  drule_all unwrap_alloc_semantic_frames >> strip_tac >>
  drule_then strip_assume_tac copy_static_fields >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) (fn_insts func)` by
    (drule unwrap_alloc_generated_code >> strip_tac >> drule_all buffer_alloc_code >> gvs[]) >>
  `local_ptrs_reserved cenv mid` by metis_tac[local_ptrs_reserved_next_var] >>
  `!name b len. local_region cenv ee.scopes s name b len ==>
     b+len <= w2n dst \/ w2n dst+nb <= b` by
    (rpt strip_tac >> drule_all unwrap_alloc_local_separation >> simp[] >> metis_tac[]) >>
  `!name b len. local_region cenv ee.scopes z name b len <=>
                local_region cenv ee.scopes s name b len` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >> qexists_tac `sa` >>
     simp[] >> gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x z = _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  `stmt_state_rel H ctx func cenv cx ee z` by suspend "semantic_state" >>
  `immutable_frame_mods func cenv cx ee z` by suspend "immutable_frame" >>
  `ghost_inv_at_mods (DF H) lo d cenv cx ee HG tf z` by suspend "ghost_frame" >>
  `ghost_kept_at lo cenv es sa G tn s HG tf /\
   wb_frame cenv ee ee sa s z /\ pure_frame cenv func ee sa s z` by
    suspend "retention" >>
  suspend "post"
QED

Resume qualified_ctor_code_copy_read_mods[semantic_state]:
  irule copy_buffer_state_rel_frame >>
  goal_assum (drule_at (Pat `copy_static _ = _`)) >>
  goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`w2n dst`, `mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]`, `mid`, `nb`] >>
  `!name b len. local_region cenv ee.scopes u name b len ==>
     w2n dst+nb <= b \/ b+len <= w2n dst` by
    (rpt strip_tac >> qpat_assum `!name b len. local_region cenv ee.scopes u name b len ==> regions_disjoint _ _ _ _`
       (drule_then (mp_tac o REWRITE_RULE [regions_disjoint_def])) >> decide_tac) >>
  `!p k. p+k <= w2n dst \/ w2n dst+nb <= p ==>
    mem_bytes_at p k z.vs_memory = mem_bytes_at p k u.vs_memory` by
    (qpat_assum `u.vs_memory = s.vs_memory` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
    (pure_rewrite_tac[mk_inst_def, instruction_accessors, instruction_accfupds, combinTheory.K_THM] >>
     (REFL_TAC ORELSE first_assum ACCEPT_TAC)))
QED

Resume qualified_ctor_code_copy_read_mods[immutable_frame]:
  `!aid b k. FLOOKUP z.vs_allocas aid = SOME (b,k) ==>
      FLOOKUP s.vs_allocas aid = SOME (b,k) \/ s.vs_alloca_next <= b` by
    (qpat_assum `z.vs_allocas = u.vs_allocas` SUBST1_TAC >>
     qpat_assum `u = update_var _ dst _` SUBST1_TAC >>
     simp[buffer_allocation_fields_def, update_var_def] >>
     Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >>
     simp[FLOOKUP_UPDATE] >> rpt strip_tac >> Cases_on `sa.cs_next_id = aid` >> gvs[]) >>
  `!src'. !id b k. local_region (cenv with ce_module := src') ee.scopes z id b k ==>
      local_region (cenv with ce_module := src') ee.scopes s id b k` by
    (rpt gen_tac >> simp_tac bool_ss [local_region_def,compile_env_accfupds] >>
     disch_then strip_assume_tac >>
     rename1 `lookup_var p z = SOME w` >>
     `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
     qexistsl_tac [`entry`,`p`,`w`] >> metis_tac[]) >>
  `immutable_alloca_sep_mods func cenv cx ee z` by
    (rewrite_tac[immutable_alloca_sep_mods_def] >> rpt strip_tac >>
     irule immutable_alloca_sep_frame >> qexistsl_tac [`s`, `ee`] >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
       (fs[immutable_frame_mods_def, immutable_alloca_sep_mods_def] >> metis_tac[]))) >>
  `z.vs_data_section = s.vs_data_section` by
    (qpat_assum `z.vs_data_section = u.vs_data_section` SUBST1_TAC >>
     qpat_assum `u = update_var _ dst _` SUBST1_TAC >>
     simp[buffer_allocation_fields_def, update_var_def] >>
     Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >> simp[]) >>
  `LENGTH s.vs_memory <= LENGTH z.vs_memory` by metis_tac[] >>
  rewrite_tac[immutable_frame_mods_def] >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  rewrite_tac[immutables_rel_mods_def] >> rpt strip_tac >>
  irule immutables_rel_mem_agree >> qexists_tac `s` >> rpt conj_tac
  >- (fs[immutable_frame_mods_def, immutables_rel_mods_def] >> metis_tac[])
  >- first_assum ACCEPT_TAC
  >- (disch_tac >> map_every qx_gen_tac [`name`,`tv`,`v'`,`off'`] >>
      strip_tac >> suspend "owner_disjoint") >>
  fs[immutable_frame_mods_def, immutables_rel_mods_def] >> metis_tac[]
QED

Resume qualified_ctor_code_copy_read_mods[owner_disjoint]:
  `immutable_alloca_sep func (cenv with ce_module := src') cx ee z` by
    fs[immutable_alloca_sep_mods_def] >>
  `regions_disjoint off' (type_memory_size tv) (w2n dst) nb` by
    (qpat_assum `immutable_alloca_sep func (cenv with ce_module := src') cx ee z` mp_tac >>
     pure_rewrite_tac[immutable_alloca_sep_def, compile_env_accfupds, combinTheory.K_THM] >>
     disch_then (mp_tac o CONJUNCT2) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (qspecl_then [`name`,`tv`,`v'`,`off'`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     strip_tac >> qpat_assum `!i b k. MEM i (fn_insts _) /\ _ ==> _` irule >>
     qexists_tac `mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]` >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
       (pure_rewrite_tac[mk_inst_def,instruction_accessors,instruction_accfupds,combinTheory.K_THM] >>
        (REFL_TAC ORELSE (qpat_assum `z.vs_allocas = u.vs_allocas` SUBST1_TAC >>
                         first_assum ACCEPT_TAC))))) >>
  qpat_assum `!p k. _ ==> mem_bytes_at p k z.vs_memory = _` irule >>
  fs[regions_disjoint_def] >> decide_tac
QED

Resume qualified_ctor_code_copy_read_mods[ghost_frame]:
  (* Forget just the protected-prefix clauses, transport the local/return
     pointer part, and reattach the unchanged linked prefix. *)
  `ghost_inv_at (DF H) 0 d cenv cx ee G tn s` by
    (qpat_assum `ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s` mp_tac >>
     simp_tac bool_ss [ghost_inv_at_def, ghost_inv_at_mods_def, allocas_from_def,
                       prim_recTheory.NOT_LESS_0, arithmeticTheory.ZERO_LESS_EQ] >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `z.vs_accounts = s.vs_accounts /\ z.vs_transient = s.vs_transient /\
   z.vs_call_ctx = s.vs_call_ctx /\ z.vs_immutables = s.vs_immutables` by
    (qpat_assum `copy_static z = copy_static u`
       (mp_tac o Q.AP_TERM `\st. (st.vs_accounts,st.vs_transient,st.vs_call_ctx,st.vs_immutables)`) >>
     simp_tac bool_ss [copy_static_def,venom_state_accfupds,pairTheory.PAIR_EQ] >>
     strip_tac >> drule unwrap_alloc_runtime_frame >>
     simp_tac bool_ss [venom_state_accfupds] >> strip_tac >>
     rpt conj_tac >> metis_tac[]) >>
  `local_ptrs_rel func cenv ee.scopes s` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `stor_taint_ok_at (DF H) tf z` by
    (qpat_assum `ghost_inv_at (DF H) 0 _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[ghost_inv_at_def] >> strip_tac >>
     pure_rewrite_tac[stor_taint_ok_at_def] >>
     rewrite_tac[] >>
     qpat_assum `stor_taint_ok_at _ tn s` (mp_tac o REWRITE_RULE [stor_taint_ok_at_def]) >>
     asm_rewrite_tac[]) >>
  `allocas_from 0 z` by simp[allocas_from_def] >>
  `!name b len. local_region cenv ee.scopes s name b len ==>
      w2n dst+nb <= b \/ b+len <= w2n dst` by
    (ONCE_REWRITE_TAC[DISJ_COMM] >> first_assum ACCEPT_TAC) >>
  `0 <= w2n dst /\ 0 <= z.vs_alloca_next` by simp[] >>
  `ghost_inv_at (DF H) 0 d cenv cx ee HG tf z` by
    (drule_all unwrap_slot_copy_ghost_inv_at >> disch_then ACCEPT_TAC) >>
  `mem_bytes_at 0 lo z.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (qpat_assum `!p k. _ ==> mem_bytes_at p k z.vs_memory = _` irule >> decide_tac) >>
  `!i. i < lo /\ i IN tf.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >> `i < w2n dst` by decide_tac >> metis_tac[]) >>
  `!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==>
       FLOOKUP HG x = NONE /\ op_taint tf (Var x) = {}` by
    (rpt strip_tac >>
     `not_fresh_at sa x` by metis_tac[local_ptrs_reserved_imm_base] >>
     fs[ghost_inv_at_mods_def] >> metis_tac[]) >>
  `lo <= z.vs_alloca_next` by decide_tac >>
  qpat_assum `ghost_inv_at (DF H) 0 d cenv cx ee HG tf z` mp_tac >>
  simp_tac bool_ss [ghost_inv_at_def, ghost_inv_at_mods_def,
                    prim_recTheory.NOT_LESS_0, arithmeticTheory.ZERO_LESS_EQ] >>
  strip_tac >> rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
    (rpt strip_tac >>
     qpat_assum `ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
     qpat_assum `mem_bytes_at 0 lo z.vs_memory = _` SUBST1_TAC >>
     qpat_assum `!j. j < lo /\ j IN tn.t_mem ==> _` irule >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `!j. j < lo /\ j IN tf.t_mem ==> _` irule >>
     rpt conj_tac >> first_assum ACCEPT_TAC))
QED

Resume qualified_ctor_code_copy_read_mods[retention]:
  `!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
      FLOOKUP z.vs_allocas id = SOME entry` by
    (qpat_assum `z.vs_allocas = u.vs_allocas` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `!id b len. FLOOKUP s.vs_allocas id = SOME (b,len) /\ id < sa.cs_next_id ==>
      b+len <= w2n dst \/ w2n dst+nb <= b` by
    (rpt strip_tac >>
     qpat_assum `!id b len. _ ==> regions_disjoint (w2n dst) nb b len`
       (drule_all_then (mp_tac o REWRITE_RULE [regions_disjoint_def])) >> decide_tac) >>
  `wb_frame cenv ee ee sa s z` by
    (irule unwrap_slot_copy_wb_frame >> conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!x. not_fresh_at sa x ==> lookup_var x z = _ /\ _`
           (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`nb`, `w2n dst`] >> rpt conj_tac >>
     (first_assum ACCEPT_TAC ORELSE
      (rpt strip_tac >>
       qpat_assum `!id b len. FLOOKUP s.vs_allocas id = SOME (b,len) /\ id < _ ==> _`
         (drule_all_then ACCEPT_TAC)))) >>
  `pure_frame cenv func ee sa s z` by
    (drule_all bodyFullUnwrapCodePureFrameTheory.unwrap_alloc_copy_pure_frame >>
     disch_then ACCEPT_TAC) >>
  reverse conj_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  pure_rewrite_tac[ghost_kept_at_def] >> conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!x. not_fresh_at sa x ==> lookup_var x z = _ /\ _`
        (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  conj_tac >> rpt strip_tac >>
  `i < w2n dst \/ w2n dst+nb <= i` by
    (qpat_x_assum `ee.scopes = es.scopes` (SUBST_ALL_TAC o SYM) >>
     (qpat_assum `!id b len. FLOOKUP s.vs_allocas id = SOME (b,len) /\ _ ==> _` drule_all ORELSE
      qpat_assum `!name b len. local_region cenv ee.scopes s name b len ==> _` drule) >>
     decide_tac) >>
  qpat_assum `!j. _ ==> (j IN tf.t_mem <=> _)` (qspec_then `i` mp_tac) >>
  (impl_tac >- decide_tac) >>
  qpat_assum `i IN tf.t_mem` mp_tac >> simp_tac bool_ss []
QED

Resume qualified_ctor_code_copy_read_mods[post]:
  qpat_assum `op = Var root` SUBST1_TAC >>
  `eval_operand (Var root) z = SOME dst` by
    (rewrite_tac[eval_operand_def] >> first_assum ACCEPT_TAC) >>
  `FLOOKUP z.vs_allocas sa.cs_next_id = SOME (w2n dst,nb)` by
    (qpat_assum `z.vs_allocas = u.vs_allocas` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rewrite_tac[expr_post_mods_def, body_field_expr_post_inst_idx] >>
      conj_tac >- suspend "value_post" >> suspend "counted_immutable") >>
  simp_tac bool_ss [venom_state_accfupds, post_value_type_def, expr_type_def,
                    combinTheory.K_THM] >>
  rpt conj_tac
  >- (rewrite_tac[expr_store_bound_def,ghostPcTransportPtrTheory.eval_operand_inst_idx] >>
      rpt gen_tac >> strip_tac >>
      `tv = rt /\ w = dst` by metis_tac[optionTheory.SOME_11] >>
      qpat_assum `tv = rt` SUBST1_TAC >> qpat_assum `w = dst` SUBST1_TAC >>
      rewrite_tac[venom_state_accfupds] >> decide_tac)
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (rewrite_tac[exprPtrUnwrapFramesTheory.copy_allocas_inst_idx] >>
      qpat_assum `stmt_state_rel H ctx func cenv cx ee z`
        (mp_then Any ACCEPT_TAC stmt_state_rel_allocas_below_fmp))
  >- first_assum ACCEPT_TAC
  >- suspend "counted_ghost"
  >- first_assum ACCEPT_TAC
  >- (irule ptr_covers_buf_ok >> qexistsl_tac [`nb`,`tf`] >>
      rewrite_tac[lowered_value_type_def,expr_type_def,
                  ghostPcTransportPtrTheory.ptr_covers_inst_idx] >>
      conj_tac >- simp[] >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

Resume qualified_ctor_code_copy_read_mods[value_post]:
  `wb_frame cenv es ee sa s z` by
    (qpat_assum `wb_frame cenv ee ee sa s z` mp_tac >>
     qpat_assum `ee.scopes = es.scopes` (fn th =>
       simp_tac bool_ss [wb_frame_def,locals_kept_def,popped_kept_def,th]) >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `pure_frame cenv func es sa s z` by metis_tac[pure_frame_scopes] >>
  qpat_assum `wb_frame cenv es ee sa s z`
    (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
  irule copy_buffer_expr_post >>
  simp_tac bool_ss [post_value_type_def,expr_type_def] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
    (disch_tac >> first_assum ACCEPT_TAC) ORELSE
    (qexistsl_tac [`sa.cs_next_id`,`nb`,`rt`,`dst`] >>
     rewrite_tac[arithmeticTheory.LESS_EQ_REFL] >> rpt conj_tac >>
     (first_assum ACCEPT_TAC ORELSE
      (qpat_assum `!name b len. local_region cenv ee.scopes z name b len <=> _`
         (fn th => REWRITE_TAC [th]) >>
       ONCE_REWRITE_TAC[DISJ_COMM] >> first_assum ACCEPT_TAC))))
QED

Resume qualified_ctor_code_copy_read_mods[counted_immutable]:
  qpat_assum `immutable_frame_mods func cenv cx ee z` mp_tac >>
  simp_tac bool_ss [immutable_frame_mods_def,immutables_rel_mods_def,
    immutable_alloca_sep_mods_def,immutables_rel_def,immutable_alloca_sep_def,
    immutable_decl_sep_alt,local_region_def,lookup_var_def,
    venom_state_accfupds,combinTheory.K_THM]
QED

Resume qualified_ctor_code_copy_read_mods[counted_ghost]:
  qpat_assum `ghost_inv_at_mods (DF H) lo d cenv cx ee HG tf z` mp_tac >>
  Cases_on `d`
  >- (simp_tac bool_ss [ghost_inv_at_mods_def,return_buf_ptr_def,ptr_covers_def,
        stor_taint_ok_at_def,allocas_from_def,lookup_var_def,
        venom_state_accfupds,combinTheory.K_THM] >>
      strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rename1 `ghost_inv_at_mods _ _ (SOME rp) _ _ _ _ _ _` >> PairCases_on `rp` >>
  simp_tac bool_ss [ghost_inv_at_mods_def,return_buf_ptr_def,ptr_covers_def,
    stor_taint_ok_at_def,allocas_from_def,lookup_var_def,venom_state_accfupds,
    combinTheory.K_THM] >>
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise qualified_ctor_code_copy_read_mods
