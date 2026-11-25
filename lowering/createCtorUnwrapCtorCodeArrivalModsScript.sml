(* Constructor code is read from the immutable memory range, then copied to
   the buffer allocated by unwrap_value itself. *)
Theory createCtorUnwrapCtorCodeArrivalMods
Ancestors
  createCtorUnwrapCtorCodeArrival createExprSizeExitDefsMods
  createCtorStraightBand createCtorImmutableCopyBand bodyFullUnwrapCodeCtorRun bodyFullUnwrapCodeCtorSemantic
  bodyFullUnwrapCodeCtorFrame exprSimAbiEncodeObliviousCode exprPtrUnwrapCode
  exprPtrUnwrapStorageShape exprSimVVFrame bodyPtrEnvBuiltinsBoundary
  bodyPtrIfExpAllocSource bodyPtrMakeArrayMemoryFrame stateRelProj
  exprPtrUnwrapAllocationFrame exprPtrUnwrapAllocEntry exprPtrUnwrapAllocSeparation
  fragGasOriginPtrDead bodyFieldMemoryProps context compileEnv loweringPosts
  ptrDiscipline bodyPtrDefs venomState venomInst vyperStorageFootprint
  exprSimProps localPtrsProps finite_map pred_set words arithmetic
  exprPtrUnwrapAllocation exprPtrUnwrapCodeCopySemantic loweringHalt exprSimCopy
  fragExec instIdxIndep list rich_list exprLowering exprLoweringProps
  loweringStateRelDefs immutableCopyExecution venomExecSemantics valueEncodingProps
  bodyFullHashKeccakFixed exprSimUnwrapProps bufferAllocationExecution
  exprPtrUnwrapCodeCopyShape allocationPtr freshWrites exprSimAlloc
  bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit reasonCodeResourcesPtr
  bodyFullUnwrapSlotPost exprPtrUnwrapAllocSemantic exprSimStorageCopy
  valueEncodingDefs immutableMemoryFrame exprPtrUnwrapRetained exprBopSimProps loweringSlice

Theorem ctor_unwrap_ctor_code_arrival_mods:
  cenv.ce_is_ctor /\ p.ptr_location = LocCode /\ ~is_word_type t /\
  compile_expr cenv ty e sa = (LocatedValue t p,sm) /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  unwrap_value cenv (LocatedValue t p) sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rty /\
  type_memory_size rty < 2**64 /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
     ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s) /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv e) tv (LocatedValue t p) ee G tn s /\
  (?val. read_result cx tv ee = (INL val,ee) /\
    !w. eval_operand p.ptr_operand s = SOME w ==>
        w2n w + type_memory_size rty <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
               val_in_memory rty val (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v z G' tn'.
    read_result cx tv ee = (INL v,ee) /\
    RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
         sb.cs_next_id <= i.inst_id /\ i.inst_id < sc.cs_next_id /\
         i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) s z /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,G',tn') /\
       expr_post_mods H ctx func cenv cx e es sa sc s0 ee v op z /\
       ghost_inv_at_mods (DF H) lo d cenv cx ee G' tn' z) /\
    ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv e) v op G' tn' z /\
    ptr_buf_ok cenv e op G' z /\
    (!rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand op z = SOME w ==>
            type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G' tn' /\
    (!x. not_fresh_at sb x ==>
       lookup_var x z = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
    pure_frame cenv func ee sb s z /\
    wb_frame cenv ee ee sb s z /\ ghost_kept_at lo cenv ee sb G tn s G' tn'
Proof
  strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[Abbr `H0`, storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  `t = post_value_type cenv e /\ ?src. eval_operand p.ptr_operand s = SOME src /\
     ?md. immutable_holds (cenv with ce_module := md) cx t tv src ee s` by
    (qpat_assum `vv_post_mods H0 ctx func cenv cx e es sa sm s0 ee tv (LocatedValue _ p) s` mp_tac >>
     qpat_assum `p.ptr_location = LocCode` (fn th =>
       POP_ASSUM_LIST (K all_tac) >>
       simp[th,vv_post_mods_def,vv_holds_mods_def,immutable_holds_mods_def]) >>
     metis_tac[]) >>
  `lowered_value_type cenv e = expr_type e` by
    (drule compile_nonmemory_lowered_value_type >> simp[]) >>
  `post_value_type cenv e = expr_type e` by metis_tac[post_value_type_lowered] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  rename1 `eval_operand p.ptr_operand s = SOME src` >>
  rename1 `read_result cx tv ee = (INL v,ee)` >>
  `w2n src + type_memory_size rty <= lo /\
   (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rty v (w2n src) mem)` by
    (qpat_assum `!w. eval_operand p.ptr_operand s = SOME w ==> _`
       (qspec_then `src` mp_tac) >> simp[]) >>
  `val_wf rty v /\ w2n src + type_memory_size rty < dimword(:256)` by
    (drule immutable_holds_read_result_value >>
     disch_then (fn th => qpat_assum `immutable_holds _ _ _ tv _ _ _`
       (assume_tac o PURE_REWRITE_RULE [th])) >>
     drule_all immutable_holds_bounds >> metis_tac[]) >>
  `stmt_state_rel H0 ctx func cenv cx ee s /\ wb_frame cenv es ee sa s0 s` by
    (qpat_assum `vv_post_mods H0 ctx func cenv cx e es sa sm s0 ee tv (LocatedValue _ p) s` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[vv_post_mods_def, wb_frame_def] >> metis_tac[]) >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by decide_tac >>
  `local_ptrs_reserved cenv sb` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sb x` by metis_tac[not_fresh_at_mono] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by metis_tac[stmt_state_rel_allocas_below_fmp] >>
  `op_taint tn p.ptr_operand = {} /\ op_prov G p.ptr_operand = NONE` by
    fs[ptr_vv_ok_def, vv_operand_def] >>
  `type_memory_size rty = 32 * type_slot_size rty` by simp[type_memory_size_slots] >>
  `(type_memory_size rty + 31) DIV 32 = type_slot_size rty` by
    simp[type_memory_size_slots, ADD_DIV_ADD_DIV] >>
  `type_memory_size rty < dimword(:256)` by (fs[dimword_def] >> decide_tac) >>
  `?buf mid. compile_alloc_buffer (type_memory_size rty) sb = (buf,mid) /\
     compile_imm_copy_to_memory T cenv.ce_imm_alloca p.ptr_operand buf.buf_operand
        (type_slot_size rty) 0 mid = ((),sc) /\ op = buf.buf_operand` by
    (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
     simp[unwrap_value_def, compile_ensure_in_memory_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[]) >>
  `ci_mono sb mid /\ ci_mono mid sc` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_compile_imm_copy_to_memory, pairTheory.SND] >>
  `fn_has_code sb mid func /\ fn_has_code mid sc func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  `type_slot_size rty <> 0 ==> !region. cenv.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sb region /\
    op_taint tn region = {} /\ op_prov G region = NONE` by
    (disch_tac >> gen_tac >> disch_tac >> `lo <> 0` by decide_tac >>
     drule_then assume_tac stmt_state_rel_immutable_base_zero >>
     conj_tac >- fs[immutable_base_zero_def] >>
     Cases_on `region` >>
     fs[copy_old_operand_def, op_taint_def, op_prov_def, ghost_inv_at_mods_def] >>
     metis_tac[local_ptrs_reserved_imm_base]) >>
  `w2n src + 32 * type_slot_size rty <= lo` by decide_tac >>
  drule_all ctor_code_copy_origin_execution >>
  disch_then (qspecl_then [`explicit`,`PG`,
     `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]
     strip_assume_tac) >>
  rename1 `copy_runtime_frame mid a sc z` >>
  rename1 `lookup_var root a = SOME dst` >>
  suspend "allocation_frames"
QED

Resume ctor_unwrap_ctor_code_arrival_mods[allocation_frames]:
  markerLib.RESUME_TAC >>
  `sb.cs_next_var <= mid.cs_next_var` by fs[ci_mono_def] >>
  `a.vs_memory = s.vs_memory /\ a.vs_accounts = s.vs_accounts /\
   a.vs_transient = s.vs_transient /\ a.vs_call_ctx = s.vs_call_ctx /\
   a.vs_immutables = s.vs_immutables` by
    (drule unwrap_alloc_runtime_frame >> simp[] >> metis_tac[]) >>
  `buffer_allocation_base s sb.cs_next_id < dimword(:256)` by
    (drule_all unwrap_alloc_site_bound >> decide_tac) >>
  `lo <= w2n dst` by
    (simp[] >> Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >>
     fs[buffer_allocation_base_def, allocas_from_def] >>
     PairCases_on `x` >> fs[] >> metis_tac[]) >>
  `lo <= z.vs_alloca_next` by decide_tac >>
  `tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm` by
    fs[step_taint_def, mk_inst_def, adopt_reset_def, store_taint_def, imm_taint_def] >>
  `32 * type_slot_size rty <= type_memory_size rty` by decide_tac >>
  `not_fresh_at mid root` by (drule_all allocated_copy_operands_old >> simp[]) >>
  `lookup_var root z = SOME dst` by
    (fs[copy_runtime_frame_def] >> metis_tac[]) >>
  `op = Var root` by metis_tac[] >>
  `MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w (type_memory_size rty))] [root])
      (fn_insts func)` by
    (drule unwrap_alloc_generated_code >> strip_tac >> drule_all buffer_alloc_code >> gvs[]) >>
  drule_all ctor_code_copy_exterior_frames >> strip_tac >>
  `u = update_var root dst (buffer_allocation_fields s sb.cs_next_id (type_memory_size rty))` by simp[] >>
  drule_all ctor_code_copy_retained_frames_pure >> strip_tac >>
  qabbrev_tac `q = z with vs_inst_idx := LENGTH sc.cs_current_insts` >>
  `eval_operand op q = SOME dst` by fs[Abbr `q`,eval_operand_def,lookup_var_def] >>
  `!x. not_fresh_at sb x ==> lookup_var x q = lookup_var x s /\ FLOOKUP HG x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x)` by
    (qpat_assum `!x. not_fresh_at sb x ==> lookup_var x z = _ /\ _` mp_tac >>
     UNABBREV_ALL_TAC >> POP_ASSUM_LIST (K ALL_TAC) >> simp[lookup_var_def]) >>
  `!off len. off+len <= w2n dst \/ w2n dst+type_memory_size rty <= off ==>
     mem_bytes_at off len q.vs_memory = mem_bytes_at off len s.vs_memory` by
    (simp[Abbr `q`] >> rpt strip_tac >>
     qpat_assum `!off len. _ ==> mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory`
       irule >> fs[] >> decide_tac) >>
  suspend "copied_value"
QED

Resume ctor_unwrap_ctor_code_arrival_mods[copied_value]:
  markerLib.RESUME_TAC >>
  `regions_disjoint (w2n src) (type_memory_size rty) (w2n dst) (type_memory_size rty)` by
    (rewrite_tac[regions_disjoint_def] >> decide_tac) >>
  `z.vs_memory = (immutable_transfers F T src dst (type_slot_size rty) 0 a).vs_memory` by
    suspend "raw_memory" >>
  `!i. i < buffer_allocation_base s sb.cs_next_id \/
       buffer_allocation_base s sb.cs_next_id + type_memory_size rty <= i ==>
       (i IN tm.t_mem <=> i IN tn.t_mem)` by
    (drule_all unwrap_alloc_taint_frame >> simp[] >> metis_tac[]) >>
  `!i. i < type_memory_size rty ==>
     (w2n dst+i IN tf.t_mem <=> w2n src+i IN tm.t_mem)` by
    (rpt strip_tac >>
     qpat_assum `!j. j IN tf.t_mem <=> _` (qspec_then `w2n dst+i` SUBST1_TAC) >>
     `w2n dst <= w2n dst+i /\ w2n dst+i < w2n dst+32*type_slot_size rty /\
      w2n dst+i-w2n dst = i` by decide_tac >> simp[]) >>
  `val_footprint rty v <= type_memory_size rty /\
   val_store_size rty v <= type_memory_size rty` by simp[val_footprint_le, val_store_size_le] >>
  `!mem. mem_agree_outside tm.t_mem a.vs_memory mem ==>
      val_in_memory rty v (w2n src) mem` by
    (gen_tac >> disch_tac >> irule robust_val_in_memory_shrinking_frame >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`tn.t_mem`,`tm.t_mem`,`s.vs_memory`,`a.vs_memory`,`type_memory_size rty`] >>
     simp[] >> rpt strip_tac >>
     `i < buffer_allocation_base s sb.cs_next_id` by (gvs[] >> decide_tac) >> metis_tac[]) >>
  `ptr_val_ok cx (post_value_type cenv e) v (Var root) HG tf q` by
    (qpat_assum `Abbrev(q = _)`
       (fn th => pure_rewrite_tac[REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
     irule ctor_code_copy_ptr_val_ok >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`a`,`dst`,`type_memory_size rty`,`src`,`tm`,`rty`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "finish"
QED

Resume ctor_unwrap_ctor_code_arrival_mods[raw_memory]:
  markerLib.RESUME_TAC >>
  Cases_on `type_slot_size rty = 0`
  >- gvs[compile_imm_copy_to_memory_def, comp_return_def,
         copy_runtime_frame_def, immutable_transfers_def, run_inst_seq_def] >>
  `!q. (!x. q = Var x ==> x <> root) ==>
        eval_operand q a = eval_operand q s` by
    (gen_tac >> strip_tac >> qpat_assum `a = _` SUBST1_TAC >>
     irule unwrap_alloc_operand_frame >> metis_tac[]) >>
  `!region. cenv.ce_imm_alloca = SOME region ==>
    eval_operand region a = SOME 0w /\ copy_old_operand mid region` by
    (gen_tac >> disch_tac >>
     `eval_operand region s = SOME 0w /\ copy_old_operand sb region` by metis_tac[] >>
     `!x. region = Var x ==> x <> root` by
       (fs[copy_old_operand_def] >> metis_tac[unwrap_alloc_old_operand_distinct]) >>
     conj_tac >- metis_tac[] >>
     metis_tac[copy_old_operand_mono, ci_mono_def]) >>
  `copy_old_operand mid p.ptr_operand` by metis_tac[allocated_copy_operands_old] >>
  `!x. p.ptr_operand = Var x ==> x <> root` by metis_tac[unwrap_alloc_old_operand_distinct] >>
  `eval_operand p.ptr_operand a = SOME src` by metis_tac[] >>
  `eval_operand buf.buf_operand a = SOME dst /\ copy_old_operand mid buf.buf_operand` by
    gvs[eval_operand_def, copy_old_operand_def, operand_11, lookup_var_def] >>
  drule_all copy_ctor_run >> strip_tac >> fs[copy_runtime_frame_def] >> metis_tac[]
QED

Resume ctor_unwrap_ctor_code_arrival_mods[finish]:
  markerLib.RESUME_TAC >>
  `~q.vs_halted /\ q.vs_current_bb = sc.cs_current_bb /\
   q.vs_inst_idx = LENGTH sc.cs_current_insts /\ q.vs_alloca_next = z.vs_alloca_next` by
    simp[Abbr `q`] >>
  `s0.vs_alloca_next <= q.vs_alloca_next /\ s.vs_alloca_next <= q.vs_alloca_next` by decide_tac >>
  `ptr_buf_ok cenv e op HG q` by
    (simp[Abbr `q`,ptr_buf_ok_inst_idx] >> irule ptr_covers_buf_ok >>
     qexistsl_tac [`type_memory_size rty`,`tf`] >> fs[]) >>
  `!rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
      eval_operand op q = SOME w ==>
      type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= q.vs_alloca_next` by
    (rpt gen_tac >> strip_tac >>
     `rt = rty` by
       (qpat_assum `lowered_value_type cenv e = _` (fn th =>
          qpat_assum `evaluate_type _ (lowered_value_type cenv e) = SOME rt`
            (mp_tac o PURE_REWRITE_RULE [th])) >>
        qpat_assum `post_value_type cenv e = _` (fn th =>
          qpat_assum `evaluate_type _ (post_value_type cenv e) = SOME rty`
            (mp_tac o PURE_REWRITE_RULE [th])) >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
     `w = dst` by metis_tac[optionTheory.SOME_11] >>
     disj2_tac >> qpat_assum `rt = rty` SUBST1_TAC >>
     qpat_assum `w = dst` SUBST1_TAC >> decide_tac) >>
  qexistsl_tac [`v`,`q`,`HG`,`tf`] >>
  asm_simp_tac (srw_ss()) [] >>
  conj_tac >- (drule_all immutable_copy_band >> simp[Abbr `q`]) >>
  suspend "linked_posts"
QED

Resume ctor_unwrap_ctor_code_arrival_mods[linked_posts]:
  markerLib.RESUME_TAC >>
  reverse conj_tac >-
    (qpat_assum `post_value_type cenv e = _` (fn th =>
       qpat_assum `ptr_val_ok cx (post_value_type cenv e) _ _ _ _ q`
         (ACCEPT_TAC o PURE_REWRITE_RULE [th]))) >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _` (drule_then strip_assume_tac) >>
  conj_tac >- (irule gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel H ctx func cenv cx ee s` by fs[vv_post_mods_def] >>
  drule_all unwrap_alloc_semantic_frames >> strip_tac >>
  `local_ptrs_reserved cenv mid` by metis_tac[local_ptrs_reserved_next_var] >>
  `!name b sz. local_region cenv ee.scopes q name b sz <=>
    local_region cenv ee.scopes s name b sz` by
    (irule copy_buffer_local_region_frame >> qexists_tac `sb` >> metis_tac[]) >>
  `!name b len. local_region cenv ee.scopes s name b len ==>
      w2n dst + type_memory_size rty <= b \/ b+len <= w2n dst` by
    (rpt strip_tac >> drule_all unwrap_alloc_local_separation >> simp[]) >>
  `copy_static z = copy_static a /\
    (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x a)` by fs[copy_runtime_frame_def] >>
  `q.vs_memory = z.vs_memory /\ q.vs_allocas = u.vs_allocas /\
    q.vs_alloca_next = a.vs_alloca_next /\ q.vs_alloca_next = z.vs_alloca_next` by
    (drule copy_static_fields >> simp[Abbr `q`] >>
     qpat_assum `a = u with vs_inst_idx := _` (fn th => simp_tac (srw_ss()) [th])) >>
  conj_tac >- suspend "linked_expr_post" >>
  suspend "linked_ghost"
QED

Resume ctor_unwrap_ctor_code_arrival_mods[linked_expr_post]:
  markerLib.RESUME_TAC >>
  `stmt_state_rel H ctx func cenv cx ee a` by
    (qpat_assum `a = u with vs_inst_idx := _`
       (fn th => pure_rewrite_tac[th,stmt_state_rel_inst_idx]) >> first_assum ACCEPT_TAC) >>
  `FLOOKUP a.vs_allocas sb.cs_next_id = SOME (w2n dst,type_memory_size rty)` by
    (qpat_assum `FLOOKUP u.vs_allocas sb.cs_next_id = SOME _` mp_tac >>
     qpat_assum `a = u with vs_inst_idx := _` (fn th => simp_tac (srw_ss()) [th])) >>
  `!name b len. local_region cenv ee.scopes a name b len ==>
     w2n dst + type_memory_size rty <= b \/ b+len <= w2n dst` by
    (qpat_assum `!name b len. local_region cenv ee.scopes u name b len ==> _` mp_tac >>
     qpat_assum `a = u with vs_inst_idx := _`
       (fn th => simp_tac (srw_ss()) [th,local_region_def,lookup_var_def,regions_disjoint_def])) >>
  `LENGTH a.vs_memory <= LENGTH z.vs_memory` by
    (Cases_on `type_slot_size rty = 0` >- simp[immutable_transfers_def] >>
     drule_all copy_ctor_memory_snapshot >> simp[immutable_write_memory_capacity]) >>
  `stmt_state_rel H ctx func cenv cx ee q` by
    (qpat_assum `Abbrev(q = _)`
       (fn th => pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th,stmt_state_rel_inst_idx]) >>
     irule copy_buffer_state_rel_frame >>
     qexistsl [`w2n dst`,`mk_inst sb.cs_next_id ALLOCA [Lit (n2w (type_memory_size rty))] [root]`,
        `a`,`mid`,`type_memory_size rty`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     simp_tac (srw_ss()) [mk_inst_def] >>
     TRY (first_assum ACCEPT_TAC) >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!off len. _ ==> mem_bytes_at off len z.vs_memory = mem_bytes_at off len a.vs_memory`
       irule >> decide_tac) >>
  `val_in_memory rty v (w2n dst) q.vs_memory` by
    (`eval_operand (Var root) q = SOME dst` by metis_tac[] >>
     qpat_assum `ptr_val_ok cx _ _ _ _ _ q` mp_tac >>
     simp_tac (srw_ss()) [ptr_val_ok_def,ptr_mem_ok_def] >> strip_tac >>
     qpat_assum `!tv w. evaluate_type _ _ = SOME tv /\ eval_operand _ q = SOME w ==> _`
       (qspecl_then [`rty`,`dst`] mp_tac) >> simp[mem_agree_outside_def]) >>
  `sb.cs_next_id < sc.cs_next_id` by
    (drule compile_alloc_buffer_parts >> strip_tac >> fs[ci_mono_def] >> decide_tac) >>
  `wb_frame cenv es ee sa s0 q` by suspend "compose_wb" >>
  `(~expr_has_effect e ==> pure_frame cenv func es sa s0 q)` by
    (strip_tac >> irule pure_frame_trans >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`ee`,`sb`,`s`] >>
     qpat_assum `vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv (LocatedValue _ p) s`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     qpat_assum `wb_frame cenv ee ee sb s q`
       (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE (first_x_assum irule >> first_assum ACCEPT_TAC))) >>
  rewrite_tac[expr_post_mods_def] >>
  conj_tac >- suspend "plain_post" >>
  suspend "linked_immutable"
QED

Resume ctor_unwrap_ctor_code_arrival_mods[compose_wb]:
  markerLib.RESUME_TAC >>
  qpat_assum `wb_frame cenv es ee sa s0 s` (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
  qpat_assum `wb_frame cenv ee ee sb s q` (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
  rewrite_tac[wb_frame_def] >> conj_tac
  >- (rpt strip_tac >> metis_tac[not_fresh_at_mono]) >>
  conj_tac >- metis_tac[] >>
  reverse conj_tac
  >- (irule locals_kept_trans >> qexistsl [`ee`, `sa`, `s`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  `FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sb.cs_next_id` by
    (conj_tac >- metis_tac[] >> decide_tac) >>
  `regions_disjoint (w2n dst) (type_memory_size rty) off sz` by metis_tac[] >>
  fs[regions_disjoint_def] >> metis_tac[]
QED

Resume ctor_unwrap_ctor_code_arrival_mods[plain_post]:
  markerLib.RESUME_TAC >>
  qpat_assum `wb_frame cenv es ee sa s0 q`
    (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
  qpat_assum `vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv (LocatedValue _ p) s`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  qpat_assum `post_value_type cenv e = _` (fn th =>
    qpat_assum `~is_word_type (post_value_type cenv e)`
      (assume_tac o PURE_REWRITE_RULE [th]) >>
    qpat_assum `evaluate_type _ (post_value_type cenv e) = SOME rty`
      (assume_tac o PURE_REWRITE_RULE [th])) >>
  irule copy_buffer_expr_post >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl [`sb.cs_next_id`,`type_memory_size rty`,`rty`,`dst`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  (first_assum (fn th => pure_rewrite_tac[th] >> first_assum ACCEPT_TAC) ORELSE
   metis_tac[])
QED

Resume ctor_unwrap_ctor_code_arrival_mods[linked_ghost]:
  markerLib.RESUME_TAC >>
  `z.vs_accounts = s.vs_accounts /\ z.vs_transient = s.vs_transient /\
   z.vs_call_ctx = s.vs_call_ctx /\ z.vs_immutables = s.vs_immutables` by
    (qpat_assum `copy_static z = copy_static a` mp_tac >>
     simp_tac (srw_ss()) [copy_static_def,venom_state_component_equality] >>
     strip_tac >> metis_tac[]) >>
  `local_ptrs_rel func cenv ee.scopes s` by fs[stmt_state_rel_def,state_rel_def] >>
  `stor_taint_ok_at (DF H) tf q` by
    fs[Abbr `q`,ghost_inv_at_mods_def,stor_taint_ok_at_def] >>
  `ghost_inv_at (DF H) 0 d cenv cx ee G tn s` by
    (fs[ghost_inv_at_mods_def,ghost_inv_at_def,allocas_from_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at (DF H) 0 d cenv cx ee HG tf q` by
    (`allocas_from 0 q /\ 0 <= q.vs_alloca_next /\ 0 <= w2n dst` by simp[allocas_from_def] >>
     irule unwrap_slot_copy_ghost_inv_at >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl [`G`,`func`,`type_memory_size rty`,`s`,`sb`,`w2n dst`,`tn`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (rpt strip_tac >> qpat_assum `!x sz. cenv.ce_return_buf = _ ==> _` drule >>
         strip_tac >> drule_all not_fresh_at_mono >> simp[])
     >- (rpt strip_tac >> qpat_assum `!x sz. cenv.ce_return_pc = _ ==> _` drule >>
         strip_tac >> drule_all not_fresh_at_mono >> simp[])) >>
  `mem_bytes_at 0 lo q.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (qpat_assum `!off len. _ ==> mem_bytes_at off len q.vs_memory = mem_bytes_at off len s.vs_memory`
       irule >> simp_tac (srw_ss()) [] >> disj1_tac >> first_assum ACCEPT_TAC) >>
  `allocas_from lo q` by
    (qpat_assum `Abbrev(q = _)`
       (fn th => pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
     qpat_assum `allocas_from lo z` mp_tac >> simp_tac (srw_ss()) [allocas_from_def]) >>
  `lo <= q.vs_alloca_next` by decide_tac >>
  qpat_assum `ghost_inv_at (DF H) 0 d cenv cx ee HG tf q`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
  qpat_assum `ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
  rewrite_tac[ghost_inv_at_mods_def] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> conj_tac
  >- (rpt strip_tac >> `i < w2n dst` by decide_tac >> metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sb x` by (irule local_ptrs_reserved_imm_base >> goal_assum drule >> simp[]) >>
      qpat_assum `!x. not_fresh_at sb x ==> lookup_var x q = _ /\ _` drule >>
      qpat_assum `!x. lo <> 0 /\ cenv.ce_imm_alloca = _ ==> _` drule_all >>
      metis_tac[]) >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Resume ctor_unwrap_ctor_code_arrival_mods[linked_immutable]:
  markerLib.RESUME_TAC >>
  `!id b sz. FLOOKUP q.vs_allocas id = SOME (b,sz) ==>
      FLOOKUP s.vs_allocas id = SOME (b,sz) \/ s.vs_alloca_next <= b` by
    (qpat_assum `u = update_var root dst _` (fn th => simp_tac (srw_ss()) [th]) >>
     qpat_assum `q.vs_allocas = u.vs_allocas` (fn th => rewrite_tac[th]) >>
     qpat_assum `u = update_var root dst _` SUBST1_TAC >>
     Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >>
     simp[buffer_allocation_fields_def,update_var_def,FLOOKUP_UPDATE,AllCaseEqs()] >>
     rpt gen_tac >> strip_tac >> simp[]) >>
  `immutable_frame_mods func cenv cx ee s` by fs[vv_post_mods_def] >>
  qpat_x_assum `immutable_frame_mods func cenv cx ee s`
    (strip_assume_tac o REWRITE_RULE [immutable_frame_mods_def]) >>
  rewrite_tac[immutable_frame_mods_def] >> reverse conj_tac
  >- (rw[immutable_alloca_sep_mods_def] >>
      irule immutable_alloca_sep_frame >> qexistsl [`s`,`ee`] >>
      qpat_assum `immutable_alloca_sep_mods func cenv cx ee s` (assume_tac o REWRITE_RULE [immutable_alloca_sep_mods_def]) >>
      simp[] >> rpt gen_tac >> disch_tac >> disj1_tac >> qexists_tac `id` >>
      pop_assum mp_tac >>
      qpat_assum `!name b sz. local_region cenv ee.scopes q name b sz <=> _`
        (qspecl_then [`id`,`b`,`sz`] mp_tac) >>
      simp_tac (srw_ss()) [local_region_def]) >>
  suspend "linked_bytes"
QED

Resume ctor_unwrap_ctor_code_arrival_mods[linked_bytes]:
  markerLib.RESUME_TAC >>
  rw[immutables_rel_mods_def] >>
  qpat_assum `immutables_rel_mods cenv _ _ ee s`
    (assume_tac o REWRITE_RULE [immutables_rel_mods_def]) >>
  qpat_assum `immutable_alloca_sep_mods func cenv cx ee s`
    (assume_tac o REWRITE_RULE [immutable_alloca_sep_mods_def]) >>
  qpat_assum `cenv.ce_is_ctor` (fn ctor =>
    qpat_assum `!src tops. ALOOKUP cenv.ce_modules src = SOME tops ==> immutables_rel _ _ _ _ _ _`
      (drule_then (assume_tac o SIMP_RULE (srw_ss()) [immutables_rel_def,LET_THM,ctor])) >>
    simp_tac (srw_ss()) [immutables_rel_def,LET_THM,ctor]) >>
  qpat_assum `!src tops. ALOOKUP cenv.ce_modules src = SOME tops ==> immutable_alloca_sep _ _ _ _ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [immutable_alloca_sep_def])) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!name tv v off. _ /\ _ ==> immutable_value_admissible _ _ /\ _`
    (drule_all_then strip_assume_tac) >>
  rename1 `val_in_memory vt value off s.vs_memory` >>
  `mem_bytes_at off (type_memory_size vt) q.vs_memory =
   mem_bytes_at off (type_memory_size vt) s.vs_memory` by
    (qpat_assum `!off len. _ \/ _ ==> mem_bytes_at off len q.vs_memory = _`
      irule >> suspend "immutable_separation") >>
  conj_tac >- first_assum ACCEPT_TAC >> reverse conj_tac
  >- (qpat_assum `mem_bytes_at off (type_memory_size vt) q.vs_memory = _`
        (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  irule valueEncodingPropsTheory.val_in_memory_mem_agree >>
  conj_tac >- (irule (cj 1 immutable_admissible_val_wf) >> first_assum ACCEPT_TAC) >>
  qexistsl [`type_memory_size vt`,`s.vs_memory`] >>
  simp_tac (srw_ss()) [] >> conj_tac
  >- (sym_tac >> first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC
QED

Resume ctor_unwrap_ctor_code_arrival_mods[immutable_separation]:
  markerLib.RESUME_TAC >>
  `off + type_memory_size vt <= s.vs_alloca_next /\
   (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
      regions_disjoint off (type_memory_size vt) b sz)` by
    (qpat_assum `cenv.ce_is_ctor` (fn ctor =>
       qpat_assum `(cenv with ce_module := _).ce_is_ctor ==> _`
         (assume_tac o SIMP_RULE (srw_ss()) [ctor])) >>
     qpat_x_assum `!name tv v off. _ /\ _ ==> off + type_memory_size tv <= _ /\ _`
       (drule_all_then strip_assume_tac) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  rewrite_tac[w2n_n2w] >>
  `buffer_allocation_base s sb.cs_next_id MOD dimword(:256) =
   buffer_allocation_base s sb.cs_next_id` by simp[LESS_MOD] >>
  pop_assum SUBST1_TAC >>
  Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id`
  >- fs[buffer_allocation_base_def] >>
  rename1 `FLOOKUP s.vs_allocas sb.cs_next_id = SOME row` >> PairCases_on `row` >>
  `row1 = type_memory_size rty` by
    (qpat_assum `FLOOKUP (update_var root _ (buffer_allocation_fields s sb.cs_next_id _)).vs_allocas sb.cs_next_id = SOME _`
       mp_tac >>
     qpat_assum `FLOOKUP s.vs_allocas sb.cs_next_id = SOME (row0,row1)`
       (fn th => simp_tac (srw_ss()) [update_var_def,buffer_allocation_fields_def,th])) >>
  `regions_disjoint off (type_memory_size vt) row0 row1` by
    (qpat_assum `!inst b sz. _ ==> regions_disjoint off (type_memory_size vt) b sz` irule >>
     qexists_tac `mk_inst sb.cs_next_id ALLOCA [Lit (n2w (type_memory_size rty))] [root]` >>
     simp[mk_inst_def]) >>
  qpat_x_assum `regions_disjoint off (type_memory_size vt) row0 row1` mp_tac >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def,buffer_allocation_base_def]
QED

Finalise ctor_unwrap_ctor_code_arrival_mods
