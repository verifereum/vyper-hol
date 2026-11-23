(* Constructor code is read from the immutable memory range, then copied to
   the buffer allocated by unwrap_value itself. *)
Theory createCtorUnwrapCtorCodeArrival
Ancestors
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

Theorem ctor_unwrap_ctor_code_arrival:
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
     vv_post H ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
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
       expr_post H ctx func cenv cx e es sa sc s0 ee v op z /\
       ghost_inv_at (DF H) lo d cenv cx ee G' tn' z) /\
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
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[Abbr `H0`, storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  drule_all vv_post_code_source >> strip_tac >>
  `t = post_value_type cenv e` by first_assum ACCEPT_TAC >>
  rpt BasicProvers.VAR_EQ_TAC >>
  `lowered_value_type cenv e = expr_type e` by
    (drule compile_nonmemory_lowered_value_type >> simp[]) >>
  `lowered_value_type cenv e = post_value_type cenv e` by metis_tac[post_value_type_lowered] >>
  rename1 `eval_operand p.ptr_operand s = SOME src` >>
  `w2n src + type_memory_size rty <= lo /\
   (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rty v (w2n src) mem)` by
    (qpat_x_assum `?val. read_result _ _ _ = _ /\ _` strip_assume_tac >> gvs[] >>
     qpat_assum `!w. eval_operand p.ptr_operand s = SOME w ==> _`
       (qspec_then `src` mp_tac) >> simp[]) >>
  `stmt_state_rel H0 ctx func cenv cx ee s /\ wb_frame cenv es ee sa s0 s` by
    (qpat_assum `vv_post H0 _ _ _ _ _ _ _ _ _ _ _ _ s` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[vv_post_def, wb_frame_def] >> metis_tac[]) >>
  `local_ptrs_reserved cenv sb` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sb x` by metis_tac[not_fresh_at_mono] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
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
     fs[copy_old_operand_def, op_taint_def, op_prov_def, ghost_inv_at_def] >>
     metis_tac[local_ptrs_reserved_imm_base]) >>
  `w2n src + 32 * type_slot_size rty <= lo` by decide_tac >>
  drule_all ctor_code_copy_origin_execution >>
  disch_then (qspecl_then [`explicit`,`PG`,
     `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]
     strip_assume_tac) >>
  rename1 `copy_runtime_frame mid a sc z` >>
  rename1 `lookup_var root a = SOME dst` >>
  suspend "endpoint"
QED

Resume ctor_unwrap_ctor_code_arrival[endpoint]:
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by decide_tac >>
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
  qexistsl_tac [`v`, `z with vs_inst_idx := LENGTH sc.cs_current_insts`, `HG`, `tf`] >>
  asm_simp_tac (srw_ss()) [] >>
  conj_tac >- (drule_all immutable_copy_band >> simp[]) >>
  conj_tac >- suspend "horizon_post" >>
  conj_tac >- decide_tac >>
  conj_tac >- suspend "copied_value" >>
  conj_tac >-
    (rewrite_tac[ptr_buf_ok_inst_idx] >> irule ptr_covers_buf_ok >>
     qexistsl_tac [`type_memory_size rty`,`tf`] >> simp[]) >>
  conj_tac >-
    (simp[eval_operand_def, lookup_var_def] >> rpt strip_tac >>
     gvs[lookup_var_def] >> decide_tac) >>
  suspend "retention"
QED

Resume ctor_unwrap_ctor_code_arrival[horizon_post]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _` (drule_then strip_assume_tac) >>
  conj_tac >- (irule gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rewrite_tac[body_field_expr_post_inst_idx] >>
      `vv_post H ctx func cenv cx e es sa sb s0 ee (Value v)
         (LocatedValue (post_value_type cenv e) p) s` by
        (irule vv_post_read_result >> qexists_tac `tv` >> simp[] >>
         qpat_x_assum `vv_post H ctx func _ _ _ _ _ sm _ _ _ _ s` mp_tac >>
         qpat_assum `p.ptr_location = LocCode` (fn loc =>
           POP_ASSUM_LIST (K all_tac) >> simp[loc, vv_post_def, vv_at_def, vv_own_def]) >>
         metis_tac[]) >>
      `!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt ==>
            type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt` by simp[] >>
      drule_all ctor_code_copy_endpoint_post >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx ee s` by fs[vv_post_def] >>
  drule_all ctor_code_copy_ghost_inv_at >> simp[]
QED

Resume ctor_unwrap_ctor_code_arrival[copied_value]:
  `val_wf rty v /\ w2n src + type_memory_size rty < dimword(:256)` by
    metis_tac[immutable_holds_bounds] >>
  `regions_disjoint (w2n src) (type_memory_size rty) (w2n dst) (type_memory_size rty)` by
    (rewrite_tac[regions_disjoint_def] >> decide_tac) >>
  `z.vs_memory = (immutable_transfers F T src dst (type_slot_size rty) 0 a).vs_memory` by
    suspend "raw_memory" >>
  `MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w (type_memory_size rty))] [root])
      (fn_insts func)` by
    (drule unwrap_alloc_generated_code >> strip_tac >> drule_all buffer_alloc_code >> gvs[]) >>
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
   val_store_size rty v <= type_memory_size rty` by
    simp[val_footprint_le, val_store_size_le] >>
  `!mem. mem_agree_outside tm.t_mem a.vs_memory mem ==>
      val_in_memory rty v (w2n src) mem` by
    (gen_tac >> disch_tac >> irule robust_val_in_memory_shrinking_frame >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`tn.t_mem`,`tm.t_mem`,`s.vs_memory`,`a.vs_memory`,`type_memory_size rty`] >>
     simp[] >> rpt strip_tac >>
     `i < buffer_allocation_base s sb.cs_next_id` by (gvs[] >> decide_tac) >> metis_tac[]) >>
  drule_all ctor_code_copy_ptr_val_ok >> simp[]
QED

(* No immutable-region operand is needed for an empty copy. *)
Resume ctor_unwrap_ctor_code_arrival[raw_memory]:
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

Resume ctor_unwrap_ctor_code_arrival[retention]:
  drule_all ctor_code_copy_exterior_frames >> strip_tac >>
  `u = update_var root dst (buffer_allocation_fields s sb.cs_next_id (type_memory_size rty))` by simp[] >>
  drule_all ctor_code_copy_retained_frames_pure >> strip_tac >>
  fs[pure_frame_inst_idx] >>
  gen_tac >> disch_tac >>
  qpat_assum `!x. not_fresh_at sb x ==> lookup_var x z = lookup_var x s /\ _`
    (drule_then (assume_tac o CONJUNCT1)) >>
  fs[lookup_var_def]
QED

Finalise ctor_unwrap_ctor_code_arrival
