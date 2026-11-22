(* A runtime immutable copy reaches the semantic endpoint along its own instructions. *)
Theory createCtorUnwrapRuntimeCodeArrival
Ancestors
  createCtorStraightBand exprSimAbiEncodeObliviousCode exprSimAbiGasBridge
  bodyFullUnwrapCodeRuntimeRun bodyFullUnwrapCodeRuntimeFrame
  exprPtrUnwrapCodeCopyShape exprPtrUnwrapCodeCopySemantic exprPtrUnwrapCode
  exprPtrUnwrapAllocation exprPtrUnwrapAllocSeparation exprPtrUnwrapAllocationFrame
  exprPtrCleanBufferPost exprSimCopy exprSimStorageCopy exprSimAlloc
  exprSimUnwrapProps
  fragGasOriginPtrDead bodyFieldMemoryProps loweringPosts loweringStateRelDefs
  bodyPtrDefs freshWrites context compileEnv exprLowering exprLoweringProps
  venomState venomInst venomExecSemantics instIdxIndep fragExec abiBufferAllocationCode bufferAllocationExecution
  ptrDiscipline finite_map relation words arithmetic list rich_list
  vyperStorageFootprint bodyFullHashKeccakFixed valueEncodingProps bodyImmutableUnwrapMemory
  exprPtrUnwrapStorageShape exprSimMemDefs allocaHistory

Theorem runtime_copy_offset_action[local]:
  !P src off. P ADD ==> code_action P (compile_lit_byte_offset src off)
Proof
  rpt strip_tac >> Cases_on `off = 0` >> Cases_on `src` >>
  simp[compile_lit_byte_offset_def, code_action_return, code_action_emit_op]
QED

Theorem runtime_copy_action[local]:
  !n P imm src dst off. P ADD /\ P DLOAD /\ P MSTORE ==>
    code_action P (compile_imm_copy_to_memory F imm src dst n off)
Proof
  Induct >> simp[compile_imm_copy_to_memory_def, code_action_return] >>
  rpt strip_tac >> rewrite_tac[compile_imm_copy_to_memory_def,
    compile_imm_load_word_runtime] >>
  rpt (CHANGED_TAC BETA_TAC ORELSE irule code_action_bind ORELSE
       irule code_action_ignore_bind ORELSE conj_tac ORELSE gen_tac) >>
  simp[runtime_copy_offset_action, code_action_emit_op, code_action_emit_void]
QED

Theorem runtime_copy_band[local]:
  compile_alloc_buffer nb sb = (buf,mid) /\ buf.buf_operand = Var root /\
  compile_imm_copy_to_memory F imm src buf.buf_operand n 0 mid = ((),sc) /\
  fn_has_code sb sc func /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := k /\ copy_runtime_frame mid a sc z ==>
  RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
                 sb.cs_next_id <= i.inst_id /\ i.inst_id < sc.cs_next_id /\
                 i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v)
    s (z with vs_inst_idx := LENGTH sc.cs_current_insts)
Proof
  strip_tac >>
  `code_step (\opc. opc <> INVOKE /\ ~is_terminator opc) sb sc` by
    (irule code_step_trans >> qexists_tac `mid` >> conj_tac
     >- (mp_tac (Q.SPECL [`\opc. opc <> INVOKE /\ ~is_terminator opc`, `nb`]
          code_action_alloc_buffer) >> simp[code_action_def,is_terminator_def] >> metis_tac[])
     >> mp_tac (Q.SPECL [`n`, `\opc. opc <> INVOKE /\ ~is_terminator opc`, `imm`, `src`,
                         `buf.buf_operand`, `0`] runtime_copy_action) >>
     simp[code_action_def,is_terminator_def] >> metis_tac[]) >>
  drule compile_alloc_buffer_code >> strip_tac >>
  drule_all unwrap_code_copy_shifted_run >> strip_tac >>
  `sc.cs_blocks = sb.cs_blocks /\ sc.cs_current_bb = sb.cs_current_bb /\
   ?is. sc.cs_current_insts = sb.cs_current_insts ++ is` by
    (qpat_assum `copy_runtime_frame _ _ _ _`
       (strip_assume_tac o REWRITE_RULE[copy_runtime_frame_def,same_blocks_def]) >>
     qpat_assum `same_blocks sb mid` (strip_assume_tac o REWRITE_RULE[same_blocks_def]) >>
     simp[] >> qexists_tac `emitted_insts sb mid ++ emitted_insts mid sc` >>
     metis_tac[APPEND_ASSOC]) >>
  `frag_code sb sc = emitted_insts sb sc` by
    simp[frag_code_def,emitted_blocks_def] >>
  `emitted_insts sb sc = is` by simp[emitted_insts_def,DROP_APPEND] >>
  fs[code_step_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) is` by fs[EVERY_MEM] >>
  `?t. run_inst_seq is s = OK t /\ z = t with vs_inst_idx := k` by
    (drule run_inst_seq_inst_idx >> disch_then (qspecl_then [`s`,`k`] mp_tac) >>
     Cases_on `run_inst_seq is s` >> fs[exec_result_map_def]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX is (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def,IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC,DROP_LENGTH_APPEND] >> simp[]) >>
  `RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
                  sb.cs_next_id <= i.inst_id /\ i.inst_id < sc.cs_next_id /\
                  i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v)
       s (t with vs_inst_idx := s.vs_inst_idx + LENGTH is)` by
    (irule ctor_straight_band_run >> metis_tac[]) >>
  gvs[ADD_COMM]
QED

Theorem ctor_unwrap_runtime_code_arrival:
  ~cenv.ce_is_ctor /\
  vv = LocatedValue t p /\ p.ptr_location = LocCode /\ ~is_word_type t /\
  compile_expr cenv ty e sa = (vv,sm) /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  unwrap_value cenv vv sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rty /\
  type_memory_size rty < 2**64 /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v z G' tn'.
    read_result cx tv ee = (INL v, ee) /\
    RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
                    sb.cs_next_id <= i.inst_id /\ i.inst_id < sc.cs_next_id /\
                    i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) s z /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (s, G, tn) [] (OK z, G', tn') /\
       expr_post H ctx func cenv cx e es sa sc s0 ee v op z /\
       ghost_inv_at (DF H) lo d cenv cx ee G' tn' z) /\
    expr_store_bound cx (post_value_type cenv e) v op z /\
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
    wb_frame cenv ee ee sb s z /\ ghost_kept_at lo cenv ee sb G tn s G' tn'
Proof
  strip_tac >> gvs[] >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  drule_all vv_post_code_source >> strip_tac >> gvs[] >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by decide_tac >>
  `local_ptrs_reserved cenv sb` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sb x` by
    (fs[vv_operand_def] >> metis_tac[not_fresh_at_mono]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e es sa sb s0 ee tv
       (LocatedValue (post_value_type cenv e) p) s` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
       (drule_then strip_assume_tac) >>
     gvs[vv_post_def,vv_at_def,vv_own_def] >> metis_tac[]) >>
  `stmt_state_rel H0 ctx func cenv cx ee s` by fs[vv_post_def] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
       (qspec_then `H0` (drule_then strip_assume_tac)) >> fs[ghost_inv_at_def]) >>
  `op_taint tn p.ptr_operand = {}` by fs[ptr_vv_ok_def,vv_operand_def] >>
  `compile_ensure_in_memory p.ptr_operand LocCode
    (type_memory_bytes cenv (post_value_type cenv e))
    ((type_memory_bytes cenv (post_value_type cenv e) + 31) DIV 32)
    F cenv.ce_imm_alloca sb = (op,sc)` by gvs[unwrap_value_def] >>
  drule_all ensure_runtime_code_layout >> strip_tac >>
  `(type_memory_size rty + 31) DIV 32 = type_slot_size rty` by
    simp[type_memory_size_slots,ADD_DIV_ADD_DIV] >>
  `compile_alloc_buffer (type_memory_size rty) sb = (buf,mid) /\
   compile_imm_copy_to_memory F cenv.ce_imm_alloca p.ptr_operand buf.buf_operand
     (type_slot_size rty) 0 mid = ((),sc)` by metis_tac[] >>
  `type_memory_size rty = 32 * type_slot_size rty` by simp[type_memory_size_slots] >>
  `w2n a + 32 * type_slot_size rty <= LENGTH s.vs_data_section /\
   w2n a + 32 * type_slot_size rty < dimword(:256)` by
    (drule_all runtime_immutable_data_section >> disch_tac >>
     drule_all immutable_holds_bounds >> simp[]) >>
  `type_memory_size rty < dimword(:256)` by decide_tac >>
  drule_all runtime_code_copy_origin_execution >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`,
    `<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>`]
    strip_assume_tac) >>
  rename1 `copy_runtime_frame mid allocst sc z` >>
  rename1 `lookup_var root allocst = SOME dst` >>
  suspend "runtime_posts"
QED

Resume ctor_unwrap_runtime_code_arrival[runtime_posts]:
  markerLib.RESUME_TAC >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post H ctx func cenv cx e es sa sc s0 ee v (Var root) z` by
    (rpt strip_tac >>
     `vv_post H ctx func cenv cx e es sa sb s0 ee (Value v)
       (LocatedValue (post_value_type cenv e) p) s` by
       (irule vv_post_read_result >> qexists_tac `tv` >> simp[]) >>
     `!ty. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ty ==>
       type_memory_bytes cenv (post_value_type cenv e) = type_memory_size ty` by simp[] >>
     drule_all unwrap_code_copy_endpoint_post >> simp[]) >>
  `allocst.vs_memory = s.vs_memory /\ allocst.vs_accounts = s.vs_accounts /\
   allocst.vs_transient = s.vs_transient /\ allocst.vs_call_ctx = s.vs_call_ctx /\
   allocst.vs_immutables = s.vs_immutables` by
    (drule unwrap_alloc_runtime_frame >> simp[] >> metis_tac[]) >>
  `buffer_allocation_base s sb.cs_next_id < dimword(:256)` by
    (drule_all unwrap_alloc_site_bound >> decide_tac) >>
  `lo <= w2n dst` by
    (simp[] >> Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >>
     fs[buffer_allocation_base_def,allocas_from_def] >> PairCases_on `x` >> fs[] >> metis_tac[]) >>
  `tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm` by
    fs[step_taint_def,mk_inst_def,adopt_reset_def,store_taint_def,imm_taint_def] >>
  `32 * type_slot_size rty <= type_memory_size rty /\ lo <= z.vs_alloca_next` by decide_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx ee HG tf (z with vs_inst_idx := LENGTH sc.cs_current_insts)` by
    (rpt strip_tac >>
     `stmt_state_rel H ctx func cenv cx ee s /\ ghost_inv_at (DF H) lo d cenv cx ee G tn s` by
       (fs[vv_post_def] >> metis_tac[]) >>
     drule_all runtime_code_copy_ghost_inv_at >> simp[]) >>
  suspend "runtime_frames"
QED

Resume ctor_unwrap_runtime_code_arrival[runtime_frames]:
  markerLib.RESUME_TAC >>
  `MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w (type_memory_size rty))] [root])
     (fn_insts func)` by
    (drule unwrap_alloc_generated_code >> strip_tac >> drule_all buffer_alloc_code >> gvs[]) >>
  `!i. i < buffer_allocation_base s sb.cs_next_id \/
       buffer_allocation_base s sb.cs_next_id + type_memory_size rty <= i ==>
       (i IN tm.t_mem <=> i IN tn.t_mem)` by
    (drule_all unwrap_alloc_taint_frame >> simp[] >> metis_tac[]) >>
  `tf.t_mem SUBSET tn.t_mem` by
    (fs[pred_setTheory.SUBSET_DEF] >> rpt strip_tac >>
     `w2n dst = buffer_allocation_base s sb.cs_next_id` by simp[] >>
     metis_tac[NOT_LESS_EQUAL]) >>
  `!off len. off+len <= w2n dst \/ w2n dst+type_memory_size rty <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory` by metis_tac[] >>
  `u = update_var root dst (buffer_allocation_fields s sb.cs_next_id (type_memory_size rty))` by simp[] >>
  drule_all runtime_code_copy_retained_frames_pure >> strip_tac >>
  drule_all runtime_copy_band >> disch_tac >>
  suspend "runtime_value"
QED

Resume ctor_unwrap_runtime_code_arrival[runtime_value]:
  markerLib.RESUME_TAC >>
  qabbrev_tac `q = z with vs_inst_idx := LENGTH sc.cs_current_insts` >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post H ctx func cenv cx e es sa sc s0 ee v (Var root) q` by
    simp[Abbr `q`,body_field_expr_post_inst_idx] >>
  `expr_post H0 ctx func cenv cx e es sa sc s0 ee v (Var root) q` by simp[] >>
  `lookup_var root z = SOME dst` by
    (fs[copy_runtime_frame_def,lookup_var_def] >> metis_tac[allocated_copy_operands_old]) >>
  `eval_operand (Var root) q = SOME dst` by fs[Abbr `q`,eval_operand_def,lookup_var_def] >>
  `ptr_covers HG tf root q (type_memory_size rty)` by
    (qpat_assum `ptr_covers HG tf root z _` mp_tac >>
     simp[Abbr `q`,ptr_covers_def,lookup_var_def]) >>
  `val_wf rty v` by (fs[expr_post_def,expr_val_at_def] >> metis_tac[]) >>
  `!i. w2n dst <= i /\ i < w2n dst + type_memory_size rty ==> i NOTIN tf.t_mem` by
    (fs[pred_setTheory.IN_DIFF,pred_setTheory.GSPECIFICATION] >> decide_tac) >>
  `lowered_value_type cenv e = expr_type e` by
    (drule compile_nonmemory_lowered_value_type >> simp[]) >>
  `post_value_type cenv e = expr_type e` by metis_tac[post_value_type_lowered] >>
  `type_memory_bytes cenv (lowered_value_type cenv e) <= type_memory_size rty` by fs[] >>
  `type_memory_size rty <= type_memory_size rty` by simp[] >>
  drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`) clean_buffer_pointer_posts >>
  simp[] >> disch_then drule >> simp[] >> strip_tac >>
  `expr_store_bound cx (post_value_type cenv e) v (Var root) q` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ q`
       (mp_then (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`) mp_tac
          expr_store_bound_capacity) >>
     simp[] >> disch_then irule >> rpt strip_tac >> gvs[Abbr `q`]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK q,HG,tf)` by
    (rpt strip_tac >> irule gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`q`,`HG`,`tf`] >>
  gvs[Abbr `q`,eval_operand_def,lookup_var_def] >> decide_tac
QED

Finalise ctor_unwrap_runtime_code_arrival
