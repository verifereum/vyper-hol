(* Runtime code arguments are copied after the tuple slot address is
   computed. Retain the unrestricted counted path at that same endpoint. *)
Theory bodyFullExtCallRuntimeCopyReplay
Ancestors
  bodyFullUnwrapCodeRuntimeRun bodyFullUnwrapCodeRuntimeFrame
  createCtorImmutableCopyBand createCtorSegmentArrival relation
  exprPtrUnwrapCode exprPtrUnwrapCodeCopyShape exprPtrUnwrapCodeCopySemantic
  exprPtrUnwrapAllocation
  exprPtrCleanBufferPost bodyImmutableUnwrapMemory bodyFieldMemoryProps
  fragGasOriginPtrDead bodyFullHashKeccakFixed freshWrites
  exprSimMemDefs exprPtrUnwrapAllocationFrame exprPtrUnwrapAllocSeparation
  exprSimCopy exprSimStorageCopy exprSimAlloc exprLoweringProps
  loweringPosts loweringStateRelDefs bodyPtrDefs ptrDiscipline
  compileEnv context vyperStorageFootprint vyperState valueEncodingProps
  exprLowering exprSimSliceCaptureControl venomState venomInst bufferAllocationExecution finite_map words arithmetic

Libs horizonTypeLib pureFrameLib

Theorem extcall_saved_runtime_copy_replay_band:
  lowered_value_type ce e = expr_type e /\
  ~is_word_type (expr_type e) /\ p.ptr_location = LocCode /\ ~ce.ce_is_ctor /\
  sm.cs_next_var <= su.cs_next_var /\ sm.cs_next_id <= su.cs_next_id /\
  unwrap_value ce (LocatedValue (expr_type e) p) su = (src,sb) /\
  local_ptrs_reserved ce si /\ local_ptrs_reserved ce sm /\
  si.cs_next_var <= sm.cs_next_var /\ si.cs_next_id <= sm.cs_next_id /\
  fn_has_code su sb fn /\ fn_inst_ids_distinct fn /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
  type_memory_bytes ce (expr_type e) = type_memory_size rt /\
  type_memory_size rt < 2**64 /\
  storage_trace_domain cx st0 ee.storage_trace /\
  ptr_vv_ok cx (expr_type e) (Value v) (LocatedValue (expr_type e) p) ee G tn t /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx fn ce cx e ee si sm t ee (Value v) (LocatedValue (expr_type e) p) t /\
    ghost_inv_at (DF H) lo d ce cx ee G tn t) /\
  alloca_history fn t /\ ~t.vs_halted /\ t.vs_current_bb = su.cs_current_bb /\
  t.vs_inst_idx = LENGTH su.cs_current_insts /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) ==>
  ?z G' tn'.
    pure_frame ce fn ee su t z /\
    gas_origin_ptr_path
      (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>,
       lo,explicit,ctx,fn,PG) (t,G,tn) [] (OK z,G',tn') /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (t,G,tn) [] (OK z,G',tn') /\
      stmt_state_rel H ctx fn ce cx ee z /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d ce cx ee G' tn' z) /\
    expr_val_rel cx (expr_type e) v src z /\ ptr_val_ok cx (expr_type e) v src G' tn' z /\
    expr_store_bound cx (expr_type e) v src z /\ ptr_buf_ok ce e src G' z /\
    (!w. eval_operand src z = SOME w ==>
      type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    alloca_history fn z /\ t.vs_alloca_next <= z.vs_alloca_next /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at su x ==>
       lookup_var x z = lookup_var x t /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
    wb_frame ce ee ee su t z /\ ghost_kept_at lo ce ee su G tn t G' tn' /\
    expr_val_at ce cx (expr_type e) su sb ee v src z /\
    RTC (\r q. ?i. ctor_segment_fetch fn r = SOME i /\
                     su.cs_next_id <= i.inst_id /\ i.inst_id < sb.cs_next_id /\
                     i.inst_opcode <> INVOKE /\ ctor_segment_next fn r i = SOME q) t z
Proof
  strip_tac >>
  `post_value_type ce e = expr_type e` by metis_tac[post_value_type_lowered] >>
  `si.cs_next_var <= su.cs_next_var /\ si.cs_next_id <= su.cs_next_id` by decide_tac >>
  `local_ptrs_reserved ce su` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at su x` by
    metis_tac[not_fresh_at_mono] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx fn ce cx e ee si su t ee (Value v) (LocatedValue (expr_type e) p) t /\
    ghost_inv_at (DF H) lo d ce cx ee G tn t` by
    (rpt gen_tac >> disch_tac >> first_x_assum (drule_then strip_assume_tac) >>
     fs[vv_post_def,vv_at_def]) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> vv_post H _ _ _ _ _ _ _ su _ _ _ _ _ /\ _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  drule_all vv_post_code_source >>
  disch_then (CONJUNCTS_THEN2 kall_tac
    (qx_choose_then `a` strip_assume_tac o
     SIMP_RULE (srw_ss()) [vyperStateTheory.read_result_def,vyperStateTheory.return_def])) >>
  `stmt_state_rel H0 ctx fn ce cx ee t` by fs[vv_post_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `op_taint tn p.ptr_operand = {}` by fs[ptr_vv_ok_def] >>
  `compile_ensure_in_memory p.ptr_operand LocCode
    (type_memory_bytes ce (expr_type e))
    ((type_memory_bytes ce (expr_type e) + 31) DIV 32) F ce.ce_imm_alloca su = (src,sb)` by
    gvs[unwrap_value_def] >>
  drule_all ensure_runtime_code_layout >> strip_tac >>
  `(type_memory_size rt + 31) DIV 32 = type_slot_size rt` by
    simp[type_memory_size_slots,ADD_DIV_ADD_DIV] >>
  `compile_alloc_buffer (type_memory_size rt) su = (buf,mid) /\
   compile_imm_copy_to_memory F ce.ce_imm_alloca p.ptr_operand buf.buf_operand
     (type_slot_size rt) 0 mid = ((),sb)` by gvs[] >>
  `type_memory_size rt = 32 * type_slot_size rt` by simp[type_memory_size_slots] >>
  `w2n a + 32 * type_slot_size rt <= LENGTH t.vs_data_section /\
   w2n a + 32 * type_slot_size rt < dimword(:256)` by
    (drule_all runtime_immutable_data_section >> disch_tac >>
     drule_all immutable_holds_bounds >> simp[]) >>
  `type_memory_size rt < dimword(:256)` by decide_tac >>
  drule_all runtime_code_copy_origin_execution >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`,
    `<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>`]
    strip_assume_tac) >>
  rename1 `copy_runtime_frame mid allocst sb z` >>
  rename1 `lookup_var root allocst = SOME dst` >>
  drule_all immutable_copy_band >> disch_tac >>
  suspend "posts"
QED

Resume extcall_saved_runtime_copy_replay_band[posts]:
  markerLib.RESUME_TAC >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post H ctx fn ce cx e ee si sb t ee v (Var root) z` by
    (rpt strip_tac >>
     `vv_post H ctx fn ce cx e ee si su t ee (Value v) (LocatedValue (expr_type e) p) t` by
       metis_tac[] >>
     `!ty. evaluate_type (get_tenv cx) (expr_type e) = SOME ty ==>
       type_memory_bytes ce (expr_type e) = type_memory_size ty` by simp[] >>
     `MAP FDOM ee.scopes = MAP FDOM ee.scopes` by simp[] >>
     drule_all unwrap_code_copy_endpoint_post >> simp[]) >>
  `allocst.vs_memory = t.vs_memory /\ allocst.vs_accounts = t.vs_accounts /\
   allocst.vs_transient = t.vs_transient /\ allocst.vs_call_ctx = t.vs_call_ctx /\
   allocst.vs_immutables = t.vs_immutables` by
    (drule unwrap_alloc_runtime_frame >> simp[] >> metis_tac[]) >>
  `buffer_allocation_base t su.cs_next_id < dimword(:256)` by
    (drule_all unwrap_alloc_site_bound >> decide_tac) >>
  `lo <= w2n dst` by
    (simp[] >> Cases_on `FLOOKUP t.vs_allocas su.cs_next_id` >>
     fs[buffer_allocation_base_def,allocas_from_def] >> PairCases_on `x` >> fs[] >> metis_tac[]) >>
  `tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm` by
    fs[step_taint_def,mk_inst_def,adopt_reset_def,store_taint_def,imm_taint_def] >>
  `32 * type_slot_size rt <= type_memory_size rt /\ lo <= z.vs_alloca_next` by decide_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    ghost_inv_at (DF H) lo d ce cx ee HG tf (z with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (rpt strip_tac >>
     `stmt_state_rel H ctx fn ce cx ee t /\ ghost_inv_at (DF H) lo d ce cx ee G tn t` by
       (fs[vv_post_def] >> metis_tac[]) >>
     drule_all runtime_code_copy_ghost_inv_at >> simp[]) >>
  suspend "frames"
QED

Resume extcall_saved_runtime_copy_replay_band[frames]:
  markerLib.RESUME_TAC >>
  `MEM (mk_inst su.cs_next_id ALLOCA [Lit (n2w (type_memory_size rt))] [root])
     (fn_insts fn)` by
    (drule unwrap_alloc_generated_code >> strip_tac >> drule_all buffer_alloc_code >> gvs[]) >>
  `!i. i < buffer_allocation_base t su.cs_next_id \/
       buffer_allocation_base t su.cs_next_id + type_memory_size rt <= i ==>
       (i IN tm.t_mem <=> i IN tn.t_mem)` by
    (drule_all unwrap_alloc_taint_frame >> simp[] >> metis_tac[]) >>
  `tf.t_mem SUBSET tn.t_mem` by
    (fs[pred_setTheory.SUBSET_DEF] >> rpt strip_tac >>
     `w2n dst = buffer_allocation_base t su.cs_next_id` by simp[] >>
     metis_tac[NOT_LESS_EQUAL]) >>
  `!off len. off+len <= w2n dst \/ w2n dst+type_memory_size rt <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len t.vs_memory` by metis_tac[] >>
  `u = update_var root dst (buffer_allocation_fields t su.cs_next_id (type_memory_size rt))` by simp[] >>
  `ghost_kept_at lo ce ee si G tn t G tn` by simp[ghost_kept_at_def] >>
  drule_all runtime_code_copy_retained_frames_pure >> strip_tac >>
  suspend "value"
QED

Resume extcall_saved_runtime_copy_replay_band[value]:
  markerLib.RESUME_TAC >>
  qabbrev_tac `q = z with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `expr_post H0 ctx fn ce cx e ee si sb t ee v (Var root) q` by simp[Abbr `q`] >>
  `lookup_var root z = SOME dst` by
    (fs[copy_runtime_frame_def,lookup_var_def] >>
     metis_tac[allocated_copy_operands_old]) >>
  `eval_operand (Var root) q = SOME dst` by fs[Abbr `q`,eval_operand_def,lookup_var_def] >>
  `ptr_covers HG tf root q (type_memory_size rt)` by
    (qpat_assum `ptr_covers HG tf root z _` mp_tac >>
     simp[Abbr `q`,ptr_covers_def,lookup_var_def]) >>
  `val_wf rt v` by (fs[expr_post_def,expr_val_at_def] >> metis_tac[]) >>
  `!i. w2n dst <= i /\ i < w2n dst + type_memory_size rt ==> i NOTIN tf.t_mem` by
    (fs[pred_setTheory.IN_DIFF,pred_setTheory.GSPECIFICATION] >> decide_tac) >>
  `type_memory_bytes ce (lowered_value_type ce e) <= type_memory_size rt` by fs[] >>
  `type_memory_size rt <= type_memory_size rt` by simp[] >>
  drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`) clean_buffer_pointer_posts >>
  simp[] >> disch_then drule >> simp[] >> strip_tac >>
  `w2n dst + type_memory_size rt <= q.vs_alloca_next` by
    ((qpat_assum `w2n dst + type_memory_size rt <= z.vs_alloca_next` mp_tac >>
     simp[Abbr `q`] >> (gvs[]))) >>
  `expr_store_bound cx (expr_type e) v (Var root) q` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ q`
       (mp_then (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`) mp_tac
          expr_store_bound_capacity) >>
     simp[] >> disch_then irule >> rpt strip_tac >> gvs[] >>
     qexists `dst` >> simp[]) >>
  `expr_val_rel cx (expr_type e) v (Var root) q` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ q`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     metis_tac[]) >>
  `!w. eval_operand (Var root) q = SOME w ==>
    type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= q.vs_alloca_next` by
    (qpat_assum `eval_operand (Var root) q = SOME dst` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms] >> disj2_tac >> once_rewrite_tac[ADD_COMM] >>
     first_assum ACCEPT_TAC) >>
  `expr_val_at ce cx (expr_type e) su sb ee v (Var root) q` by
    (`vv_post H0 ctx fn ce cx e ee su su t ee (Value v) (LocatedValue (expr_type e) p) t` by
       (`vv_post H0 ctx fn ce cx e ee si su t ee (Value v) (LocatedValue (expr_type e) p) t` by metis_tac[] >>
        qpat_assum `p.ptr_location = LocCode` (fn loc =>
          qpat_assum `vv_post H0 ctx fn ce cx e ee si su t ee _ _ t` mp_tac >>
          POP_ASSUM_LIST (K ALL_TAC) >>
          simp[loc, vv_post_def, vv_at_def, vv_own_def,
            exprSimPropsTheory.locals_kept_refl, pure_frame_refl])) >>
     `!ty. evaluate_type (get_tenv cx) (expr_type e) = SOME ty ==>
       type_memory_bytes ce (expr_type e) = type_memory_size ty` by simp[] >>
     `MAP FDOM ee.scopes = MAP FDOM ee.scopes` by simp[] >>
     `su.cs_next_var <= su.cs_next_var /\ su.cs_next_id <= su.cs_next_id` by simp[] >>
     `expr_post H0 ctx fn ce cx e ee su sb t ee v (Var root) z` by
       (mp_tac (Q.INST [`H` |-> `H0`] (INST [``s:venom_state`` |-> ``t:venom_state``,
          ``s0:venom_state`` |-> ``t:venom_state``,
          ``sa:compile_state`` |-> ``su:compile_state``,
          ``sm:compile_state`` |-> ``su:compile_state``,
          ``t:vyperAST$type`` |-> ``expr_type e``,
          ``cenv:compile_env`` |-> ``ce:compile_env``,
          ``func:ir_function`` |-> ``fn:ir_function``,
          ``es:evaluation_state`` |-> ``ee:evaluation_state``,
          ``a:venom_state`` |-> ``allocst:venom_state``,
          ``op:operand`` |-> ``Var root``, ``nb:num`` |-> ``type_memory_size rt``,
          ``k:num`` |-> ``SUC t.vs_inst_idx``] (horizonTypeLib.at_horizon_named "H" unwrap_code_copy_endpoint_post))) >>
        asm_simp_tac (srw_ss()) []) >>
     `expr_val_at ce cx (expr_type e) su sb ee v (Var root) z` by
       (qpat_assum `expr_post H0 ctx fn ce cx e ee su sb t ee v (Var root) z`
         (mp_tac o cj 4 o REWRITE_RULE [expr_post_def]) >> asm_rewrite_tac[]) >>
     qpat_assum `Abbrev (q = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     asm_rewrite_tac[slice_capture_value_index]) >>
  `pure_frame ce fn ee su t q` by simp[Abbr `q`] >>
  qexistsl [`q`,`HG`,`tf`] >>
  asm_rewrite_tac[] >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post H _ _ _ _ _ _ _ _ _ _ _ _ z`
        (qspec_then `H` (drule_then assume_tac)) >>
      `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (t,G,tn) [] (OK q,HG,tf)` by
        (irule gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC) >>
      fs[Abbr `q`,expr_post_def,stmt_state_rel_inst_idx]) >>
  gvs[Abbr `q`,eval_operand_def,lookup_var_def]
QED

Finalise extcall_saved_runtime_copy_replay_band

Theorem extcall_saved_runtime_copy_replay_pure:
  lowered_value_type ce e = expr_type e /\
  ~is_word_type (expr_type e) /\ p.ptr_location = LocCode /\ ~ce.ce_is_ctor /\
  sm.cs_next_var <= su.cs_next_var /\ sm.cs_next_id <= su.cs_next_id /\
  unwrap_value ce (LocatedValue (expr_type e) p) su = (src,sb) /\
  local_ptrs_reserved ce si /\ local_ptrs_reserved ce sm /\
  si.cs_next_var <= sm.cs_next_var /\ si.cs_next_id <= sm.cs_next_id /\
  fn_has_code su sb fn /\ fn_inst_ids_distinct fn /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
  type_memory_bytes ce (expr_type e) = type_memory_size rt /\
  type_memory_size rt < 2**64 /\
  storage_trace_domain cx st0 ee.storage_trace /\
  ptr_vv_ok cx (expr_type e) (Value v) (LocatedValue (expr_type e) p) ee G tn t /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx fn ce cx e ee si sm t ee (Value v) (LocatedValue (expr_type e) p) t /\
    ghost_inv_at (DF H) lo d ce cx ee G tn t) /\
  alloca_history fn t /\ ~t.vs_halted /\ t.vs_current_bb = su.cs_current_bb /\
  t.vs_inst_idx = LENGTH su.cs_current_insts /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) ==>
  ?z G' tn'.
    pure_frame ce fn ee su t z /\
    gas_origin_ptr_path
      (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>,
       lo,explicit,ctx,fn,PG) (t,G,tn) [] (OK z,G',tn') /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (t,G,tn) [] (OK z,G',tn') /\
      stmt_state_rel H ctx fn ce cx ee z /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d ce cx ee G' tn' z) /\
    expr_val_rel cx (expr_type e) v src z /\ ptr_val_ok cx (expr_type e) v src G' tn' z /\
    expr_store_bound cx (expr_type e) v src z /\ ptr_buf_ok ce e src G' z /\
    (!w. eval_operand src z = SOME w ==>
      type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    alloca_history fn z /\ t.vs_alloca_next <= z.vs_alloca_next /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at su x ==>
       lookup_var x z = lookup_var x t /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
    wb_frame ce ee ee su t z /\ ghost_kept_at lo ce ee su G tn t G' tn' /\
    expr_val_at ce cx (expr_type e) su sb ee v src z
Proof
  disch_tac >> mp_tac (SPEC_ALL extcall_saved_runtime_copy_replay_band) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qexistsl [`z`,`G'`,`tn'`] >> asm_rewrite_tac[]
QED

Theorem extcall_saved_runtime_copy_replay =
  pureFrameLib.drop_frame extcall_saved_runtime_copy_replay_pure
