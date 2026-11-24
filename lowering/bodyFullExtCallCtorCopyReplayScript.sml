(* The delayed constructor copy keeps its counted run and value at one endpoint. *)
Theory bodyFullExtCallCtorCopyReplay
Ancestors
  bodyFullUnwrapCodeCtorRun bodyFullUnwrapCodeCtorSemantic
  createCtorImmutableCopyBand createCtorSegmentArrival relation
  bodyFullUnwrapCodeCtorFrame exprPtrUnwrapCode exprPtrUnwrapCodeCopyShape
  exprPtrUnwrapAllocationFrame exprPtrUnwrapAllocEntry
  exprPtrUnwrapAllocation exprPtrUnwrapAllocSeparation
  fragGasOriginPtrDead bodyFieldMemoryProps bodyPtrEnvBuiltinsBoundary
  bodyFullHashKeccakFixed stateRelProj exprSimCopy exprSimProps
  exprSimMemDefs exprLoweringProps exprLowering context compileEnv
  immutableCopyExecution bufferAllocationExecution bodyPtrDefs loweringPosts
  venomState venomInst freshWrites words finite_map ptrDiscipline
  loweringStateRelDefs fragExec venomExecSemantics vyperStorageFootprint

Libs horizonTypeLib pureFrameLib

Theorem saved_ctor_immutable_operand[local]:
  lo <> 0 /\ local_ptrs_reserved ce su /\ immutable_base_zero ce t /\
  ghost_inv_at D lo d ce cx ee G tn t /\ ce.ce_imm_alloca = SOME region ==>
  eval_operand region t = SOME 0w /\ copy_old_operand su region /\
  op_taint tn region = {} /\ op_prov G region = NONE
Proof
  strip_tac >>
  conj_tac >- fs[immutable_base_zero_def] >>
  Cases_on `region` >>
  fs[copy_old_operand_def, op_taint_def, op_prov_def, ghost_inv_at_def] >>
  metis_tac[local_ptrs_reserved_imm_base]
QED

Theorem saved_ctor_copy_snapshot[local]:
  compile_alloc_buffer nb su = (buf,mid) /\ buf.buf_operand = Var root /\
  compile_imm_copy_to_memory T imm op0 buf.buf_operand n 0 mid = ((),sb) /\
  copy_runtime_frame mid allocst sb z /\
  step_inst_base (mk_inst su.cs_next_id ALLOCA [Lit (n2w nb)] [root]) t = OK u /\
  allocst = u with vs_inst_idx := k /\ lookup_var root allocst = SOME dst /\
  (!x. op0 = Var x ==> not_fresh_at su x) /\ eval_operand op0 t = SOME a /\
  (n <> 0 ==> !region. imm = SOME region ==>
    eval_operand region t = SOME 0w /\ copy_old_operand su region) ==>
  z.vs_memory = (immutable_transfers F T a dst n 0 allocst).vs_memory
Proof
  strip_tac >> Cases_on `n = 0`
  >- gvs[compile_imm_copy_to_memory_def, comp_return_def,
         copy_runtime_frame_def, immutable_transfers_def, run_inst_seq_def] >>
  `!op. (!p. op = Var p ==> p <> root) ==>
        eval_operand op allocst = eval_operand op t` by
    (gen_tac >> strip_tac >> qpat_assum `allocst = _` SUBST1_TAC >>
     irule unwrap_alloc_operand_frame >> metis_tac[]) >>
  `!region. imm = SOME region ==>
    eval_operand region allocst = SOME 0w /\ copy_old_operand mid region` by
    (gen_tac >> disch_tac >>
     `eval_operand region t = SOME 0w /\ copy_old_operand su region` by metis_tac[] >>
     `!x. region = Var x ==> x <> root` by
       (fs[copy_old_operand_def] >> metis_tac[unwrap_alloc_old_operand_distinct]) >>
     conj_tac >- metis_tac[] >>
     `ci_mono su mid` by metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
     metis_tac[copy_old_operand_mono, ci_mono_def]) >>
  `copy_old_operand mid op0 /\ not_fresh_at mid root` by
    metis_tac[allocated_copy_operands_old] >>
  `!x. op0 = Var x ==> x <> root` by metis_tac[unwrap_alloc_old_operand_distinct] >>
  `eval_operand op0 allocst = SOME a` by metis_tac[] >>
  `eval_operand buf.buf_operand allocst = SOME dst /\ copy_old_operand mid buf.buf_operand` by
    (asm_rewrite_tac[eval_operand_def, copy_old_operand_def, operand_11] >> (gvs[eval_operand_def, copy_old_operand_def, operand_11])) >>
  drule_all copy_ctor_run >> strip_tac >> fs[copy_runtime_frame_def] >> metis_tac[]
QED

Theorem extcall_saved_ctor_copy_replay_band:
  lowered_value_type ce e = expr_type e /\
  ~is_word_type (expr_type e) /\ p.ptr_location = LocCode /\ ce.ce_is_ctor /\
  compile_expr ce (expr_type e) e si = (LocatedValue (expr_type e) p,sm) /\
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
  (!w. eval_operand p.ptr_operand t = SOME w ==>
    w2n w + type_memory_size rt <= lo /\
    (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
      val_in_memory rt v (w2n w) mem)) /\
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
  `post_value_type ce e = expr_type e` by simp[post_value_type_lowered] >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[Abbr `H0`, storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx fn ce cx e ee si su t ee (Value v) (LocatedValue (expr_type e) p) t /\
    ghost_inv_at (DF H) lo d ce cx ee G tn t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
       (qspec_then `H` mp_tac) >> simp[vv_post_def, vv_at_def, vv_own_def] >>
     metis_tac[vv_post_def, vv_at_def, vv_own_def]) >>
  `vv_post H0 ctx fn ce cx e ee si su t ee (Value v) (LocatedValue (expr_type e) p) t /\
   ghost_inv_at (DF H0) lo d ce cx ee G tn t` by metis_tac[] >>
  drule_all vv_post_code_source >>
  simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def] >> strip_tac >>
  `stmt_state_rel H0 ctx fn ce cx ee t` by fs[vv_post_def] >>
  `local_ptrs_reserved ce su` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at su x` by metis_tac[not_fresh_at_mono] >>
  `si.cs_next_var <= su.cs_next_var /\ si.cs_next_id <= su.cs_next_id` by decide_tac >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t)` by metis_tac[stmt_state_rel_allocas_below_fmp] >>
  `op_taint tn p.ptr_operand = {} /\ op_prov G p.ptr_operand = NONE` by
    fs[ptr_vv_ok_def, vv_operand_def] >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def, compile_ensure_in_memory_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  gvs[] >> rename1 `compile_alloc_buffer _ su = (buf,mid)` >>
  rename1 `fn_has_code su sb fn` >>
  `unwrap_value ce (LocatedValue (expr_type e) p) su = (buf.buf_operand,sb)` by
    simp[unwrap_value_def, compile_ensure_in_memory_def,
         comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  `type_memory_size rt = 32 * type_slot_size rt` by
    simp[valueEncodingPropsTheory.type_memory_size_slots] >>
  `(type_memory_size rt + 31) DIV 32 = type_slot_size rt` by
    simp[valueEncodingPropsTheory.type_memory_size_slots, arithmeticTheory.ADD_DIV_ADD_DIV] >>
  `type_memory_size rt < dimword(:256)` by (fs[wordsTheory.dimword_def] >> decide_tac) >>
  `ci_mono su mid` by metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `ci_mono mid sb` by metis_tac[ci_mono_compile_imm_copy_to_memory, pairTheory.SND] >>
  `fn_has_code su mid fn /\ fn_has_code mid sb fn` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  rename1 `eval_operand p.ptr_operand t = SOME a` >>
  `w2n a + 32 * type_slot_size rt <= lo` by decide_tac >>
  `compile_imm_copy_to_memory T ce.ce_imm_alloca p.ptr_operand buf.buf_operand
     (type_slot_size rt) 0 mid = ((),sb)` by metis_tac[] >>
  `type_slot_size rt <> 0 ==> !region. ce.ce_imm_alloca = SOME region ==>
    eval_operand region t = SOME 0w /\ copy_old_operand su region /\
    op_taint tn region = {} /\ op_prov G region = NONE` by
    (disch_tac >> gen_tac >> disch_tac >> `lo <> 0` by decide_tac >>
     `ghost_inv_at (DF H0) lo d ce cx ee G tn t` by metis_tac[] >>
     drule_then assume_tac stmt_state_rel_immutable_base_zero >>
     drule_all saved_ctor_immutable_operand >> simp[]) >>
  drule_all ctor_code_copy_origin_execution >>
  disch_then (qspecl_then [`explicit`,`PG`,
    `<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>`]
    strip_assume_tac) >>
  rename1 `copy_runtime_frame mid allocst sb z` >>
  rename1 `lookup_var root allocst = SOME dst` >>
  drule_all immutable_copy_band >> disch_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post H ctx fn ce cx e ee si sb t ee v buf.buf_operand z` by
    (rpt strip_tac >>
     `vv_post H ctx fn ce cx e ee si su t ee (Value v) (LocatedValue (expr_type e) p) t` by
       metis_tac[] >>
     `!ty. evaluate_type (get_tenv cx) (expr_type e) = SOME ty ==>
        type_memory_bytes ce (expr_type e) = type_memory_size ty` by simp[] >>
     `si.cs_next_var <= su.cs_next_var /\ si.cs_next_id <= su.cs_next_id` by decide_tac >>
     `MAP FDOM ee.scopes = MAP FDOM ee.scopes` by simp[] >>
     drule_all ctor_code_copy_endpoint_post >> simp[]) >>
  `allocst.vs_memory = t.vs_memory /\
   allocst.vs_accounts = t.vs_accounts /\ allocst.vs_transient = t.vs_transient /\
   allocst.vs_call_ctx = t.vs_call_ctx /\ allocst.vs_immutables = t.vs_immutables` by
    (drule unwrap_alloc_runtime_frame >> simp[] >> metis_tac[]) >>
  `buffer_allocation_base t su.cs_next_id < dimword(:256)` by
    (drule_all unwrap_alloc_site_bound >> decide_tac) >>
  `lo <= w2n dst` by
    (simp[] >> Cases_on `FLOOKUP t.vs_allocas su.cs_next_id` >>
     fs[buffer_allocation_base_def, allocas_from_def] >>
     PairCases_on `x` >> fs[] >> metis_tac[]) >>
  `si.cs_next_var <= su.cs_next_var /\ si.cs_next_id <= su.cs_next_id` by decide_tac >>
  `MAP FDOM ee.scopes = MAP FDOM ee.scopes` by simp[] >>
  `su.cs_next_var <= mid.cs_next_var` by fs[ci_mono_def] >>
  `tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm` by
    fs[step_taint_def, mk_inst_def, adopt_reset_def, store_taint_def, imm_taint_def] >>
  `32 * type_slot_size rt <= type_memory_size rt /\ lo <= z.vs_alloca_next` by decide_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    ghost_inv_at (DF H) lo d ce cx ee HG tf (z with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (rpt strip_tac >>
     `stmt_state_rel H ctx fn ce cx ee t /\ ghost_inv_at (DF H) lo d ce cx ee G tn t` by
       (fs[vv_post_def] >> metis_tac[]) >>
     drule_all ctor_code_copy_ghost_inv_at >> simp[]) >>
  drule_all ctor_code_copy_exterior_frames >> strip_tac >>
  `wb_frame ce ee ee si t t /\ ghost_kept_at lo ce ee si G tn t G tn` by
    simp[wb_frame_def, ghost_kept_at_def] >>
  `u = update_var root dst (buffer_allocation_fields t su.cs_next_id (type_memory_size rt))` by simp[] >>
  drule_all ctor_code_copy_retained_frames_pure >> strip_tac >>
  `not_fresh_at mid root` by (drule_all allocated_copy_operands_old >> simp[]) >>
  `lookup_var root z = SOME dst` by (fs[copy_runtime_frame_def, lookup_var_def] >> metis_tac[]) >>
  `val_wf rt v /\ w2n a + type_memory_size rt < dimword(:256)` by
    metis_tac[immutable_holds_bounds] >>
  `regions_disjoint (w2n a) (type_memory_size rt) (w2n dst) (type_memory_size rt)` by
    (gvs[regions_disjoint_def] >> decide_tac) >>
  `z.vs_memory = (immutable_transfers F T a dst (type_slot_size rt) 0 allocst).vs_memory` by
    (`type_slot_size rt <> 0 ==> !region. ce.ce_imm_alloca = SOME region ==>
        eval_operand region t = SOME 0w /\ copy_old_operand su region` by metis_tac[] >>
     drule_all saved_ctor_copy_snapshot >> simp[]) >>
  `MEM (mk_inst su.cs_next_id ALLOCA [Lit (n2w (type_memory_size rt))] [root]) (fn_insts fn)` by
    (drule unwrap_alloc_generated_code >> strip_tac >> drule_all exprSimAllocTheory.buffer_alloc_code >> gvs[]) >>
  `!i. i < buffer_allocation_base t su.cs_next_id \/
       buffer_allocation_base t su.cs_next_id + type_memory_size rt <= i ==>
       (i IN tm.t_mem <=> i IN tn.t_mem)` by
    (drule_all unwrap_alloc_taint_frame >> simp[] >> metis_tac[]) >>
  `!i. i < type_memory_size rt ==>
     (w2n dst+i IN tf.t_mem <=> w2n a+i IN tm.t_mem)` by
    (rpt strip_tac >>
     `w2n dst <= w2n dst+i /\ w2n dst+i < w2n dst+32*type_slot_size rt /\
      w2n a+i < buffer_allocation_base t su.cs_next_id` by (gvs[] >> decide_tac) >>
     `w2n dst+i-w2n dst = i` by decide_tac >> metis_tac[]) >>
  `val_footprint rt v <= type_memory_size rt /\ val_store_size rt v <= type_memory_size rt` by
    simp[exprSimPropsTheory.val_footprint_le, exprSimPropsTheory.val_store_size_le] >>
  `ptr_val_ok cx (expr_type e) v (Var root) HG tf (z with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (`!mem. mem_agree_outside tm.t_mem allocst.vs_memory mem ==>
        val_in_memory rt v (w2n a) mem` by
       (`mem_bytes_at (w2n a) (type_memory_size rt) allocst.vs_memory =
         mem_bytes_at (w2n a) (type_memory_size rt) t.vs_memory` by simp[] >>
        `!i. w2n a <= i /\ i < w2n a + type_memory_size rt /\ i IN tm.t_mem ==> i IN tn.t_mem` by
          (rpt strip_tac >>
           `i < buffer_allocation_base t su.cs_next_id` by (gvs[] >> decide_tac) >>
           metis_tac[]) >>
        gen_tac >> disch_tac >>
        irule bodyPtrMakeArrayMemoryFrameTheory.robust_val_in_memory_shrinking_frame >>
        conj_tac >- first_assum ACCEPT_TAC >>
        qexistsl [`tn.t_mem`,`tm.t_mem`,`t.vs_memory`,`allocst.vs_memory`,`type_memory_size rt`] >>
        asm_rewrite_tac[]) >>
     drule_all ctor_code_copy_ptr_val_ok >> simp[]) >>
  `ptr_buf_ok ce e (Var root) HG z` by
    (irule ptr_covers_buf_ok >> qexistsl [`type_memory_size rt`,`tf`] >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post H ctx fn ce cx e ee si sb t ee v (Var root)
      (z with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (gen_tac >> disch_tac >> rewrite_tac[body_field_expr_post_inst_idx] >>
     qpat_assum `buf.buf_operand = Var root` (rewrite_tac o single o SYM) >>
     first_x_assum irule >> first_assum ACCEPT_TAC) >>
  pop_assum (mk_asm "copy_post") >>
  `eval_operand (Var root) z = SOME dst` by
    (rewrite_tac[eval_operand_def] >> first_assum ACCEPT_TAC) >>
  `expr_val_at ce cx (expr_type e) su sb ee v (Var root)
    (z with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (`vv_post H0 ctx fn ce cx e ee su su t ee (Value v) (LocatedValue (expr_type e) p) t` by
       (`vv_post H0 ctx fn ce cx e ee si su t ee (Value v) (LocatedValue (expr_type e) p) t` by metis_tac[] >>
        qpat_assum `p.ptr_location = LocCode` (fn loc =>
          pop_assum mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
          simp[loc, vv_post_def, vv_at_def, vv_own_def,
            exprSimPropsTheory.locals_kept_refl, pure_frame_refl])) >>
     `!ty. evaluate_type (get_tenv cx) (expr_type e) = SOME ty ==>
       type_memory_bytes ce (expr_type e) = type_memory_size ty` by simp[] >>
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
          ``k:num`` |-> ``SUC t.vs_inst_idx``] (horizonTypeLib.at_horizon_named "H" ctor_code_copy_endpoint_post))) >>
        asm_simp_tac (srw_ss()) []) >>
     qpat_assum `expr_post H0 ctx fn ce cx e ee su sb t ee v (Var root) z`
       (mp_tac o cj 4 o REWRITE_RULE [expr_post_def]) >>
     simp[expr_val_at_def, instIdxIndepTheory.eval_op_inst_idx,
       local_region_def, venomStateTheory.lookup_var_def]) >>
  qexistsl [`z with vs_inst_idx := LENGTH sb.cs_current_insts`,`HG`,`tf`] >>
  asm_rewrite_tac[] >> simp[] >>
  conj_tac >-
    (gen_tac >> disch_tac >>
     conj_tac >- (irule gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC) >>
     asm "copy_post" (qspec_then `H` mp_tac) >>
     asm_rewrite_tac[expr_post_def] >>
     disch_then strip_assume_tac >> simp[]) >>
  conj_tac >-
    (asm "copy_post" (qspec_then `H0` mp_tac) >>
     asm_rewrite_tac[expr_post_def] >>
     disch_then strip_assume_tac >> first_assum ACCEPT_TAC) >>
  simp[expr_store_bound_def, blockPrefixEquivTheory.lookup_var_set_inst_idx] >>
  gvs[] >> decide_tac
QED

Theorem extcall_saved_ctor_copy_replay_pure:
  lowered_value_type ce e = expr_type e /\
  ~is_word_type (expr_type e) /\ p.ptr_location = LocCode /\ ce.ce_is_ctor /\
  compile_expr ce (expr_type e) e si = (LocatedValue (expr_type e) p,sm) /\
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
  (!w. eval_operand p.ptr_operand t = SOME w ==>
    w2n w + type_memory_size rt <= lo /\
    (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
      val_in_memory rt v (w2n w) mem)) /\
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
  disch_tac >> mp_tac (SPEC_ALL extcall_saved_ctor_copy_replay_band) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qexistsl [`z`,`G'`,`tn'`] >> asm_rewrite_tac[]
QED

Theorem extcall_saved_ctor_copy_replay =
  pureFrameLib.drop_frame extcall_saved_ctor_copy_replay_pure
