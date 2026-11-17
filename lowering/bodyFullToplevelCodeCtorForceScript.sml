(* One constructor immutable-copy endpoint for every finite horizon. *)
Theory bodyFullToplevelCodeCtorForce
Ancestors
  bodyFullToplevelCodeCtorExecution bodyFullToplevelCodeCtorValuePosts
  bodyFullToplevelCodeCtorFramePosts bodyFullToplevelSlotForce
  bodyImmutableUnwrapMemory exprPtrUnwrapCodeCopyShape valueEncodingProps
  vyperStorageFootprint loweringPosts exprLowering bodyPtrDefs exprSimProps
  context exprLoweringProps loweringHalt pair compileEnv fragExec
  loweringStateRelDefs exprSimHypsDefs exprSimCopy venomState ptrDiscipline

Theorem toplevel_code_ctor_force_full:
  vv = LocatedValue t p /\ p.ptr_location = LocCode /\
  ~is_word_type t /\ cenv.ce_is_ctor /\
  compile_expr cenv ty (TopLevelName ann nsid) sa = (vv,sm) /\
  (is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
    is_word_type (expr_type (TopLevelName ann nsid))) /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  unwrap_value cenv vv sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv (TopLevelName ann nsid)) = SOME rt /\
    ~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
    type_memory_bytes cenv (post_value_type cenv (TopLevelName ann nsid)) = type_memory_size rt /\
    type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv (TopLevelName ann nsid)) = SOME rty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx (TopLevelName ann nsid) es sa sm s0 ee tv vv s /\
    ghost_inv_at (DF H) lo ret cenv cx ee G tn s) /\
  vv_store_bound cx (expr_type (TopLevelName ann nsid))
    (lowered_value_type cenv (TopLevelName ann nsid)) ee tv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv (TopLevelName ann nsid)) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
    ptr_buf_ok cenv (TopLevelName ann nsid) op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv (TopLevelName ann nsid) p.ptr_operand G s) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx tv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (TopLevelName ann nsid)) = SOME rt /\
        eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v z G' tn'.
    read_result cx tv ee = (INL v,ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,G',tn') /\
      expr_post H ctx func cenv cx (TopLevelName ann nsid) es sa sc s0 ee v op z /\
      ghost_inv_at (DF H) lo ret cenv cx ee G' tn' z) /\
    (~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
      vv_at cenv cx (post_value_type cenv (TopLevelName ann nsid)) sa sc ee tv
        (LocatedValue (post_value_type cenv (TopLevelName ann nsid)) (mk_ptr op LocMemory)) z) /\
    expr_store_bound cx (expr_type (TopLevelName ann nsid)) v op z /\
    z.vs_current_bb = sc.cs_current_bb /\ z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv (TopLevelName ann nsid)) v op G' tn' z /\
    (~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
      ptr_buf_ok cenv (TopLevelName ann nsid) op G' z) /\
    (~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
      !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv (TopLevelName ann nsid)) = SOME rt /\
        eval_operand op z = SOME w ==> type_memory_size rt = 0 \/
        w2n w+type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G' tn' /\
    (!x. not_fresh_at sb x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv ee ee sb s z /\ ghost_kept_at lo cenv ee sb G tn s G' tn'
Proof
  strip_tac >> qpat_x_assum `vv = _` SUBST_ALL_TAC >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `vv_post (storage_trace_horizon ee.storage_trace) ctx func cenv cx
    (TopLevelName ann nsid) es sa sm s0 ee tv (LocatedValue t p) s /\
   ghost_inv_at (DF (storage_trace_horizon ee.storage_trace)) lo ret cenv cx ee G tn s` by metis_tac[] >>
  drule_all exprPtrUnwrapCodeTheory.vv_post_code_source >> strip_tac >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee s` by fs[vv_post_def] >>
  `type_memory_bytes cenv t = type_memory_size rty /\ type_memory_size rty < 2**64` by metis_tac[] >>
  `evaluate_type (get_tenv cx) t = SOME rty` by metis_tac[] >>
  `t = expr_type (TopLevelName ann nsid)` by fs[post_value_type_def] >>
  `w2n a + type_memory_size rty <= lo /\
   (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rty v (w2n a) mem)` by
    (fs[contextTheory.vv_location_def, contextTheory.vv_operand_def] >> metis_tac[]) >>
  `compile_ensure_in_memory p.ptr_operand LocCode (type_memory_bytes cenv t)
    ((type_memory_bytes cenv t+31) DIV 32) T cenv.ce_imm_alloca sb = (op,sc)` by
    gvs[unwrap_value_def] >>
  suspend "layout"
QED

Resume toplevel_code_ctor_force_full[layout]:
  `?buf mid. compile_alloc_buffer (type_memory_bytes cenv t) sb = (buf,mid) /\
    op = buf.buf_operand /\
    compile_imm_copy_to_memory T cenv.ce_imm_alloca p.ptr_operand buf.buf_operand
      ((type_memory_bytes cenv t+31) DIV 32) 0 mid = ((),sc)` by
    (qpat_x_assum `compile_ensure_in_memory _ _ _ _ _ _ _ = _` mp_tac >>
     simp[exprPtrUnwrapCodeEdgesTheory.ensure_code_copy_route, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
     pairarg_tac >> gvs[] >> pairarg_tac >> gvs[]) >>
  `cs_extends sb mid /\ cs_extends mid sc` by
    metis_tac[compile_alloc_buffer_extends, ci_mono_compile_imm_copy_to_memory, ci_mono_def, SND] >>
  `fn_has_code sb mid func /\ fn_has_code mid sc func` by metis_tac[fn_has_code_split] >>
  `mid.cs_next_id <= sc.cs_next_id` by
    metis_tac[ci_mono_compile_imm_copy_to_memory, ci_mono_def, SND] >>
  `((type_memory_bytes cenv t+31) DIV 32) = type_slot_size rty` by
    simp[type_memory_size_slots, arithmeticTheory.ADD_DIV_ADD_DIV] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sb x` by
    (fs[contextTheory.vv_operand_def, loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
  `op_taint tn p.ptr_operand = {} /\ op_prov G p.ptr_operand = NONE` by fs[ptr_vv_ok_def] >>
  `type_memory_bytes cenv t < dimword(:256) /\
   32*type_slot_size rty <= type_memory_bytes cenv t /\ w2n a+32*type_slot_size rty <= lo` by
    (fs[type_memory_size_slots, wordsTheory.dimword_def] >> decide_tac) >>
  `!region. cenv.ce_imm_alloca = SOME region ==> eval_operand region s = SOME 0w /\
    copy_old_operand sb region /\
    (type_slot_size rty <> 0 ==> op_taint tn region = {} /\ op_prov G region = NONE)` by
    (rpt gen_tac >> disch_tac >> suspend "region") >>
  suspend "execute"
QED

Resume toplevel_code_ctor_force_full[region]:
  `eval_operand region s = SOME 0w` by
    fs[stmt_state_rel_def, expr_sim_inv_def, immutable_base_zero_def] >>
  `copy_old_operand sb region` by
    (Cases_on `region` >> simp[copy_old_operand_def] >>
     fs[local_ptrs_reserved_def, not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  simp[] >> strip_tac >>
  `lo <> 0` by decide_tac >>
  Cases_on `region` >> fs[op_taint_def, op_prov_def, eval_operand_def, ghost_inv_at_def]
QED

Resume toplevel_code_ctor_force_full[execute]:
  `compile_expr cenv ty (TopLevelName ann nsid) sb = (LocatedValue t p,sb)` by
    metis_tac[toplevel_located_compile_at] >>
  `compile_imm_copy_to_memory T cenv.ce_imm_alloca p.ptr_operand buf.buf_operand
     (type_slot_size rty) 0 mid = ((),sc)` by metis_tac[] >>
  drule_all toplevel_code_ctor_execution_full >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  suspend "allocation_posts"
QED

Resume toplevel_code_ctor_force_full[allocation_posts]:
  markerLib.RESUME_TAC >>
  drule_all bodyFullToplevelCodeWitnessPostsTheory.toplevel_code_runtime_witness_allocation >> strip_tac >>
  `buffer_allocation_base s sb.cs_next_id < dimword(:256)` by
    (drule_all exprPtrUnwrapAllocSeparationTheory.unwrap_alloc_site_bound >> decide_tac) >>
  `lo <= w2n d` by
    (simp[] >> Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >>
     fs[bufferAllocationExecutionTheory.buffer_allocation_base_def, allocas_from_def] >>
     PairCases_on `x` >> fs[] >> metis_tac[]) >>
  `regions_disjoint (w2n a) (type_memory_size rty) (w2n d) (type_memory_size rty)` by
    (simp[loweringStateRelDefsTheory.regions_disjoint_def] >> gvs[]) >>
  drule_all allocated_copy_operands_old >> strip_tac >>
  `copy_old_operand mid buf.buf_operand /\ eval_operand buf.buf_operand a' = SOME d` by
    simp[copy_old_operand_def, eval_operand_def, lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  `eval_operand p.ptr_operand a' = SOME a` by
    (`!x. p.ptr_operand = Var x ==> x <> root` by
       metis_tac[exprPtrUnwrapAllocEntryTheory.unwrap_alloc_old_operand_distinct] >>
     drule_all exprPtrUnwrapAllocEntryTheory.unwrap_alloc_old_operand_ghost >>
     disch_then (qspecl_then [`tn`,`SUC s.vs_inst_idx`,`PG`,`G`] mp_tac) >>
     asm_rewrite_tac[] >> strip_tac >>
     Cases_on `p.ptr_operand` >> gvs[eval_operand_def, lookup_var_def]) >>
  suspend "copy_posts"
QED

Resume toplevel_code_ctor_force_full[copy_posts]:
  `local_ptrs_reserved cenv sb` by metis_tac[local_ptrs_reserved_next_var] >>
  drule_all abiEncodeMaterializeExecTheory.materialize_alloc_run >> strip_tac >>
  drule exprPtrUnwrapAllocationTheory.unwrap_alloc_generated_code >> strip_tac >>
  `out = root` by (qpat_assum `buf.buf_operand = Var root` mp_tac >> simp[]) >> qpat_x_assum `out = root` SUBST_ALL_TAC >>
  `u' = u` by gvs[run_inst_seq_def] >> qpat_x_assum `u' = u` SUBST_ALL_TAC >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee a'` by
    (qpat_assum `a' = u with vs_inst_idx := SUC s.vs_inst_idx` (fn th => pure_rewrite_tac[th]) >>
     pure_rewrite_tac[stmt_state_rel_inst_idx] >> metis_tac[]) >>
  `!region. cenv.ce_imm_alloca = SOME region ==> eval_operand region a' = SOME 0w /\
    copy_old_operand mid region` by
    (rpt strip_tac >>
     `copy_old_operand sb region /\ eval_operand region s = SOME 0w` by metis_tac[] >>
     `copy_old_operand mid region` by
       (irule copy_old_operand_mono >> qexists `sb` >> simp[] >>
        metis_tac[compile_alloc_buffer_extends, ci_mono_compile_alloc_buffer, ci_mono_def, SND]) >>
     `region <> Var root` by
       (Cases_on `region` >> fs[copy_old_operand_def, not_fresh_at_def] >>
        qpat_x_assum `!n. sb.cs_next_var <= n ==> _` (qspec_then `sb.cs_next_var` mp_tac) >>
        gvs[]) >>
     Cases_on `region` >> gvs[eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, bufferAllocationExecutionTheory.buffer_allocation_fields_def] >>
     Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >> gvs[]) >>
  `immutable_holds cenv cx t (Value v) a ee a'` by
    metis_tac[immutable_holds_memory_cong] >>
  `w2n d + type_memory_size rty < dimword(:256)` by metis_tac[] >>
  drule_all bodyFullToplevelCodeCtorPostsTheory.toplevel_code_ctor_contents >> strip_tac >>
  `32 * type_slot_size rty = type_memory_size rty` by simp[type_memory_size_slots] >>
  `!j. j IN tnf.t_mem <=>
    if w2n d <= j /\ j < w2n d + type_memory_size rty
    then w2n a + (j-w2n d) IN tm.t_mem else j IN tm.t_mem` by metis_tac[] >>
  `type_memory_size rty <= type_memory_bytes cenv t` by simp[] >>
  drule_all bodyFullToplevelCodeCtorPostsTheory.toplevel_code_ctor_exterior >> strip_tac >>
  suspend "family"
QED

Resume toplevel_code_ctor_force_full[family]:
  `eval_operand buf.buf_operand z = SOME d` by
    (Cases_on `buf.buf_operand` >> fs[copy_old_operand_def, eval_operand_def,
      copy_runtime_frame_def] >> metis_tac[]) >>
  `z.vs_alloca_next = a'.vs_alloca_next` by
    (qpat_assum `copy_runtime_frame mid a' sc z` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[copy_runtime_frame_def, exprSimStorageCopyTheory.copy_static_def,
       venom_state_component_equality]) >>
  `w2n d + type_memory_bytes cenv t <= z.vs_alloca_next` by metis_tac[] >>
  `op = Var root` by metis_tac[] >>
  `tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm` by
    fs[step_taint_def, adopt_reset_def, store_taint_def, imm_taint_def,
      venomInstTheory.mk_inst_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx (TopLevelName ann nsid) es sa sb s0 ee tv (LocatedValue t p) s` by
    (rpt strip_tac >> irule bodyFullToplevelSlotSinglePostTheory.toplevel_slot_single_cursor_frame >>
     qexists `sm` >> metis_tac[]) >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by decide_tac >>
  suspend "join"
QED

Resume toplevel_code_ctor_force_full[join]:
  `!j. j IN tnf.t_mem <=>
    if w2n d <= j /\ j < w2n d + type_memory_bytes cenv t
    then w2n a + (j-w2n d) IN tm.t_mem else j IN tm.t_mem` by metis_tac[] >>
  `regions_disjoint (w2n a) (type_memory_bytes cenv t) (w2n d) (type_memory_bytes cenv t)` by metis_tac[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post H ctx func cenv cx (TopLevelName ann nsid) es sa sc s0 ee v op z /\
    vv_at cenv cx (post_value_type cenv (TopLevelName ann nsid)) sa sc ee tv
      (LocatedValue (post_value_type cenv (TopLevelName ann nsid)) (mk_ptr op LocMemory)) z /\
    expr_store_bound cx (expr_type (TopLevelName ann nsid)) v op z /\
    ptr_val_ok cx (post_value_type cenv (TopLevelName ann nsid)) v op Gf tnf z /\
    ptr_buf_ok cenv (TopLevelName ann nsid) op Gf z /\
    (!rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv (TopLevelName ann nsid)) = SOME rt /\
      eval_operand op z = SOME w ==> type_memory_size rt = 0 \/
      w2n w + type_memory_size rt <= z.vs_alloca_next)` by
    (gen_tac >> disch_tac >>
     `vv_post H ctx func cenv cx (TopLevelName ann nsid) es sa sb s0 ee tv (LocatedValue t p) s` by metis_tac[] >>
     `stmt_state_rel H ctx func cenv cx ee a'` by
       (`stmt_state_rel H ctx func cenv cx ee s` by fs[vv_post_def] >>
        qpat_x_assum `stmt_state_rel _ _ _ _ _ ee a'` kall_tac >>
        qpat_x_assum `stmt_state_rel _ _ _ _ _ ee u` kall_tac >>
        qpat_x_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ s` kall_tac >>
        drule_all abiEncodeMaterializeExecTheory.materialize_alloc_run >> strip_tac >>
        `u' = u` by gvs[run_inst_seq_def] >> qpat_x_assum `u' = u` SUBST_ALL_TAC >>
        qpat_assum `a' = u with vs_inst_idx := SUC s.vs_inst_idx` (fn th => pure_rewrite_tac[th]) >>
        pure_rewrite_tac[stmt_state_rel_inst_idx] >> metis_tac[]) >>
     irule toplevel_code_ctor_value_posts >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- metis_tac[]) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `vv_post H _ _ _ _ _ _ _ sb _ _ _ _ s` (irule_at Any) >>
     qpat_assum `compile_alloc_buffer _ sb = _` (irule_at Any) >>
     qpat_assum `copy_runtime_frame mid a' sc z` (irule_at Any) >>
     qpat_assum `step_inst_base _ s = OK u` (irule_at Any) >>
     qpat_assum `tm = step_taint _ s u tn` (irule_at Any) >>
     qpat_assum `compile_imm_copy_to_memory T _ _ _ (type_slot_size rty) 0 mid = _` (irule_at Any) >>
     qexistsl [`a`, `lo`, `SUC s.vs_inst_idx`, `d`] >>
     simp[] >> gvs[]) >>
  suspend "frame"
QED

Resume toplevel_code_ctor_force_full[frame]:
  `!off len. off+len <= buffer_allocation_base s sb.cs_next_id \/
    buffer_allocation_base s sb.cs_next_id + type_memory_bytes cenv t <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory` by
    (qpat_assum `!off len. off+len <= w2n d \/ w2n d + type_memory_bytes cenv t <= off ==> _` mp_tac >>
     qpat_assum `d = n2w _` mp_tac >>
     qpat_assum `buffer_allocation_base s sb.cs_next_id < dimword (:256)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `!j. j < buffer_allocation_base s sb.cs_next_id \/
    buffer_allocation_base s sb.cs_next_id + type_memory_bytes cenv t <= j ==>
    (j IN tnf.t_mem <=> j IN tn.t_mem)` by
    (qpat_assum `!j. j < w2n d \/ w2n d + type_memory_bytes cenv t <= j ==> _` mp_tac >>
     qpat_assum `d = n2w _` mp_tac >>
     qpat_assum `buffer_allocation_base s sb.cs_next_id < dimword (:256)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    ghost_inv_at (DF H) lo ret cenv cx ee Gf tnf (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
    alloca_history func (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
    s.vs_alloca_next <= z.vs_alloca_next /\ s0.vs_alloca_next <= z.vs_alloca_next /\
    (!x. not_fresh_at sb x ==>
      lookup_var x (z with vs_inst_idx := LENGTH sc.cs_current_insts) = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv ee ee sb s (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
    ghost_kept_at lo cenv es sa Gi ti s0 Gf tnf /\
    ghost_kept_at lo cenv ee sb G tn s Gf tnf` by
    (gen_tac >> disch_tac >>
     `vv_post H ctx func cenv cx (TopLevelName ann nsid) es sa sb s0 ee tv (LocatedValue t p) s` by metis_tac[] >>
     `ghost_inv_at (DF H) lo ret cenv cx ee G tn s` by metis_tac[] >>
     irule (INST_TYPE [``:'a`` |-> ``:256``] toplevel_code_ctor_frame_posts) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >-
     (qpat_assum `compile_alloc_buffer _ sb = _` (irule_at Any) >>
     qpat_assum `copy_runtime_frame mid a' sc z` (irule_at Any) >>
     qpat_assum `Gm = step_prov _ _ _ u` (irule_at Any) >>
     qpat_assum `tm = step_taint _ s u tn` (irule_at Any) >>
     qpat_assum `compile_imm_copy_to_memory T _ _ _ (type_slot_size rty) 0 mid = _` (irule_at Any) >>
     qexists `d` >>
     rpt (qpat_x_assum `!j. j IN tnf.t_mem <=> _` kall_tac) >>
     simp[] >> rpt conj_tac
     >- (qpat_assum `!off len. off+len <= buffer_allocation_base s sb.cs_next_id \/ _ ==> _` mp_tac >>
         qpat_assum `type_memory_bytes cenv t = type_memory_size rty` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[arithmeticTheory.ADD_COMM])
     >- (qpat_assum `!j. j < buffer_allocation_base s sb.cs_next_id \/ _ ==> _` mp_tac >>
         qpat_assum `type_memory_bytes cenv t = type_memory_size rty` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[arithmeticTheory.ADD_COMM]) >> gvs[])) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl [`H`, `ann`, `ctx`, `nsid`] >>
     qpat_assum `vv_post H _ _ _ _ _ _ _ sb _ _ _ _ s` (irule_at Any) >>
     qpat_assum `compile_expr _ _ _ sa = _` (irule_at Any) >> simp[]) >>
  suspend "normalize"
QED

Resume toplevel_code_ctor_force_full[normalize]:
  qexistsl [`v`, `z with vs_inst_idx := LENGTH sc.cs_current_insts`, `Gf`, `tnf`] >>
  `expr_post (storage_trace_horizon ee.storage_trace) ctx func cenv cx (TopLevelName ann nsid) es sa sc s0 ee v op z /\
    vv_at cenv cx (post_value_type cenv (TopLevelName ann nsid)) sa sc ee tv
      (LocatedValue (post_value_type cenv (TopLevelName ann nsid)) (mk_ptr op LocMemory)) z /\
    expr_store_bound cx (expr_type (TopLevelName ann nsid)) v op z /\
    ptr_val_ok cx (post_value_type cenv (TopLevelName ann nsid)) v op Gf tnf z /\
    ptr_buf_ok cenv (TopLevelName ann nsid) op Gf z /\
    (!rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv (TopLevelName ann nsid)) = SOME rt /\
      eval_operand op z = SOME w ==> type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next)` by metis_tac[] >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> ghost_inv_at _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _` mp_tac >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> ghost_inv_at _ _ _ _ _ _ _ _ _ /\ _` mp_tac >>
  qpat_assum `expr_post (storage_trace_horizon _) _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  qpat_assum `vv_at _ _ _ _ _ _ _ _ z` mp_tac >>
  qpat_assum `expr_store_bound _ _ _ _ z` mp_tac >>
  qpat_assum `ptr_val_ok _ _ _ _ _ _ z` mp_tac >>
  qpat_assum `ptr_buf_ok _ _ _ _ z` mp_tac >>
  qpat_assum `!rt w. evaluate_type _ _ = SOME rt /\ eval_operand op z = SOME w ==> _` mp_tac >>
  qpat_assum `read_result cx tv ee = (INL v,ee)` mp_tac >>
  qpat_assum `!D. gas_origin_ptr_path _ _ _ _` mp_tac >>
  qpat_assum `z.vs_current_bb = sc.cs_current_bb` mp_tac >>
  qpat_assum `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[vv_at_def, exprSimMemDefsTheory.expr_store_bound_def, ptr_val_ok_def, ptr_mem_ok_def,
       ptr_buf_ok_def, lookup_var_def, local_region_def] >> metis_tac[]
QED

Finalise toplevel_code_ctor_force_full
