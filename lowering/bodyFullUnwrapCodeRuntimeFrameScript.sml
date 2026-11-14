Theory bodyFullUnwrapCodeRuntimeFrame
Ancestors
  exprPtrCodeCopyEndpoint bodyFullUnwrapSlotPost bodyFullUnwrapRun
  freshWrites exprPtrUnwrapAllocSemantic exprPtrUnwrapAllocation
  exprPtrUnwrapAllocSeparation
  exprPtrUnwrapRetained exprPtrUnwrapAllocationFrame exprSimStorageCopy
  bodyPtrDefs loweringStateRelDefs loweringPosts exprSimAlloc
  ptrDiscipline allocationPtr compileEnv finite_map arithmetic words
  venomState venomInst exprSimCopy exprSimProps exprLoweringProps


Theorem runtime_code_copy_ghost_inv_at:
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  stmt_state_rel H ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  ghost_inv_at D lo ret cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  buf.buf_operand = Var root /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= mid.cs_next_var /\
  step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := k /\
  G0 = step_prov PG G (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
  tn0 = step_taint (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
  (d:bytes32) = n2w (buffer_allocation_base s sm.cs_next_id) /\
  buffer_allocation_base s sm.cs_next_id < dimword (:256) /\
  nb < dimword (:256) /\ 32*n <= nb /\ a.vs_memory = s.vs_memory /\
  a.vs_accounts = s.vs_accounts /\ a.vs_transient = s.vs_transient /\
  a.vs_call_ctx = s.vs_call_ctx /\ a.vs_immutables = s.vs_immutables /\
  copy_runtime_frame mid a sb z /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  (!x. not_fresh_at mid x ==>
    FLOOKUP HG x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
  (!off len. off+len <= w2n d \/ w2n d+32*n <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len a.vs_memory) /\
  tf.t_mem = tn0.t_mem DIFF {j | w2n d <= j /\ j < w2n d+32*n} /\
  lo <= w2n d /\ allocas_from lo z /\ lo <= z.vs_alloca_next ==>
  ghost_inv_at D lo ret cenv cx es HG tf
    (z with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==>
    lookup_var x z = lookup_var x s /\ FLOOKUP HG x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >> irule unwrap_code_old_variable_frames >>
     goal_assum (drule_at (Pat `copy_runtime_frame _ _ _ _`)) >>
     goal_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
     qexistsl [`G0`, `PG`, `k`, `root`, `sa`, `tn0`, `u`] >> asm_rewrite_tac[]) >>
  drule_all unwrap_code_exterior_frames >> strip_tac >>
  `local_ptrs_rel func cenv es.scopes s` by fs[stmt_state_rel_def, state_rel_def] >>
  `!name off len. local_region cenv es.scopes s name off len ==>
    w2n d+nb <= off \/ off+len <= w2n d` by
    (rpt strip_tac >> drule_all unwrap_alloc_local_separation >> simp[]) >>
  `z.vs_accounts = s.vs_accounts /\ z.vs_transient = s.vs_transient /\
   z.vs_call_ctx = s.vs_call_ctx /\ z.vs_immutables = s.vs_immutables` by
    (fs[copy_runtime_frame_def] >>
     qpat_x_assum `copy_static z = copy_static a`
       (mp_tac o Q.AP_TERM `\st. (st.vs_accounts,st.vs_transient,st.vs_call_ctx,st.vs_immutables)`) >>
     gvs[copy_static_def]) >>
  `stor_taint_ok_at D tf z` by
    fs[stor_taint_ok_at_def, ghost_inv_at_def] >>
  `ghost_inv_at D lo ret cenv cx es HG tf z` by
    (irule unwrap_slot_copy_ghost_inv_at >>
     asm_rewrite_tac[] >>
     qexistsl [`G`, `func`, `nb`, `s`, `sa`, `w2n d`, `tn`] >>
     metis_tac[]) >>
  qpat_x_assum `ghost_inv_at D lo ret cenv cx es HG tf z` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  Cases_on `ret` >-
    (simp[ghost_inv_at_def, return_buf_ptr_def, ptr_covers_def,
       lookup_var_def, stor_taint_ok_at_def, allocas_from_def] >> metis_tac[]) >>
  rename1 `SOME rp` >> PairCases_on `rp` >>
  simp[ghost_inv_at_def, return_buf_ptr_def, ptr_covers_def,
    lookup_var_def, stor_taint_ok_at_def, allocas_from_def] >> metis_tac[]
QED

Theorem runtime_code_copy_retained_frames:
  compile_alloc_buffer nb sb = (buf,mid) /\ fn_has_code sb mid func /\
  stmt_state_rel H ctx func cenv cx ee s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sb /\ nb < dimword (:256) /\
  buf.buf_operand = Var root /\
  u = update_var root d (buffer_allocation_fields s sb.cs_next_id nb) /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := k /\ copy_runtime_frame mid a sc z /\
  sa.cs_next_var <= sb.cs_next_var /\
  (!x. not_fresh_at sb x ==>
    lookup_var x z = lookup_var x s /\ FLOOKUP HG x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!off len. off+len <= w2n d \/ w2n d+nb <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
  tf.t_mem SUBSET tn.t_mem /\ ghost_kept_at lo cenv es sa Gi ti s0 G tn ==>
  ghost_kept_at lo cenv es sa Gi ti s0 HG tf /\
  wb_frame cenv ee ee sb s (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
  ghost_kept_at lo cenv ee sb G tn s HG tf
Proof
  strip_tac >>
  `ghost_kept_at lo cenv es sa Gi ti s0 HG tf` by
    (irule ghost_kept_at_clean_suffix >> qexistsl [`G`, `tn`] >>
     metis_tac[not_fresh_at_mono]) >>
  `ghost_kept_at lo cenv ee sb G tn s HG tf` by
    (fs[ghost_kept_at_def] >> metis_tac[pred_setTheory.SUBSET_DEF]) >>
  drule_all unwrap_alloc_semantic_frames >> strip_tac >>
  `z.vs_allocas = u.vs_allocas` by
    (fs[copy_runtime_frame_def] >> drule copy_static_fields >> simp[]) >>
  `!name b len. local_region cenv ee.scopes s name b len ==>
     b+len <= w2n d \/ w2n d+nb <= b` by
    (rpt strip_tac >> drule_all unwrap_alloc_local_separation >>
     `d = n2w (buffer_allocation_base s sb.cs_next_id)` by
       (drule unwrap_alloc_generated_step >> strip_tac >> gvs[update_var_def] >>
        qpat_x_assum `_ with vs_vars := _ = _`
          (mp_tac o Q.AP_TERM `\st. FLOOKUP st.vs_vars root`) >>
        simp[FLOOKUP_UPDATE]) >>
     qpat_x_assum `stmt_state_rel _ _ _ _ _ _ u` kall_tac >>
     drule_all unwrap_alloc_site_bound >> strip_tac >>
     `buffer_allocation_base s sb.cs_next_id < dimword (:256)` by decide_tac >>
     asm_simp_tac (srw_ss()) [] >> metis_tac[]) >>
  `wb_frame cenv ee ee sb s z` by
    (irule unwrap_slot_copy_wb_frame >>
     conj_tac >- metis_tac[] >>
     reverse conj_tac >- metis_tac[] >>
     qexistsl [`nb`, `w2n d`] >>
     fs[regions_disjoint_def] >> metis_tac[]) >>
  simp[] >>
  qpat_x_assum `wb_frame cenv ee ee sb s z` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[wb_frame_def, lookup_var_def, locals_kept_def] >> metis_tac[]
QED
