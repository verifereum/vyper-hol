(* Same-endpoint constructor aggregate contents; no operational witnesses are chosen here. *)
Theory bodyFullToplevelCodeCtorPosts
Ancestors
  exprSimCopy exprSimMemUnwrap robustCopyTransportPtr bodyFullToplevelCodePosts
  bodyFullToplevelCodeWitnessPosts valueEncodingProps valueEncodingDefs exprSimMemorySource
  exprLowering compileEnv venomMemDefs venomState words arithmetic list
  exprSimAlloc exprPtrUnwrapAllocationFrame exprPtrUnwrapAllocation
  loweringStateRelDefs exprPtrUnwrapAllocSeparation bodyPtrDefs allocationPtr
  ptrDiscipline immutableCopyExecution bodyFullUnwrapSlotPost
  exprLoweringProps exprPtrUnwrapRetained bufferAllocationExecution exprSimStorageCopy
  abiEncodeMaterializeExec exprSimProps loweringPosts

Theorem toplevel_code_ctor_contents:
  compile_expr cenv ty (TopLevelName ann nsid) sx = (vv,sm) /\
  compile_imm_copy_to_memory T imm src dst (type_slot_size rt) 0 mid = ((),sb) /\
  copy_old_operand mid src /\ copy_old_operand mid dst /\
  eval_operand src a = SOME p /\ eval_operand dst a = SOME w /\
  (!region. imm = SOME region ==> eval_operand region a = SOME 0w /\
    copy_old_operand mid region) /\
  copy_runtime_frame mid a sb z /\
  stmt_state_rel H ctx func cenv cx ee a /\ cenv.ce_is_ctor /\
  immutable_holds cenv cx t (Value v) p ee a /\
  evaluate_type (get_tenv cx) t = SOME rt /\
  w2n w + type_memory_size rt < dimword(:256) /\
  regions_disjoint (w2n p) (type_memory_size rt) (w2n w) (type_memory_size rt) ==>
  val_wf rt v /\ val_in_memory rt v (w2n w) z.vs_memory /\
  val_footprint rt v <= type_memory_size rt /\
  LENGTH a.vs_memory <= LENGTH z.vs_memory /\
  (!off len. off+len <= w2n w \/ w2n w+type_memory_size rt <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len a.vs_memory) /\
  mem_bytes_at (w2n w) (type_memory_size rt) z.vs_memory =
    mem_bytes_at (w2n p) (type_memory_size rt) a.vs_memory
Proof
  strip_tac >> drule_all copy_ctor_run >> strip_tac >>
  `zz = z` by fs[copy_runtime_frame_def] >>
  qpat_x_assum `zz = z` SUBST_ALL_TAC >>
  drule_all copy_ctor_contents >> strip_tac >>
  reverse (rpt conj_tac)
  >- (Cases_on `type_slot_size rt = 0`
      >- gvs[type_memory_size_slots, mem_bytes_at_def] >>
      `w2n p + type_memory_size rt < dimword(:256)` by
        metis_tac[immutable_holds_bounds] >>
      drule_all copy_ctor_memory_snapshot >> disch_tac >>
      asm_rewrite_tac[] >>
      qspecl_then [`w2n w`, `mem_bytes_at (w2n p) (type_memory_size rt) a.vs_memory`, `a`]
        mp_tac write_memory_mem_bytes_at_same >> simp[]) >>
  metis_tac[]
QED

(* Allocation can clear the destination, but not the source below lo. *)
Theorem toplevel_code_ctor_robust:
  compile_expr cenv ty (TopLevelName ann nsid) sx = (vv,sm0) /\
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  buf.buf_operand = Var root /\
  stmt_state_rel H ctx func cenv cx ee s /\ nb < dimword(:256) /\
  step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  tm = step_taint (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
  (d:bytes32) = n2w (buffer_allocation_base s sm.cs_next_id) /\
  buffer_allocation_base s sm.cs_next_id < dimword(:256) /\
  w2n p+type_memory_size rt <= lo /\ lo <= w2n d /\
  a.vs_memory = s.vs_memory /\
  mem_bytes_at (w2n d) (type_memory_size rt) z.vs_memory =
    mem_bytes_at (w2n p) (type_memory_size rt) a.vs_memory /\
  (!j. j IN tf.t_mem <=>
    if w2n d <= j /\ j < w2n d+type_memory_size rt
    then w2n p+(j-w2n d) IN tm.t_mem else j IN tm.t_mem) /\
  val_wf rt v /\ val_footprint rt v <= type_memory_size rt /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory rt v (w2n p) mem) ==>
  !mem. mem_agree_outside tf.t_mem z.vs_memory mem ==>
    val_in_memory rt v (w2n d) mem
Proof
  strip_tac >> drule unwrap_alloc_generated_code >> strip_tac >>
  `root = out` by gvs[] >> qpat_x_assum `root = out` SUBST_ALL_TAC >>
  drule_all buffer_alloc_code >> strip_tac >>
  qpat_x_assum `out = STRING _ _` SUBST_ALL_TAC >>
  drule_all unwrap_alloc_taint_frame >>
  disch_then (qspec_then `tn` strip_assume_tac) >>
  `w2n d = buffer_allocation_base s sm.cs_next_id` by simp[] >>
  `!i. i < type_memory_size rt ==>
    (w2n d+i IN tf.t_mem <=> w2n p+i IN tn.t_mem)` by
    (rpt strip_tac >>
     `w2n p+i < buffer_allocation_base s sm.cs_next_id /\
      w2n d <= w2n d+i /\ w2n d+i < w2n d+type_memory_size rt /\
      w2n d+i-w2n d = i` by decide_tac >>
     metis_tac[]) >>
  rpt strip_tac >> irule robust_val_in_memory_copy_transport >> simp[] >>
  qexistsl [`s.vs_memory`, `z.vs_memory`, `type_memory_size rt`, `w2n p`, `tn.t_mem`, `tf.t_mem`] >>
  simp[ADD_COMM] >> metis_tac[]
QED

Theorem toplevel_code_ctor_exterior:
  compile_expr cenv ty (TopLevelName ann nsid) sx = (vv,sm0) /\
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  stmt_state_rel H ctx func cenv cx ee s /\ nb < dimword(:256) /\
  buf.buf_operand = Var root /\
  step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  tm = step_taint (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
  (d:bytes32) = n2w (buffer_allocation_base s sm.cs_next_id) /\
  buffer_allocation_base s sm.cs_next_id < dimword(:256) /\
  sz <= nb /\ a.vs_memory = s.vs_memory /\
  (!off len. off+len <= w2n d \/ w2n d+sz <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len a.vs_memory) /\
  (!j. j IN tf.t_mem <=>
    if w2n d <= j /\ j < w2n d+sz
    then src+(j-w2n d) IN tm.t_mem else j IN tm.t_mem) ==>
  (!j. j < w2n d \/ w2n d+nb <= j ==> (j IN tf.t_mem <=> j IN tn.t_mem)) /\
  (!off len. off+len <= w2n d \/ w2n d+nb <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory)
Proof
  strip_tac >> drule unwrap_alloc_generated_code >> strip_tac >>
  `root = out` by gvs[] >> qpat_x_assum `root = out` SUBST_ALL_TAC >>
  drule_all buffer_alloc_code >> strip_tac >>
  qpat_x_assum `out = STRING _ _` SUBST_ALL_TAC >>
  drule_all unwrap_alloc_taint_frame >>
  disch_then (qspec_then `tn` strip_assume_tac) >>
  `w2n d = buffer_allocation_base s sm.cs_next_id` by simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `~(w2n d <= j /\ j < w2n d+sz)` by decide_tac >>
      `j < buffer_allocation_base s sm.cs_next_id \/
       buffer_allocation_base s sm.cs_next_id+nb <= j` by decide_tac >>
      metis_tac[]) >>
  rpt strip_tac >>
  `off+len <= w2n d \/ w2n d+sz <= off` by decide_tac >> metis_tac[]
QED

Theorem toplevel_code_ctor_ghost:
  compile_expr cenv ty (TopLevelName ann nsid) sx = (vv,sm0) /\
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  stmt_state_rel H ctx func cenv cx ee s /\
  ghost_inv_at D lo ret cenv cx ee G tn s /\ local_ptrs_reserved cenv sa /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sm /\ nb < dimword(:256) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  sa.cs_next_var <= sm.cs_next_var /\
  (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  (d:bytes32) = n2w (buffer_allocation_base s sm.cs_next_id) /\
  buffer_allocation_base s sm.cs_next_id < dimword(:256) /\
  (!off len. off+len <= w2n d \/ w2n d+nb <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
  (!j. j < w2n d \/ w2n d+nb <= j ==> (j IN tf.t_mem <=> j IN tn.t_mem)) /\
  a.vs_accounts = s.vs_accounts /\ a.vs_transient = s.vs_transient /\
  a.vs_call_ctx = s.vs_call_ctx /\ a.vs_immutables = s.vs_immutables /\
  copy_runtime_frame mid a sb z /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  allocas_from lo z /\ s.vs_alloca_next <= z.vs_alloca_next ==>
  ghost_inv_at D lo ret cenv cx ee Gf tf z
Proof
  strip_tac >>
  `local_ptrs_rel func cenv ee.scopes s` by fs[stmt_state_rel_def, state_rel_def] >>
  `!name off len. local_region cenv ee.scopes s name off len ==>
    w2n d+nb <= off \/ off+len <= w2n d` by
    (rpt strip_tac >> drule_all unwrap_alloc_local_separation >> simp[]) >>
  `lo <= w2n d` by
    (gvs[ghost_inv_at_def, buffer_allocation_base_def] >>
     Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id` >>
     gvs[allocas_from_def] >> PairCases_on `x` >> gvs[] >> metis_tac[]) >>
  `stor_taint_ok_at D tf z` by
    (fs[ghost_inv_at_def, stor_taint_ok_at_def, copy_runtime_frame_def] >>
     qpat_x_assum `copy_static z = copy_static a`
       (mp_tac o Q.AP_TERM `\st. (st.vs_accounts,st.vs_transient,st.vs_call_ctx,st.vs_immutables)`) >>
     simp[copy_static_def] >> gvs[]) >>
  qpat_x_assum `d = _` kall_tac >>
  irule unwrap_slot_copy_ghost_inv_at >>
  simp[] >> (conj_tac >- (fs[ghost_inv_at_def] >> decide_tac)) >>
  goal_assum (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
  qexistsl [`nb`, `sa`, `w2n d`] >> asm_rewrite_tac[] >>
  `nb+w2n d = w2n d+nb` by decide_tac >> asm_rewrite_tac[]
QED

Theorem toplevel_code_ctor_semantic:
  compile_expr cenv ty (TopLevelName ann nsid) sx = (vv,sm0) /\
  vv_post H ctx func cenv cx (TopLevelName ann nsid) es sa sm s0 ee
    (Value v) (LocatedValue t p) s /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  fn_inst_ids_distinct func /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  mid.cs_next_id <= sb.cs_next_id /\
  compile_alloc_buffer (type_memory_bytes cenv t) sm = (buf,mid) /\
  fn_has_code sm mid func /\ type_memory_bytes cenv t < dimword(:256) /\
  buf.buf_operand = Var root /\
  step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv t))] [root]) s = OK u /\
  a = u with vs_inst_idx := k /\ eval_operand buf.buf_operand a = SOME d /\
  compile_imm_copy_to_memory T imm src buf.buf_operand (type_slot_size rt) 0 mid = ((),sb) /\
  copy_old_operand mid src /\ copy_old_operand mid buf.buf_operand /\
  eval_operand src a = SOME q /\
  (!region. imm = SOME region ==> eval_operand region a = SOME 0w /\
    copy_old_operand mid region) /\
  copy_runtime_frame mid a sb z /\ cenv.ce_is_ctor /\
  immutable_holds cenv cx t (Value v) q ee s /\
  evaluate_type (get_tenv cx) t = SOME rt /\
  type_memory_bytes cenv t = type_memory_size rt /\
  t = expr_type (TopLevelName ann nsid) /\ ~is_word_type t /\
  regions_disjoint (w2n q) (type_memory_size rt) (w2n d) (type_memory_size rt) /\
  eval_operand buf.buf_operand z = SOME d ==>
  expr_post H ctx func cenv cx (TopLevelName ann nsid) es sa sb s0 ee v buf.buf_operand z
Proof
  strip_tac >>
  `stmt_state_rel H ctx func cenv cx ee s` by fs[vv_post_def] >>
  drule_all materialize_alloc_run >> strip_tac >>
  drule unwrap_alloc_generated_code >> strip_tac >>
  `root = out` by gvs[] >> qpat_x_assum `root = out` SUBST_ALL_TAC >>
  `u' = u` by gvs[run_inst_seq_def] >> qpat_x_assum `u' = u` SUBST_ALL_TAC >>
  `w = d` by gvs[eval_operand_def, lookup_var_def] >> qpat_x_assum `w = d` SUBST_ALL_TAC >>
  `stmt_state_rel H ctx func cenv cx ee a /\ a.vs_memory = s.vs_memory` by
    simp[stmt_state_rel_inst_idx] >>
  `immutable_holds cenv cx t (Value v) q ee a` by
    metis_tac[immutable_holds_memory_cong] >>
  `w2n d + type_memory_size rt < dimword(:256)` by metis_tac[] >>
  drule_all toplevel_code_ctor_contents >> strip_tac >>
  `copy_static z = copy_static u /\
   !x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u` by
    gvs[copy_runtime_frame_def, copy_static_def, lookup_var_def] >>
  irule buffer_post_transport >>
  simp[] >> qexistsl [`mid`, `p`, `s`, `sm`, `rt`, `u`] >>
  gvs[] >> simp[ADD_COMM] >>
  drule loweringHaltTheory.compile_alloc_buffer_parts >> strip_tac >>
  gvs[] >> rpt conj_tac >> metis_tac[]
QED
