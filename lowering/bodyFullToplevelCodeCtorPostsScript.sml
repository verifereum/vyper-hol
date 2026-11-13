(* Same-endpoint constructor aggregate contents; no operational witnesses are chosen here. *)
Theory bodyFullToplevelCodeCtorPosts
Ancestors
  exprSimCopy exprSimMemUnwrap robustCopyTransportPtr bodyFullToplevelCodePosts
  bodyFullToplevelCodeWitnessPosts valueEncodingProps valueEncodingDefs exprSimMemorySource
  exprLowering compileEnv venomMemDefs venomState words arithmetic list
  exprSimAlloc exprPtrUnwrapAllocationFrame exprPtrUnwrapAllocation

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
