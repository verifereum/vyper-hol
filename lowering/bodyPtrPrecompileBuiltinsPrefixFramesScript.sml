Theory bodyPtrPrecompileBuiltinsPrefixFrames
Ancestors bodyPtrPrecompileBuiltinsCompletePrefixes decoderGhostFramePtr
          fragGasSeqPtr ptrDiscipline bodyPtrDefs pred_set list
          venomExecSemantics venomState exprLoweringProps

(* The second store footprint may be empty (ECAdd and ECMul), or the
   recovery output-zero range.  Keep allocation growth explicit. *)
Theorem prefix_taint_bound:
  final = (((initial UNION alloc1) DIFF writes1) UNION alloc2) DIFF writes2 ==>
  final SUBSET (initial UNION alloc1 UNION alloc2)
Proof
  SET_TAC[]
QED

Theorem prefix_taint_exterior:
  final = (((initial UNION alloc1) DIFF writes1) UNION alloc2) DIFF writes2 /\
  i NOTIN (alloc1 UNION alloc2 UNION writes1 UNION writes2) ==>
  (i IN final <=> i IN initial)
Proof
  SET_TAC[]
QED

Theorem prefix_taint_below_frontier:
  final = (((initial UNION alloc1) DIFF writes1) UNION alloc2) DIFF writes2 /\
  (!j. j IN (alloc1 UNION alloc2 UNION writes1 UNION writes2) ==> frontier <= j) /\
  i < frontier ==>
  (i IN final <=> i IN initial)
Proof
  strip_tac >> irule prefix_taint_exterior >>
  qexistsl [`alloc1`, `alloc2`, `writes1`, `writes2`] >>
  metis_tac[IN_UNION, arithmeticTheory.NOT_LESS_EQUAL]
QED

Theorem inst_seq_ptr_nonmemory_frame:
  !code s G tn G' tn'.
    EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> SSTORE /\
      i.inst_opcode <> TSTORE /\ i.inst_opcode <> ISTORE) code /\
    inst_seq_ptr D lo ctx fn PG G tn code s G' tn' ==>
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  Induct >> simp[inst_seq_ptr_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[AllCaseEqs()] >>
  drule_all step_taint_nonmemory_frame >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem staging_step_runtime_fields:
  (inst.inst_opcode = ALLOCA \/ inst.inst_opcode = ADD \/
   inst.inst_opcode = MLOAD \/ inst.inst_opcode = MSTORE) /\
  step_inst_base inst s = OK t ==>
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient
Proof
  strip_tac >> gvs[] >> gvs[step_inst_base_def] >>
  gvs[exec_alloca_def, exec_pure2_def, exec_read1_def, exec_write2_def,
    AllCaseEqs()] >>
  gvs[update_var_def, mstore_def]
QED

Theorem staging_sequence_runtime_fields:
  EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
    i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE) code /\
  run_inst_seq code s = OK t ==>
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient
Proof
  strip_tac >>
  ` (t.vs_call_ctx,t.vs_accounts,t.vs_transient) =
    (s.vs_call_ctx,s.vs_accounts,s.vs_transient)` suffices_by simp[] >>
  irule (BETA_RULE (ISPEC ``\u:venom_state. (u.vs_call_ctx,u.vs_accounts,u.vs_transient)``
    run_inst_seq_preserves_field)) >> qexists_tac `code` >> simp[] >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  `i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
   i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE` by metis_tac[] >>
  metis_tac[staging_step_runtime_fields]
QED

Theorem staging_alloca_footprint_above_frontier:
  inst.inst_opcode = ALLOCA /\ step_inst_base inst s = OK t /\
  i IN new_site_bytes s t ==>
  s.vs_alloca_next <= i
Proof
  strip_tac >> gvs[step_inst_base_def] >>
  gvs[exec_alloca_def, AllCaseEqs()] >>
  gvs[new_site_bytes_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
      finite_mapTheory.FLOOKUP_DEF] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[]
QED

(* One application at a completed staging boundary supplies the remaining
   non-memory frame from its code restriction and linked runtime trace. *)
Theorem staging_prefix_nonmemory_frames:
  EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
    i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE) code /\
  run_inst_seq code s = OK t /\
  (!k. inst_seq_ptr D 0 ctx fn PG G tn code
    (s with vs_inst_idx := k) G' tn') ==>
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  strip_tac >> drule_all staging_sequence_runtime_fields >> strip_tac >>
  qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `s.vs_inst_idx` assume_tac) >> gvs[] >>
  `EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> SSTORE /\
    i.inst_opcode <> TSTORE /\ i.inst_opcode <> ISTORE) code` by
    (gvs[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >> gvs[]) >>
  drule_all inst_seq_ptr_nonmemory_frame >> simp[]
QED

Theorem complete_prefix_ghost_frame:
  ghost_inv d cenv cx es G tn s /\
  (!p sz. ((?name. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz)) \/
            cenv.ce_return_buf = SOME (PtrVar (Var p) sz) \/
            cenv.ce_return_pc = SOME (PtrVar (Var p) sz)) ==>
     FLOOKUP G' p = FLOOKUP G p /\
     op_taint tn' (Var p) = op_taint tn (Var p) /\
     lookup_var p t = lookup_var p s) /\
  (!name entry p sz w.
     lookup_scopes name es.scopes = SOME entry /\
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
     lookup_var p s = SOME w ==>
     val_wf entry.type entry.value /\
     (!i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
       i NOTIN (alloc1 UNION alloc2 UNION writes1 UNION writes2))) /\
  (!i. i NOTIN (writes1 UNION writes2) ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
  tn'.t_mem = (((tn.t_mem UNION alloc1) DIFF writes1) UNION alloc2) DIFF writes2 /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient ==>
  ghost_inv d cenv cx es G' tn' t
Proof
  strip_tac >> irule bodyPtrPrecompileBuiltinsSuffixGhostTheory.ghost_inv_exterior_frame >>
  qexistsl_tac [`G`, `s`, `tn`, `alloc1 UNION alloc2 UNION writes1 UNION writes2`] >>
  simp[] >> gvs[IN_UNION] >> metis_tac[]
QED

Theorem scoped_prefix_footprint_exterior:
  local_ptrs_rel func cenv scopes s /\
  (!name b sz. local_region cenv scopes s name b sz ==>
    DISJOINT {i | b <= i /\ i < b + sz} (alloc1 UNION alloc2) /\
    regions_disjoint off1 len1 b sz /\ regions_disjoint off2 len2 b sz) /\
  lookup_scopes name scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w ==>
  val_wf entry.type entry.value /\
  (!i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
    i NOTIN (alloc1 UNION alloc2 UNION {j | off1 <= j /\ j < off1 + len1}
      UNION {j | off2 <= j /\ j < off2 + len2}))
Proof
  strip_tac >> drule_all bodyPtrPrecompileBuiltinsFreshFrameTheory.scoped_value_footprint >> strip_tac >>
  `DISJOINT {i | w2n w <= i /\ i < w2n w + sz} (alloc1 UNION alloc2) /\
   regions_disjoint off1 len1 (w2n w) sz /\
   regions_disjoint off2 len2 (w2n w) sz` by metis_tac[] >>
  `!i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
    i NOTIN alloc1 /\ i NOTIN alloc2` by
    (rpt strip_tac >> `i < w2n w + sz` by decide_tac >>
     gvs[DISJOINT_ALT, arithmeticTheory.ADD_COMM] >>
     `i < sz + w2n w` by decide_tac >> metis_tac[]) >>
  simp[] >> rpt strip_tac >>
  gvs[compileEnvTheory.regions_disjoint_def] >> decide_tac
QED

Theorem local_region_allocation_growth_disjoint:
  local_ptrs_rel func cenv scopes s /\
  local_region cenv scopes s name b sz /\
  inst.inst_opcode = ALLOCA /\ step_inst_base inst s = OK t ==>
  DISJOINT {i | b <= i /\ i < b + sz} (new_site_bytes s t)
Proof
  strip_tac >> simp[DISJOINT_ALT] >> rpt strip_tac >>
  `s.vs_alloca_next <= x` by metis_tac[staging_alloca_footprint_above_frontier] >>
  `regions_disjoint b sz x 1` by
    metis_tac[localPtrsPropsTheory.local_ptrs_rel_above_frontier] >>
  gvs[compileEnvTheory.regions_disjoint_def] >> decide_tac
QED

Theorem emitted_allocation_spatial_frame:
  compile_alloc_buffer n sa = (buf,sb) /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ local_ptrs_rel fn cenv es.scopes s /\
  n < dimword(:256) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  eval_operand buf.buf_operand t = SOME w ==>
  !name b sz. local_region cenv es.scopes s name b sz ==>
    DISJOINT {i | b <= i /\ i < b + sz} (new_site_bytes s t) /\
    regions_disjoint (w2n w) n b sz
Proof
  strip_tac >>
  drule_all exprSimLiteralBufferTheory.alloc_buffer_frame_run >> strip_tac >>
  gvs[] >>
  drule bodyPtrPrecompileBuiltinsAllocationFrameTheory.emitted_allocation_singleton >>
  strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
     [STRING #"%" (toString sa.cs_next_var)]) s = OK t` by
    (Cases_on `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sa.cs_next_var)]) s` >> gvs[run_inst_seq_def]) >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule local_region_allocation_growth_disjoint >>
      conj_tac
      >- (goal_assum (drule_at Any) >> simp[venomInstTheory.mk_inst_def]) >>
      metis_tac[]) >>
  `local_region cenv es.scopes t name b sz` by
    (irule exprSimPropsTheory.local_region_frame_fwd >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

(* Instantiate (insz,outsz,zero_len) as (96,64,0) for ECMul,
   (128,64,0) for ECAdd, and (128,32,32) for ECRecover.  s2 is the
   ordinary post-input-staging state, not a reconstructed pointer endpoint.
   The input/output allocation contracts cover reused sites as well. *)
Theorem complete_prefix_scope_exterior:
  compile_alloc_buffer insz sf = (ib,sa) /\
  compile_alloc_buffer outsz sp = (ob,sm) /\
  stmt_state_rel ctx fn cenv cx es s0 /\ stmt_state_rel ctx fn cenv cx es s2 /\
  fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sp /\
  local_ptrs_rel fn cenv es.scopes s0 /\ local_ptrs_rel fn cenv es.scopes s2 /\
  insz < dimword(:256) /\ outsz < dimword(:256) /\ zero_len <= outsz /\
  MEM (mk_inst sf.cs_next_id ALLOCA [Lit (n2w insz)]
    [STRING #"%" (toString sf.cs_next_var)]) (fn_insts fn) /\
  MEM (mk_inst sp.cs_next_id ALLOCA [Lit (n2w outsz)]
    [STRING #"%" (toString sp.cs_next_var)]) (fn_insts fn) /\
  run_inst_seq (emitted_insts sf sa) s0 = OK s1 /\
  run_inst_seq (emitted_insts sp sm) s2 = OK s3 /\
  eval_operand ib.buf_operand s1 = SOME b /\
  eval_operand ob.buf_operand s3 = SOME c /\
  (!p. not_fresh_at sf p ==> lookup_var p s2 = lookup_var p s0) ==>
  !name entry p sz w.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s0 = SOME w ==>
    val_wf entry.type entry.value /\
    (!i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
      i NOTIN (new_site_bytes s0 s1 UNION new_site_bytes s2 s3 UNION
        {j | w2n b <= j /\ j < w2n b + insz} UNION
        {j | w2n c <= j /\ j < w2n c + zero_len}))
Proof
  strip_tac >> rpt gen_tac >> disch_tac >>
  qpat_assum `local_ptrs_rel fn cenv es.scopes s0`
    (mp_then Any irule scoped_prefix_footprint_exterior) >>
  reverse conj_tac >- (qexistsl_tac [`name`, `p`, `sz`] >> gvs[]) >>
  map_every qx_gen_tac [`nm`, `addr`, `extent`] >> strip_tac >>
  `local_region cenv es.scopes s2 nm addr extent` by
    (qpat_assum `local_ptrs_reserved cenv sf`
       (mp_then Any irule exprSimPropsTheory.local_region_frame_fwd) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule_all emitted_allocation_spatial_frame >> strip_tac >>
  qpat_assum `compile_alloc_buffer insz sf = (ib,sa)`
    (mp_then Any (drule_all_then strip_assume_tac) emitted_allocation_spatial_frame) >>
  conj_tac >- metis_tac[DISJOINT_UNION, DISJOINT_SYM] >>
  gvs[compileEnvTheory.regions_disjoint_def] >> decide_tac
QED
