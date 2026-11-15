(*
 * The extcall full case's operand and request stage over the finite-horizon
 * joint judgment.
 *
 * TOP-LEVEL:
 *   extcall_request_full
 *)
Theory bodyFullExtCallRequest
Ancestors
  bodyFullPreds bodySimFull gasOutcomeFull exprSimExtCallCase bodyPtrDefs
  bodyFullExtCallRequestSnapshotFull
  bodyFullExtCallRequestOperands bodyFullUnwrap
  abiEncoderWindowJoint abiEncoderSourceRobust abiEncodeArgsTyping
  bufferAllocationJoint extcallReturnDefaultMemoryJoint bodyFullPathHistory
  ptrDiscipline gasShadow exprSimHypsDefs exprLowering
  vyperInterpreter vyperAST list
  exprSimBufferStore context loweringPosts venomState venomExecSemantics compileEnv
  emitHelperProps exprLoweringProps fragExec exprSimWordBuiltins
  bodyPtrAttributeAdd assignBasePtrFieldAddress bodyFullGhostFrame
  typedCopyOriginPtrBase fragGasSeqPtr fragGasOriginPtr fragGasOriginPtrExec exprPtrUnwrapCopyEdges
  bodyPtrMakeArrayPrimitiveInstall wordLoadStorePtr unitTransformDefs venomInst codegenRel contextCodegenRel
  typedCopyPtr fragExecPtr ptrSafetyTransport assignBasePtrCleanStore
  typedCopyOriginPtr typedMemoryCopy typedCopyAgreement robustCopyTransportPtr
  ghostObservationPtr externalEntryShape
  bodyFullExtCallRequestInterfaces gasOutcomeFullCompose

val _ = Parse.hide "body";

Theorem extcall_unwrapped_slot_store:
  !cenv cx src dst ty sa sb tv v s d.
    (if is_word_type ty then emit_void MSTORE [dst;src]
     else if is_bytestring_type ty then compile_store_bytestring src dst
     else emit_void MCOPY [dst;src;Lit (n2w (type_memory_bytes cenv ty))])
      sa = ((),sb) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
    val_wf tv v /\ expr_val_rel cx ty v src s /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    type_memory_size tv < dimword (:256) /\ eval_operand dst s = SOME d /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) ==>
    ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
      val_in_memory tv v (w2n d) q.vs_memory /\
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
      (!a k. a + k <= w2n d \/ w2n d + type_memory_size tv <= a ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `is_word_type ty`
  >- (`compile_store_memory cenv src dst ty ty sa = ((),sb)` by
        gvs[compile_store_memory_def] >>
      drule_all buffer_store_memory_encoding >> simp[]) >>
  Cases_on `is_bytestring_type ty`
  >- (`compile_store_memory cenv src dst ty ty sa = ((),sb)` by
        gvs[compile_store_memory_def] >>
      drule_all buffer_store_memory_encoding >> simp[]) >>
  gvs[expr_val_rel_def] >>
  drule buffer_emit_mcopy_run >>
  disch_then drule >> disch_then drule >>
  simp[eval_operand_def] >> strip_tac >>
  rpt conj_tac
  >- (irule buffer_mcopy_encoding >> simp[] >>
      drule exprSimPropsTheory.val_store_size_le >>
      mp_tac exprSimPropsTheory.val_footprint_le_store_size >>
      metis_tac[arithmeticTheory.LESS_EQ_TRANS])
  >- simp[mcopy_def, write_memory_with_expansion_def]
  >- simp[mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
  rpt strip_tac >> irule buffer_mcopy_exterior >> decide_tac
QED

Theorem extcall_slot_mstore_origin:
  emit_void MSTORE [Var dst;src] sa = ((),sb) /\
  fn_has_code sa sb func /\
  lookup_var dst s = SOME dw /\ eval_operand src s = SOME w /\
  ptr_covers G tn dst s 32 /\ op_taint tn src = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  w2n dw + 32 <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t tn'.
    t = (mstore (w2n dw) w s with vs_inst_idx := SUC s.vs_inst_idx) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tn'.t_var = tn.t_var /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    tn'.t_mem = tn.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + 32} /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G,tn')
Proof
  strip_tac >>
  drule_all emit_void_fetch_boundary >> strip_tac >>
  qexistsl_tac [`mstore (w2n dw) w s with vs_inst_idx := SUC s.vs_inst_idx`,
    `step_taint (mk_inst sa.cs_next_id MSTORE [Var dst;src] []) s
      (mstore (w2n dw) w s) tn`] >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `sa.cs_next_id`] strip_assume_tac) >>
  `(step_taint (mk_inst sa.cs_next_id MSTORE [Var dst;src] []) s
      (mstore (w2n dw) w s) tn).t_imm = tn.t_imm` by
    simp[step_taint_def, imm_taint_def, mk_inst_def] >>
  `~(mstore (w2n dw) w s).vs_halted /\
   (mstore (w2n dw) w s).vs_current_bb = sb.cs_current_bb` by
    simp[mstore_def, write_memory_with_expansion_def] >>
  simp[] >> gen_tac >>
  `ptr_inst_ok D lo 0 ctx func G tn
    (mk_inst sa.cs_next_id MSTORE [Var dst;src] []) s` by
    (irule ptr_inst_ok_mstore_tainted >> simp[]) >>
  `inst_mem_below_frontier
    (mk_inst sa.cs_next_id MSTORE [Var dst;src] []) s /\
   inst_dload_in_section
    (mk_inst sa.cs_next_id MSTORE [Var dst;src] []) s` by
    simp[inst_mem_below_frontier_def,
         memSafeRunTheory.inst_dload_in_section_def, mk_inst_def,
         source_memory_read_ranges_def, source_memory_write_ranges_def,
         fixed_source_write_range_def, eval_operand_def] >>
  `step_inst_base (mk_inst sa.cs_next_id MSTORE [Var dst;src] []) s =
    OK (mstore (w2n dw) w s)` by
    simp[step_inst_base_def, exec_write2_def, mk_inst_def, eval_operand_def] >>
  drule_at (Pat `step_inst_base _ _ = _`) straight_line_origin_ptr_edge >>
  simp[mk_inst_def, is_terminator_def] >>
  strip_tac >>
  gvs[GSYM mk_inst_def] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (mstore (w2n dw) w s with
       vs_inst_idx := SUC (LENGTH sa.cs_current_insts)),G,
     step_taint (mk_inst sa.cs_next_id MSTORE [Var dst;src] []) s
       (mstore (w2n dw) w s) tn)` by
    metis_tac[] >>
  qpat_x_assum `!tn' lo' func' explicit ctx' bb' PG' G' D'. _` kall_tac >>
  qmatch_goalsub_abbrev_tac `OK t` >>
  `~t.vs_halted` by
    simp[Abbr `t`, mstore_def, write_memory_with_expansion_def] >>
  qpat_x_assum `gas_origin_ptr_edge _ _ _ _` mp_tac >>
  qpat_x_assum `~t.vs_halted` mp_tac >>
  rpt (pop_assum kall_tac) >>
  metis_tac[cj 1 gas_origin_ptr_path_rules,
            cj 2 gas_origin_ptr_path_rules, APPEND]
QED

Theorem extcall_slot_mcopy_origin:
  emit_void MCOPY [Var dst;Var src;Lit (n2w n)] sa = ((),sb) /\
  fn_has_code sa sb func /\
  lookup_var dst s = SOME dw /\ lookup_var src s = SOME sw /\
  ptr_covers G tn dst s n /\ ptr_covers G tn src s n /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ n < dimword (:256) /\
  w2n dw + n <= s.vs_alloca_next /\
  w2n sw + n <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t tn'.
    t = (mcopy (w2n dw) (w2n sw) n s with
           vs_inst_idx := SUC s.vs_inst_idx) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tn'.t_var = tn.t_var /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    tn'.t_mem = (tn.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + n})
      UNION {w2n dw + i | i < n /\ w2n sw + i IN tn.t_mem} /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G,tn')
Proof
  strip_tac >>
  drule_all emit_void_fetch_boundary >> strip_tac >>
  qexistsl_tac [`mcopy (w2n dw) (w2n sw) n s with
      vs_inst_idx := SUC s.vs_inst_idx`,
    `step_taint (mk_inst sa.cs_next_id MCOPY
       [Var dst;Var src;Lit (n2w n)] []) s
       (mcopy (w2n dw) (w2n sw) n s) tn`] >>
  `eval_operand (Var dst) s = SOME dw /\
   eval_operand (Var src) s = SOME sw /\
   eval_operand (Lit (n2w n)) s = SOME (n2w n) /\
   w2n (n2w n : bytes32) = n` by simp[eval_operand_def] >>
  qpat_assum `eval_operand (Var dst) s = SOME dw`
    (mp_then (Pos hd) mp_tac mcopy_operand_ghost_frame) >>
  disch_then (qspecl_then [`PG`, `G`, `tn`, `sa.cs_next_id`] mp_tac) >>
  disch_then (qspec_then `Var src` mp_tac) >> simp[] >>
  disch_then (qspec_then `Lit (n2w n)` mp_tac) >> simp[] >>
  strip_tac >>
  `(step_taint (mk_inst sa.cs_next_id MCOPY
     [Var dst;Var src;Lit (n2w n)] []) s
     (mcopy (w2n dw) (w2n sw) n s) tn).t_imm = tn.t_imm` by
    simp[step_taint_def, imm_taint_def, mk_inst_def] >>
  `~(mcopy (w2n dw) (w2n sw) n s).vs_halted /\
   (mcopy (w2n dw) (w2n sw) n s).vs_current_bb = sb.cs_current_bb` by
    simp[mcopy_def, write_memory_with_expansion_def] >>
  simp[] >> gen_tac >>
  `ptr_inst_ok D 0 0 ctx func G tn
    (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;Lit (n2w n)] []) s` by
    (irule ptr_inst_ok_mcopy >> simp[]) >>
  `ptr_inst_ok D lo 0 ctx func G tn
    (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;Lit (n2w n)] []) s` by
    (irule ptr_inst_ok_lower_bound_transport >> simp[] >>
     qexists_tac `0` >> simp[]) >>
  `inst_mem_below_frontier
    (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;Lit (n2w n)] []) s /\
   inst_dload_in_section
    (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;Lit (n2w n)] []) s` by
    simp[inst_mem_below_frontier_def,
         memSafeRunTheory.inst_dload_in_section_def, mk_inst_def,
         source_memory_read_ranges_def, source_memory_write_ranges_def,
         sized_source_write_range_def, eval_operand_def] >>
  `step_inst_base (mk_inst sa.cs_next_id MCOPY
     [Var dst;Var src;Lit (n2w n)] []) s =
     OK (mcopy (w2n dw) (w2n sw) n s)` by
    simp[step_inst_base_def, mk_inst_def, eval_operand_def] >>
  drule_at (Pat `step_inst_base _ _ = _`) straight_line_origin_ptr_edge >>
  simp[mk_inst_def, is_terminator_def] >> strip_tac >>
  gvs[GSYM mk_inst_def] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (mcopy (w2n dw) (w2n sw) n s with
       vs_inst_idx := SUC (LENGTH sa.cs_current_insts)),G,
     step_taint (mk_inst sa.cs_next_id MCOPY
       [Var dst;Var src;Lit (n2w n)] []) s
       (mcopy (w2n dw) (w2n sw) n s) tn)` by metis_tac[] >>
  qpat_x_assum `!tn' lo' func' explicit ctx' bb' PG' G' D'. _` kall_tac >>
  qmatch_goalsub_abbrev_tac `OK t` >>
  `~t.vs_halted` by
    simp[Abbr `t`, mcopy_def, write_memory_with_expansion_def] >>
  qpat_x_assum `gas_origin_ptr_edge _ _ _ _` mp_tac >>
  qpat_x_assum `~t.vs_halted` mp_tac >>
  rpt (pop_assum kall_tac) >>
  metis_tac[cj 1 gas_origin_ptr_path_rules,
            cj 2 gas_origin_ptr_path_rules, APPEND]
QED

Theorem extcall_slot_store_origin:
  (if is_word_type ty then emit_void MSTORE [Var dst;src]
   else if is_bytestring_type ty then compile_store_bytestring src (Var dst)
   else emit_void MCOPY [Var dst;src;Lit (n2w (type_memory_bytes cenv ty))])
    sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  expr_val_rel cx ty v src s /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  (is_word_type ty ==> type_memory_size tv = 32) /\
  lookup_var dst s = SOME dw /\ eval_operand src s = SOME sw /\
  not_fresh_at sa dst /\ (!x. src = Var x ==> not_fresh_at sa x) /\
  ptr_covers G tn dst s (type_memory_size tv) /\
  (is_word_type ty ==> op_taint tn src = {}) /\
  (~is_word_type ty ==>
    (?xs. src = Var xs /\ ptr_covers G tn xs s (type_memory_size tv)) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory tv v (w2n sw) mem) /\
    w2n sw + type_memory_size tv < dimword (:256) /\
    w2n sw + type_memory_size tv <= s.vs_alloca_next /\
    (w2n sw + type_memory_size tv <= w2n dw \/
     w2n dw + type_memory_size tv <= w2n sw)) /\
  w2n dw + type_memory_size tv < dimword (:256) /\
  w2n dw + type_memory_size tv <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size tv) s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tn'.t_imm = tn.t_imm /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size tv) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
      val_in_memory tv v (w2n dw) mem) /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> Cases_on `is_word_type ty`
  >- (gvs[] >> drule_all extcall_slot_mstore_origin >>
      disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
      `sw = typed_val_to_w256 tv v` by gvs[expr_val_rel_def] >>
      `val_in_memory tv v (w2n dw) (mstore (w2n dw) sw s).vs_memory` by
        (drule_all exprSimPropsTheory.val_in_memory_word >>
         disch_then (qspecl_then [`w2n dw`, `(mstore (w2n dw) sw s).vs_memory`] mp_tac) >>
         simp[valueEncodingPropsTheory.mstore_mem_word_at_same]) >>
      qexistsl_tac [`t`,`G`,`tn'`] >>
      simp[typed_copy_mstore_state_frame, op_taint_def] >>
      rpt strip_tac >> irule assignBasePtrLocalStoreTheory.assign_base_ptr_clean_window_robust_value >>
      conj_tac >- simp[] >>
      qexistsl_tac [`(mstore (w2n dw) sw s).vs_memory`,`32`,`tn.t_mem`] >>
      gvs[] >> metis_tac[exprSimPropsTheory.val_footprint_le_store_size,
        exprSimPropsTheory.val_store_size_le, arithmeticTheory.LESS_EQ_TRANS]) >>
  gvs[] >> (Cases_on `is_bytestring_type ty`
  >- (fs[] >>
      `compile_store_memory_typed cenv (Var dst) ty (Var xs) ty sa = ((),sb)` by
        simp[compile_store_memory_typed_bytes] >>
      `lookup_var xs s = SOME sw` by gvs[eval_operand_def] >>
      `w2n sw + type_memory_size tv < dimword (:256) /\
       w2n sw + type_memory_size tv <= s.vs_alloca_next` by decide_tac >>
      drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)
        compile_store_memory_typed_origin_ptr_path >>
      disch_then (drule_at (Pat `sfields_tenv_consistent _ _`)) >>
      disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
      simp[] >> disch_then drule_all >>
      disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
      qexistsl_tac [`t`,`Gf`,`tnf`] >> simp[] >> metis_tac[]) >>
  fs[eval_operand_def] >>
  `type_memory_size tv < dimword (:256) /\
   w2n sw + type_memory_size tv <= s.vs_alloca_next` by decide_tac >>
  `w2n dw + type_memory_size tv <= s.vs_alloca_next` by decide_tac >>
  drule_all extcall_slot_mcopy_origin >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`t`,`G`,`tn'`] >>
  simp[typed_copy_mcopy_state_frame, op_taint_def] >>
  conj_tac >- (rpt strip_tac >> simp[] >> eq_tac >> rpt strip_tac >> gvs[] >> decide_tac) >>
  rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`,
    `(mcopy (w2n dw) (w2n sw) (type_memory_size tv) s).vs_memory`,
    `type_memory_size tv`, `w2n sw`, `tn.t_mem`,
    `tn.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + type_memory_size tv}
      UNION {w2n dw + i | i < type_memory_size tv /\ w2n sw + i IN tn.t_mem}`] >>
  simp[valueEncodingPropsTheory.mcopy_mem_bytes_at_same] >>
  metis_tac[exprSimPropsTheory.val_footprint_le_store_size,
    exprSimPropsTheory.val_store_size_le, arithmeticTheory.LESS_EQ_TRANS])
QED

Theorem extcall_slot_protected_resources:
  typed_copy_state_frame sc a n s t /\
  (!x. not_fresh_at sc x ==>
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  (!i. ~(a <= i /\ i < a+n) ==> (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
  lo <= a /\ local_ptrs_reserved cenv sc /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  ghost_inv_at D lo d cenv cx ee G tn s /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  sa.cs_next_var <= sc.cs_next_var /\
  (!name entry p sz. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    val_wf entry.type entry.value /\
    (!w i. lookup_var p s = SOME w /\ w2n w <= i /\
      i < w2n w + val_footprint entry.type entry.value ==> ~(a <= i /\ i < a+n))) /\
  (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
    aid < sa.cs_next_id /\
    (!name b k. local_region cenv es.scopes s0 name b k ==> off+sz <= b \/ b+k <= off) /\
    off <= i /\ i < off+sz ==> ~(a <= i /\ i < a+n)) /\
  (!name b k i. local_region cenv es.scopes s0 name b k /\ b <= i /\ i < b+k ==>
    ~(a <= i /\ i < a+n)) /\
  (!rt v p. (rt,v,p) IN resources ==> val_wf rt v /\
    (!i. p <= i /\ i < p+val_footprint rt v ==> ~(a <= i /\ i < a+n)) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt v p mem)) ==>
  ghost_inv_at D lo d cenv cx ee G' tn' t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn' /\
  (!rt v p. (rt,v,p) IN resources ==>
    !mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==> val_in_memory rt v p mem)
Proof
  strip_tac >>
  `!i. ~(a <= i /\ i < a+n) ==>
     mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (fs[typed_copy_state_frame_def, typed_copy_frame_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  conj_tac >- suspend "ghost" >>
  conj_tac >- suspend "kept" >>
  rpt strip_tac >>
  irule robust_val_in_memory_exterior_no_new_taint >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`{i | a <= i /\ i < a+n}`,`s.vs_memory`,`t.vs_memory`,
    `tn.t_mem`,`tn'.t_mem`] >> simp[] >> metis_tac[]
QED

Resume extcall_slot_protected_resources[ghost]:
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables` by
    (fs[typed_copy_state_frame_def] >>
     qpat_x_assum `_ with <|vs_memory := _; vs_vars := _; vs_prev_bb := _;
       vs_current_bb := _; vs_inst_idx := _|> = _` mp_tac >>
     simp[venom_state_component_equality]) >>
  `!p k. not_fresh_at sc p /\ ptr_covers G tn p s k ==>
    ptr_covers G' tn' p t k` by
    (fs[typed_copy_state_frame_def, ptr_covers_def] >> metis_tac[]) >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (fs[typed_copy_state_frame_def, typed_copy_frame_def]) >>
  fs[ghost_inv_at_def] >>
  conj_tac >- suspend "locals" >>
  conj_tac >- (Cases_on `d` >- simp[return_buf_ptr_def] >>
    rename1 `return_buf_ptr (SOME pair) _ _ _ _` >> PairCases_on `pair` >>
    fs[return_buf_ptr_def, typed_copy_state_frame_def] >> metis_tac[]) >>
  conj_tac >- fs[stor_taint_ok_at_def] >>
  conj_tac >- (rpt strip_tac >>
    `~(a <= i /\ i < a+n)` by decide_tac >> metis_tac[]) >>
  conj_tac >- (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
  fs[allocas_from_def] >> metis_tac[]
QED

Resume extcall_slot_protected_resources[kept]:
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  fs[ghost_kept_at_def] >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  rpt strip_tac >>
  `~(a <= i /\ i < a+n)` by decide_tac >> metis_tac[]
QED

Resume extcall_slot_protected_resources[locals]:
  rpt gen_tac >> strip_tac >>
  `not_fresh_at sc p` by
    (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
  `ptr_covers G tn p s sz` by metis_tac[] >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `lookup_var p s = SOME w` by
    (fs[typed_copy_state_frame_def] >> metis_tac[]) >>
  irule robust_val_in_memory_exterior_no_new_taint >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`{i | a <= i /\ i < a+n}`,`s.vs_memory`,`t.vs_memory`,
    `tn.t_mem`,`tn'.t_mem`] >> simp[] >> metis_tac[]
QED

Finalise extcall_slot_protected_resources

Theorem extcall_saved_identity_unwrap:
  ((?tag op0. sv = StackValue tag op0) \/
   (?p. sv = LocatedValue ty p /\ ~is_word_type ty /\
        p.ptr_location = LocMemory)) /\
  read_result cx raw ee = (INL v,ee) /\
  vv_holds cenv cx ty raw sv ee s ==>
  unwrap_value cenv sv sa = (vv_operand sv,sa) /\
  expr_val_rel cx ty v (vv_operand sv) s
Proof
  strip_tac >>
  gvs[vv_holds_def, unwrap_value_def, comp_return_def, vv_operand_def,
      expr_val_rel_def] >>
  metis_tac[]
QED

Theorem extcall_saved_identity_after_add:
  ((?tag op0. sv = StackValue tag op0) \/
   (?p. sv = LocatedValue ty p /\ ~is_word_type ty /\
        p.ptr_location = LocMemory)) /\
  read_result cx raw ee = (INL v,ee) /\
  vv_holds cenv cx ty raw sv ee s /\
  (!x. vv_operand sv = Var x ==> not_fresh_at sa x) /\
  emit_op ADD [base_op; Lit (n2w off)] sa = (dst,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK q ==>
  unwrap_value cenv sv sb = (vv_operand sv,sb) /\
  expr_val_rel cx ty v (vv_operand sv) q
Proof
  strip_tac >>
  `unwrap_value cenv sv sb = (vv_operand sv,sb) /\
   expr_val_rel cx ty v (vv_operand sv) s` by
    metis_tac[extcall_saved_identity_unwrap] >>
  drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_def, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  gvs[exec_pure2_def, AllCaseEqs(), eval_operand_def] >>
  qmatch_goalsub_abbrev_tac `expr_val_rel cx ty v saved _` >>
  `eval_operand saved
     (update_var (STRING #"%" (toString sa.cs_next_var)) (v1 + n2w off) s) =
   eval_operand saved s` by
    (irule eval_operand_update_not_fresh >> qexists_tac `sa` >>
     simp[Abbr `saved`]) >>
  gvs[expr_val_rel_def, update_var_def, Abbr `saved`]
QED

Theorem extcall_saved_nonmemory_post:
  sv = LocatedValue (post_value_type cenv e) p /\
  p.ptr_location <> LocMemory /\
  ~is_word_type (post_value_type cenv e) /\
  post_value_type cenv e = expr_type e /\
  stmt_state_rel H ctx func cenv cx ee s /\
  storage_well_formed_on cx ee (FST H) /\
  vv_holds cenv cx (post_value_type cenv e) raw sv ee s /\
  vv_at cenv cx (post_value_type cenv e) sa sb ee raw sv s /\
  vv_storage_live H cx sv ee s ==>
  vv_post H ctx func cenv cx e ee si sm s ee raw sv s
Proof
  strip_tac >> gvs[vv_post_def, vv_at_def]
QED

Theorem extcall_saved_nonmemory_value_holds:
  p.ptr_location <> LocMemory /\
  read_result cx raw ee = (INL v,ee) /\
  vv_holds cenv cx ty raw (LocatedValue tag p) ee t ==>
  vv_holds cenv cx ty (Value v) (LocatedValue tag p) ee t
Proof
  strip_tac >> Cases_on `p.ptr_location` >>
  gvs[vv_holds_def, storage_holds_def, immutable_holds_def,
      vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  metis_tac[]
QED

Theorem extcall_saved_nonmemory_uniform_post:
  sv = LocatedValue (post_value_type cenv e) p /\
  p.ptr_location <> LocMemory /\
  ~is_word_type (post_value_type cenv e) /\
  post_value_type cenv e = expr_type e /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee t /\
    storage_well_formed_on cx ee (FST H) /\
    vv_storage_live H cx sv ee t /\
    (?raw. read_result cx raw ee = (INL v,ee) /\
      vv_holds cenv cx (post_value_type cenv e) raw sv ee t)) ==>
  !H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx e ee si sm t ee (Value v) sv t
Proof
  strip_tac >> gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `vv_holds cenv cx (post_value_type cenv e) (Value v) sv ee t` by
    metis_tac[extcall_saved_nonmemory_value_holds] >>
  irule extcall_saved_nonmemory_post >>
  simp[vv_at_def] >> metis_tac[]
QED

Theorem extcall_saved_nonmemory_unwrap_origin_ptr:
  saved = LocatedValue (post_value_type cenv e) p /\
  p.ptr_location <> LocMemory /\
  ~is_word_type (post_value_type cenv e) /\
  post_value_type cenv e = expr_type e /\
  compile_expr cenv (expr_type e) e si = (saved,sm) /\
  (is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)) /\
  sm.cs_next_var <= su.cs_next_var /\ sm.cs_next_id <= su.cs_next_id /\
  unwrap_value cenv saved su = (op,sv_end) /\
  local_ptrs_reserved cenv si /\ local_ptrs_reserved cenv sm /\
  MAP FDOM ee.scopes = MAP FDOM ee.scopes /\
  si.cs_next_var <= sm.cs_next_var /\ si.cs_next_id <= sm.cs_next_id /\
  fn_has_code su sv_end func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x. vv_operand saved = Var x ==> not_fresh_at sm x) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
    ~is_word_type (post_value_type cenv e) ==>
    type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
    type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  (!w. read_result cx (Value v) ee = (INL w,ee) ==> value_has_type rty w) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     (stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      vv_storage_live H cx saved ee t /\
      (?raw. read_result cx raw ee = (INL v,ee) /\
        vv_holds cenv cx (post_value_type cenv e) raw saved ee t)) /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn t) /\
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee (Value v) saved t /\
  alloca_history func t /\ t.vs_alloca_next <= t.vs_alloca_next /\
  ~t.vs_halted /\ t.vs_current_bb = su.cs_current_bb /\
  t.vs_inst_idx = LENGTH su.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv e) (Value v) saved ee G tn t /\
  (!tag op0. saved = StackValue tag op0 /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op0 G t) /\
  (!tag p. saved = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G t) /\
  (cenv.ce_is_ctor /\ vv_location saved = SOME LocCode ==>
   ?val. read_result cx (Value v) ee = (INL val, ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                eval_operand (vv_operand saved) t = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv ee si G tn t G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) ==>
  ?z G' tn'.
    read_result cx (Value v) ee = (INL v, ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (t, G, tn) [] (OK z, G', tn') /\
       expr_post H ctx func cenv cx e ee si sv_end t ee v op z /\
       ghost_inv_at (DF H) lo d cenv cx ee G' tn' z) /\
    (~is_word_type (post_value_type cenv e) ==>
     vv_at cenv cx (post_value_type cenv e) si sv_end ee (Value v)
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
    expr_store_bound cx (expr_type e) v op z /\
    z.vs_current_bb = sv_end.cs_current_bb /\
    z.vs_inst_idx = LENGTH sv_end.cs_current_insts /\
    alloca_history func z /\ t.vs_alloca_next <= z.vs_alloca_next /\
    t.vs_alloca_next <= z.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv e) v op G' tn' z /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G' z) /\
    (~is_word_type (post_value_type cenv e) ==>
     !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand op z = SOME w ==>
            type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo cenv ee si G tn t G' tn' /\
    (!x. not_fresh_at su x ==>
         lookup_var x z = lookup_var x t /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv ee ee su t z /\
    ghost_kept_at lo cenv ee su G tn t G' tn'
Proof
  strip_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e ee si sm t ee (Value v) saved t` by
    metis_tac[extcall_saved_nonmemory_uniform_post] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e ee si sm t ee (Value v) saved t /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn t` by metis_tac[] >>
  drule_all unwrap_value_origin_ptr >>
  simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def]
QED

Theorem extcall_saved_nonmemory_add_origin_ptr:
  saved = LocatedValue (post_value_type cenv e) p /\
  p.ptr_location <> LocMemory /\
  ~is_word_type (post_value_type cenv e) /\
  post_value_type cenv e = expr_type e /\
  compile_expr cenv (expr_type e) e si = (saved,sm) /\
  sm.cs_next_var <= su.cs_next_var /\ sm.cs_next_id <= su.cs_next_id /\
  si.cs_next_var <= sm.cs_next_var /\ si.cs_next_id <= sm.cs_next_id /\
  emit_op ADD [base_op; Lit (n2w off)] su = (dst,su1) /\
  fn_has_code su su1 func /\ ~ctx_has_dalloca ctx /\
  ~t.vs_halted /\ t.vs_current_bb = su.cs_current_bb /\
  t.vs_inst_idx = LENGTH su.cs_current_insts /\
  eval_operand base_op t = SOME bw /\ op_taint tn base_op = {} /\
  (!x. vv_operand saved = Var x ==> not_fresh_at su x) /\
  local_ptrs_reserved cenv su /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func cenv cx ee t /\
     storage_well_formed_on cx ee (FST H) /\
     vv_storage_live H cx saved ee t /\
     (?raw. read_result cx raw ee = (INL v,ee) /\
       vv_holds cenv cx (post_value_type cenv e) raw saved ee t) /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn t) /\
  ptr_vv_ok cx (post_value_type cenv e) (Value v) saved ee G tn t /\
  alloca_history func t /\ ghost_kept_at lo cenv ee si G tn t G tn /\
  (cenv.ce_is_ctor /\ vv_location saved = SOME LocCode ==>
   !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
          eval_operand (vv_operand saved) t = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                 val_in_memory rt v (w2n w) mem)) ==>
  ?out q G1 tn1.
    dst = Var out /\
    q = (update_var out (bw + n2w off) t with vs_inst_idx := SUC t.vs_inst_idx) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
         (t,G,tn) [] (OK q,G1,tn1) /\
       stmt_state_rel H ctx func cenv cx ee q /\
       storage_well_formed_on cx ee (FST H) /\
       vv_storage_live H cx saved ee q /\
       (?raw. read_result cx raw ee = (INL v,ee) /\
         vv_holds cenv cx (post_value_type cenv e) raw saved ee q) /\
       ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 q) /\
    ~q.vs_halted /\ q.vs_current_bb = su1.cs_current_bb /\
    q.vs_inst_idx = LENGTH su1.cs_current_insts /\
    eval_operand dst q = SOME (bw + n2w off) /\
    FLOOKUP G1 out = op_prov G base_op /\ op_taint tn1 dst = {} /\
    (!x. not_fresh_at su x ==>
      lookup_var x q = lookup_var x t /\ FLOOKUP G1 x = FLOOKUP G x /\
      op_taint tn1 (Var x) = op_taint tn (Var x)) /\
    q.vs_memory = t.vs_memory /\ q.vs_allocas = t.vs_allocas /\
    q.vs_alloca_next = t.vs_alloca_next /\
    q.vs_call_ctx = t.vs_call_ctx /\ q.vs_accounts = t.vs_accounts /\
    q.vs_transient = t.vs_transient /\ q.vs_immutables = t.vs_immutables /\
    tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
    tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
    sm.cs_next_var <= su1.cs_next_var /\ sm.cs_next_id <= su1.cs_next_id /\
    ptr_vv_ok cx (post_value_type cenv e) (Value v) saved ee G1 tn1 q /\
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee (Value v) saved q /\
    alloca_history func q /\
    ghost_kept_at lo cenv ee si G tn q G1 tn1 /\
    ghost_kept_at lo cenv ee su G tn t G1 tn1 /\
    (cenv.ce_is_ctor /\ vv_location saved = SOME LocCode ==>
     !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
            eval_operand (vv_operand saved) q = SOME w ==>
            w2n w + type_memory_size rt <= lo /\
            (!mem. mem_agree_outside tn1.t_mem q.vs_memory mem ==>
                   val_in_memory rt v (w2n w) mem))
Proof
  strip_tac >>
  `!out. step_inst_base (mk_inst su.cs_next_id ADD
      [base_op; Lit (n2w off)] [out]) t =
     OK (update_var out (bw + n2w off) t)` by
    (simp[Once step_inst_base_def, venomInstTheory.mk_inst_def, exec_pure2_def, eval_operand_def]) >>
  `eval_operand (Lit (n2w off)) t = SOME (n2w off) /\
   op_taint tn (Lit (n2w off)) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all (attribute_emit_binop_path_ptr |> Q.INST
    [`opc` |-> `ADD`, `f` |-> `word_add`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`,`G`,`ARB`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `op_taint tf (Var out) = {}` >>
  qmatch_asmsub_abbrev_tac `step_prov PG G inst u` >>
  qabbrev_tac `HG = step_prov PG G inst u` >>
  qabbrev_tac `q = (update_var out (bw + n2w off) t with
    vs_inst_idx := SUC t.vs_inst_idx)` >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (t,G,tn) [] (OK q,HG,tf)` by
    (rpt strip_tac >>
     `allocas_from lo t` by metis_tac[ghost_inv_at_def] >>
     drule_all (typed_copy_origin_ptr_binop_path |> Q.INST
       [`opc` |-> `ADD`, `x` |-> `bw`, `y` |-> `n2w off`,
        `w` |-> `bw + n2w off`] |> SRULE []) >>
     disch_then (qspecl_then [`0`,`explicit`,`PG`,`G`,`DF H`] mp_tac) >>
     simp[Abbr `q`, Abbr `HG`, Abbr `tf`] >> metis_tac[]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `~not_fresh_at su out` by
    (gvs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `!x. not_fresh_at su x ==> x <> out` by metis_tac[] >>
  `!x. not_fresh_at su x ==>
     lookup_var x q = lookup_var x t /\ FLOOKUP HG x = FLOOKUP G x /\
     op_taint tf (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> simp[Abbr `q`, Abbr `u`, lookup_var_def, update_var_def,
      finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
  `eval_operand (vv_operand saved) q = eval_operand (vv_operand saved) t` by
    (Cases_on `vv_operand saved` >>
     simp[eval_operand_def, Abbr `q`, Abbr `u`, update_var_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
  `q.vs_memory = t.vs_memory /\ q.vs_allocas = t.vs_allocas /\
   q.vs_alloca_next = t.vs_alloca_next /\ q.vs_call_ctx = t.vs_call_ctx /\
   q.vs_accounts = t.vs_accounts /\ q.vs_transient = t.vs_transient /\
   q.vs_immutables = t.vs_immutables` by simp[Abbr `q`, Abbr `u`, update_var_def] >>
  qexistsl_tac [`out`,`q`,`HG`,`tf`] >>
  simp[IgnAsm `saved = _`] >>
  conj_tac >- gvs[] >>
  conj_tac >- suspend "uniform" >>
  suspend "remainder"
QED

Resume extcall_saved_nonmemory_add_origin_ptr[uniform]:
  gen_tac >> strip_tac >>
  qpat_x_assum `!H. valid_horizon cx st0 H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _` drule >> strip_tac >>
  rpt conj_tac
  >- (simp[Abbr `q`, stmt_state_rel_inst_idx, Abbr `u`] >> irule stmt_state_rel_update_var >>
      metis_tac[exprSimOperandsTheory.fresh_not_local_ptr])
  >- (gvs[vv_storage_live_def, vv_operand_def] >> metis_tac[])
  >- suspend "holds"
  >- (irule ghost_inv_at_exterior_frame >> qexistsl_tac [`G`,`ee`,`t`,`su`,`tn`] >> simp[])
QED

Resume extcall_saved_nonmemory_add_origin_ptr[holds]:
  qexists_tac `raw` >> simp[] >>
  gvs[vv_holds_def, vv_operand_def] >>
  Cases_on `p.ptr_location` >>
  gvs[storage_holds_def, immutable_holds_def] >>
  gvs[Abbr `q`, Abbr `u`, update_var_def, contract_storage_def, contract_transient_def,
      contextTheory.vv_location_def] >> metis_tac[]
QED

Resume extcall_saved_nonmemory_add_origin_ptr[remainder]:
  `STRING #"%" (toString su.cs_next_var) = out` by gvs[] >>
  simp[] >>
  conj_tac >- simp[Abbr `q`, update_var_def] >>
  conj_tac >- (drule loweringShapeRulesTheory.emit_op_facts >>
    strip_tac >> simp[Abbr `q`, update_var_def]) >>
  conj_tac >- simp[Abbr `q`] >>
  conj_tac >- simp[Abbr `q`, eval_operand_def, lookup_var_def, update_var_def,
    finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac >- simp[Abbr `HG`, Abbr `inst`, attribute_add_provenance] >>
  conj_tac >-
    (simp[Abbr `q`, Abbr `u`] >>
     irule (SRULE [] assign_base_field_vv_update) >>
     conj_tac >- (strip_tac >> gvs[] >> metis_tac[]) >>
     qexistsl_tac [`G`,`tn`] >> simp[] >> gvs[]) >>
  conj_tac >- simp[exprSimMemDefsTheory.vv_store_bound_nonmem] >>
  conj_tac >- suspend "history" >>
  simp[ghost_kept_at_def, Abbr `q`, Abbr `u`, update_var_def] >>
  rpt strip_tac >>
  `not_fresh_at su x` by (irule loweringShapeDefsTheory.not_fresh_at_mono >>
    qexists_tac `si` >> simp[]) >> metis_tac[]
QED

Resume extcall_saved_nonmemory_add_origin_ptr[history]:
  drule_all bodyPtrMakeArrayEmissionTheory.emit_op_fetch_boundary >> strip_tac >>
  qpat_x_assum `alloca_history func t` mp_tac >>
  simp[allocaHistoryTheory.alloca_history_def, Abbr `q`, Abbr `u`, update_var_def] >>
  strip_tac >> rpt strip_tac >>
  `bb' = bb` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  Cases_on `k < LENGTH su.cs_current_insts` >- metis_tac[] >>
  `k = LENGTH su.cs_current_insts` by decide_tac >>
  gvs[Abbr `inst`, venomInstTheory.mk_inst_def]
QED

Finalise extcall_saved_nonmemory_add_origin_ptr

Theorem extcall_request_kwarg_scalar_outcome:
  body_expr_full_ok cx e /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env e es /\ ~expr_has_effect e /\
  ~(k = EKDefault /\ ~is_word_type rt) /\
  compile_ext_call_kwarg compile_expr cenv rt k e sa = ((op,dt),sb) /\
  compile_ext_call_kwarg compile_expr cenv rt k (gas_shadow_expr e)
    shadow_sa = ((op,dt),shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\ dt = rt /\
      expr_post H ctx func cenv cx e es sa sb s0 ee v op t /\
      expr_store_bound cx (expr_type e) v op t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      return_buf_frame d cenv sb t /\
      (ee with <|gas_obs := []; outcomes := NONE; storage_trace := []|>) =
      (es with <|gas_obs := []; outcomes := NONE; storage_trace := []|>))
    (\H res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  `lower_value compile_expr cenv
     (if k = EKDefault then rt else BaseT (UintT 256)) e sa = (op,sb) /\
   lower_value compile_expr cenv
     (if k = EKDefault then rt else BaseT (UintT 256)) (gas_shadow_expr e)
       shadow_sa = (op,shadow_sb) /\ dt = rt` by
    metis_tac[extcall_request_kwarg_word_compile] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (if k = EKDefault then rt else BaseT (UintT 256)) e es` by
    (qpat_x_assum `body_expr_full_ok cx e` mp_tac >>
     simp[Once body_expr_full_ok_def] >> metis_tac[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >> disch_then drule_all >> strip_tac >>
  irule gas_outcome_full_post_source >> goal_assum (drule_at Any) >>
  simp[] >> rpt gen_tac >> strip_tac >> gvs[] >>
  conj_tac
  >- (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
      qexistsl [`cenv`,`s0`,`sa`] >>
      simp[] >> reverse conj_tac
      >- (mp_tac (Q.SPECL [`cenv`, `if k = EKDefault then dt else BaseT (UintT 256)`, `e`, `sa`]
              ci_mono_lower_value_compile_expr) >>
          gvs[ci_mono_def]) >>
      gvs[expr_post_def]) >>
  qpat_x_assum `!tail. _ = (INL v,_)` (qspec_then `[]` mp_tac) >>
  simp[] >> strip_tac >>
  drule (CONV_RULE (DEPTH_CONV ETA_CONV) exprSimSourceTheory.eval_expr_read_INL) >>
  strip_tac >> drule vyperStateTheory.read_result_state >> strip_tac >> gvs[] >>
  drule_all bodyIntCallJointPureSourceTheory.effect_free_eval_expr_frame >>
  simp[]
QED

Theorem extcall_materialize_alloc_uniform:
  compile_alloc_buffer n sm = (buf,mid) /\ fn_has_code sm mid func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sm /\
  n < dimword (:256) /\ storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?r w HG tt.
    run_inst_seq (emitted_insts sm mid) s = OK r /\
    eval_operand buf.buf_operand r = SOME w /\
    FLOOKUP r.vs_allocas sm.cs_next_id = SOME (w2n w,n) /\
    w2n w + n < dimword (:256) /\ r.vs_memory = s.vs_memory /\
    sm.cs_next_id < mid.cs_next_id /\
    (!x. not_fresh_at sm x ==> lookup_var x r = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP r.vs_allocas aid = SOME entry) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at mid p) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee r /\
      ghost_inv_at (DF H) lo d cenv cx ee HG tt r /\
      ptr_covers HG tt (STRING #"%" (toString sm.cs_next_var)) r n /\
      ghost_kept_at lo cenv ee sm G tn s HG tt /\
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK (r with vs_inst_idx := LENGTH mid.cs_current_insts),HG,tt))
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    gvs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee s` by
    metis_tac[] >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  drule_all exprSimAllocTheory.literal_alloc_buffer_run >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq _ s = OK r` >>
  qabbrev_tac `inst = mk_inst sm.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString sm.cs_next_var)]` >>
  qabbrev_tac `HG = step_prov PG G inst r` >>
  qabbrev_tac `tt = step_taint inst s r tn` >>
  qexistsl_tac [`r`,`w`,`HG`,`tt`] >> simp[] >>
  gen_tac >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx ee s /\
   ghost_inv_at (DF H) lo d cenv cx ee G tn s` by metis_tac[] >>
  `allocas_from lo s` by gvs[ghost_inv_at_def] >>
  drule_all return_default_alloc_resources >> strip_tac >>
  drule_all return_default_alloc_ghost_resources >>
  simp[Abbr `HG`, Abbr `tt`, Abbr `inst`] >> strip_tac >>
  drule_all return_default_alloc_joint >>
  simp[]
QED

Theorem extcall_materialize_alloc_entry:
  compile_expr cenv ty e sa = (vv,sm) /\
  compile_alloc_buffer n sm = (buf,mid) /\ fn_has_code sm mid func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sm /\ n < dimword (:256) /\
  (is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)) /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
    ~is_word_type (post_value_type cenv e) ==>
    type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
    type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
  (!tag op0. vv = StackValue tag op0 /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op0 G s) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G s) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx tv ee = (INL v,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
        eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt v (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?a w HG tt p.
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK a,HG,tt) /\
      stmt_state_rel H ctx func cenv cx ee a /\
      ghost_inv_at (DF H) lo d cenv cx ee HG tt a /\
      vv_post H ctx func cenv cx e es sa sm s0 ee tv vv a) /\
    ~a.vs_halted /\ a.vs_current_bb = mid.cs_current_bb /\
    a.vs_inst_idx = LENGTH mid.cs_current_insts /\
    alloca_history func a /\ s.vs_alloca_next <= a.vs_alloca_next /\
    a.vs_memory = s.vs_memory /\ contract_storage a = contract_storage s /\
    contract_transient a = contract_transient s /\
    eval_operand buf.buf_operand a = SOME w /\
    FLOOKUP a.vs_allocas sm.cs_next_id = SOME (w2n w,n) /\
    w2n w + n < dimword (:256) /\ sm.cs_next_id < mid.cs_next_id /\
    buf.buf_operand = Var p /\ not_fresh_at mid p /\ ptr_covers HG tt p a n /\
    (!name b len. local_region cenv ee.scopes a name b len ==>
      regions_disjoint (w2n w) n b len) /\
    (!x. not_fresh_at sm x ==> lookup_var x a = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP a.vs_allocas aid = SOME entry) /\
    ghost_kept_at lo cenv ee sm G tn s HG tt /\
    ghost_kept_at lo cenv es sa Gi ti s0 HG tt /\
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv a /\
    ptr_vv_ok cx (post_value_type cenv e) tv vv ee HG tt a /\
    (!tag op0. vv = StackValue tag op0 /\ ~is_word_type (post_value_type cenv e) ==>
      ptr_buf_ok cenv e op0 HG a) /\
    (!tag q. vv = LocatedValue tag q /\ q.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e q.ptr_operand HG a) /\
    (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
      ?v. read_result cx tv ee = (INL v,ee) /\
        !rt u. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
          eval_operand (vv_operand vv) a = SOME u ==>
          w2n u + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tt.t_mem a.vs_memory mem ==>
            val_in_memory rt v (w2n u) mem))
Proof
  strip_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s` by
    (rpt strip_tac >> first_x_assum drule >> simp[vv_post_def]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    gvs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee s` by
    metis_tac[] >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  drule_all exprSimAllocTheory.literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sm mid) s = OK r` >>
  qabbrev_tac `inst = mk_inst sm.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString sm.cs_next_var)]` >>
  qabbrev_tac `HG = step_prov PG G inst r` >>
  qabbrev_tac `tt = step_taint inst s r tn` >>
  drule_all return_default_alloc_run_step >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    gvs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee s /\
   ghost_inv_at (DF (storage_trace_horizon ee.storage_trace)) lo d cenv cx ee G tn s` by
    metis_tac[] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by gvs[ghost_inv_at_def] >>
  drule_all return_default_alloc_control >> strip_tac >>
  drule_all bodyPtrIfExpAllocSourceTheory.alloca_step_contracts >> strip_tac >>
  `r.vs_labels = s.vs_labels` by
    (qspecl_then [`sm.cs_next_id`,`n2w n`,
       `STRING #"%" (toString sm.cs_next_var)`,`s`] mp_tac
       loweringHaltTheory.step_alloca_frame >>
     strip_tac >> gvs[]) >>
  `eval_operand (vv_operand vv) r = eval_operand (vv_operand vv) s` by
    (Cases_on `vv_operand vv` >> simp[eval_operand_def] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee r` by
    (gen_tac >> strip_tac >>
     `stmt_state_rel H ctx func cenv cx ee s` by metis_tac[] >>
     drule_all return_default_alloc_resources >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx e es sa sm s0 ee tv vv r` by
    (rpt strip_tac >>
     irule abiEncodeMaterializeTheory.materialize_vv_post_alloc_storage_frame >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`s`,`sm`] >> simp[] >> metis_tac[]) >>
  drule_all return_default_alloc_resources >> strip_tac >>
  `w' = w` by metis_tac[optionTheory.SOME_11] >>
  `s.vs_alloca_next <= r.vs_alloca_next` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[update_var_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee r /\
    ghost_inv_at (DF H) lo d cenv cx ee HG tt r /\
    ptr_covers HG tt (STRING #"%" (toString sm.cs_next_var)) r n /\
    ghost_kept_at lo cenv ee sm G tn s HG tt /\
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (r with vs_inst_idx := LENGTH mid.cs_current_insts),HG,tt)` by
    (gen_tac >> strip_tac >>
     `stmt_state_rel H ctx func cenv cx ee s /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn s` by metis_tac[] >>
     drule_all return_default_alloc_resources >> strip_tac >>
     drule_all return_default_alloc_ghost_resources >>
     simp[Abbr `HG`, Abbr `tt`, Abbr `inst`] >>
     strip_tac >>
     drule_all return_default_alloc_joint >> simp[]) >>
  qexistsl_tac [`r with vs_inst_idx := LENGTH mid.cs_current_insts`,
    `w`,`HG`,`tt`,`p`] >>
  conj_tac >-
    (gen_tac >> strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ r /\ _`
       (drule_then strip_assume_tac) >>
     simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx,
          ghostPcTransportPtrTheory.ghost_inv_at_inst_idx]) >>
  simp[] >>
  conj_tac >-
    (irule bodyAllocMemoryTheory.body_alloc_history >>
     conj_tac >- simp[] >>
     qexistsl_tac [`buf`,`s`,`sm`,`n`] >> simp[] >>
     gvs[stmt_state_rel_def]) >>
  simp[contract_storage_def, contract_transient_def, lookup_var_def] >>
  `STRING #"%" (toString sm.cs_next_var) = p` by
    (qpat_x_assum `buf.buf_operand = Var p` mp_tac >> simp[]) >>
  simp[] >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ r /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  simp[] >> strip_tac >> simp[] >>
  conj_tac >-
    (qpat_x_assum `!name off sz. local_region _ _ _ _ _ _ ==> _` mp_tac >>
     simp[]) >>
  conj_tac >- simp[GSYM lookup_var_def] >>
  conj_tac >- suspend "ghost_compose" >>
  conj_tac >-
    (qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
     simp[exprSimMemDefsTheory.vv_store_bound_def] >> strip_tac >>
     conj_tac >> rpt strip_tac >> gvs[vv_operand_def] >>
     qpat_x_assum `SOME _ = eval_operand _ s` (assume_tac o SYM) >>
     first_x_assum (drule_at (Pat `eval_operand _ s = SOME _`)) >>
     simp[] >> strip_tac >> gvs[]) >>
  `(!i. i < s.vs_alloca_next ==> (i IN tt.t_mem <=> i IN tn.t_mem)) /\
   (!x. x <> p ==> lookup_var x r = lookup_var x s /\
     FLOOKUP HG x = FLOOKUP G x /\
     op_taint tt (Var x) = op_taint tn (Var x))` by
    (simp[Abbr `HG`, Abbr `tt`, Abbr `inst`] >>
     drule_all bodyPtrEnvBuiltinsAllocationTheory.alloca_step_frame_effects >>
     disch_then (qspecl_then [`PG`,`G`,`tn`] mp_tac) >> simp[]) >>
  `!x. vv_operand vv = Var x ==> x <> p` by
    (rpt strip_tac >> first_x_assum drule >>
     gvs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `(!x. vv_operand vv = Var x ==> FLOOKUP HG x = FLOOKUP G x) /\
   op_taint tt (vv_operand vv) = op_taint tn (vv_operand vv)` by
    (Cases_on `vv_operand vv` >> simp[op_taint_def] >> metis_tac[]) >>
  reverse conj_tac >- (conj_tac >-
    (rpt strip_tac >> irule logValueFramePtrTheory.ptr_buf_ok_frame >>
     qexistsl_tac [`G`,`s`] >> gvs[vv_operand_def] >> metis_tac[]) >>
    conj_tac >-
    (rpt strip_tac >> irule logValueFramePtrTheory.ptr_buf_ok_frame >>
     qexistsl_tac [`G`,`s`] >> gvs[vv_operand_def] >> metis_tac[]) >>
    (strip_tac >>
     qpat_x_assum `cenv.ce_is_ctor /\ _ ==> _` mp_tac >>
     simp[] >> strip_tac >>
     qexists_tac `v` >> simp[] >> gen_tac >> strip_tac >>
     qpat_x_assum `!w''. eval_operand _ s = SOME w'' ==> _`
       (qspec_then `u` mp_tac) >> simp[] >> strip_tac >>
     match_mp_tac logValueFramePtrTheory.robust_val_in_memory_footprint_frame >>
     qexistsl_tac [`tn.t_mem`,`s.vs_memory`] >> simp[] >>
     `val_wf rty v` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
     simp[] >> rpt strip_tac >>
     `val_footprint rty v <= type_memory_size rty` by
       metis_tac[exprSimPropsTheory.val_footprint_le] >>
     `i < s.vs_alloca_next` by decide_tac >> metis_tac[])) >>
  `vv_at cenv cx (post_value_type cenv e) sa sm ee tv vv s` by
    (qpat_x_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
      (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     simp[vv_post_def]) >>
  Cases_on `vv` >-
    (gvs[ptr_vv_ok_def, vv_operand_def, vv_at_def] >>
     irule logValueFramePtrTheory.ptr_val_ok_footprint_frame >>
     qexistsl_tac [`G`,`s`,`tn`] >> simp[] >>
     rpt gen_tac >> strip_tac >>
     conj_tac >- metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
     rpt strip_tac >>
     `i < s.vs_alloca_next` by
       (irule (INST_TYPE [``:'a`` |-> ``:256``]
          allocationPtrTheory.expr_val_at_below_frontier) >>
        qpat_assum `expr_val_at _ _ _ _ _ _ _ _ s`
          (irule_at Any) >> metis_tac[]) >> metis_tac[]) >>
  gvs[ptr_vv_ok_def, vv_operand_def] >>
  conj_tac >- (Cases_on `p'.ptr_operand` >> gvs[op_prov_def]) >>
  reverse conj_tac >-
    (simp[Abbr `tt`, step_taint_def, Abbr `inst`, store_taint_def,
          adopt_reset_def, mk_inst_def] >> metis_tac[]) >>
  strip_tac >> gvs[] >>
  simp[ptr_mem_ok_def] >> gen_tac >> disch_tac >>
  reverse conj_tac >-
    (qpat_x_assum `ptr_mem_ok _ _ _ _ G tn s` mp_tac >>
     simp[ptr_mem_ok_def] >> metis_tac[]) >>
  match_mp_tac logValueFramePtrTheory.robust_val_in_memory_footprint_frame >>
  qexistsl_tac [`tn.t_mem`,`s.vs_memory`] >> simp[] >>
  conj_tac >- metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  conj_tac >-
  (rpt strip_tac >>
  `i < s.vs_alloca_next` by
    (`stmt_state_rel (storage_trace_horizon ee.storage_trace)
        ctx func cenv cx ee s` by metis_tac[] >>
     `alloca_next_valid s` by
       metis_tac[exprLoweringPropsTheory.stmt_state_rel_def,
                 venomMemDefsTheory.alloca_inv_def] >>
     qpat_x_assum `vv_at _ _ _ _ _ _ _ _ s` mp_tac >>
     simp[vv_at_def] >> strip_tac >> gvs[]
     >- (fs[venomMemDefsTheory.alloca_next_valid_def] >> res_tac >> decide_tac) >>
     `stmt_state_rel (storage_trace_horizon ee.storage_trace)
        ctx func cenv cx ee s` by metis_tac[] >>
     drule_all abiEncodeOwnershipTheory.abi_encode_local_region_frontier >>
     decide_tac) >> metis_tac[]) >>
  qpat_x_assum `ptr_mem_ok _ _ _ _ G tn s` mp_tac >>
  simp[ptr_mem_ok_def] >> metis_tac[]
QED

Resume extcall_materialize_alloc_entry[ghost_compose]:
  `(!i. i < s.vs_alloca_next ==> (i IN tt.t_mem <=> i IN tn.t_mem)) /\
   (!x. x <> p ==> lookup_var x r = lookup_var x s /\
     FLOOKUP HG x = FLOOKUP G x /\
     op_taint tt (Var x) = op_taint tn (Var x))` by
    (simp[Abbr `HG`, Abbr `tt`, Abbr `inst`] >>
     drule_all bodyPtrEnvBuiltinsAllocationTheory.alloca_step_frame_effects >>
     disch_then (qspecl_then [`PG`,`G`,`tn`] mp_tac) >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x /\ x <> p` by
    (rpt strip_tac >>
     gvs[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
  `vv_post (storage_trace_horizon ee.storage_trace)
      ctx func cenv cx e es sa sm s0 ee tv vv s` by metis_tac[] >>
  simp[ghost_kept_at_def] >> conj_tac >- metis_tac[ghost_kept_at_def] >>
  conj_tac >-
    (rpt strip_tac >>
     `FLOOKUP s.vs_allocas aid = SOME (off,sz)` by metis_tac[vv_post_def] >>
     `off + sz <= s.vs_alloca_next` by
       metis_tac[exprLoweringPropsTheory.stmt_state_rel_def,
         venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
     `i < s.vs_alloca_next` by decide_tac >>
     `i IN tn.t_mem` by
       (qpat_x_assum `!i. i < s.vs_alloca_next ==> _`
          (qspec_then `i` mp_tac) >> simp[]) >>
     qpat_x_assum `ghost_kept_at lo cenv es sa Gi ti s0 G tn` mp_tac >>
     simp[ghost_kept_at_def] >> strip_tac >>
     first_x_assum (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  conj_tac >-
    (rpt strip_tac >>
     `local_region cenv ee.scopes s n' b sz` by
       (irule exprSimPropsTheory.local_region_frame_fwd >>
        qexistsl_tac [`s0`,`sa`,`es.scopes`] >> simp[] >>
        metis_tac[vv_post_def]) >>
     `b + sz <= s.vs_alloca_next` by
       (drule_all abiEncodeOwnershipTheory.abi_encode_local_region_frontier >> simp[]) >>
     `i < s.vs_alloca_next` by decide_tac >>
     `i IN tn.t_mem` by
       (qpat_x_assum `!i. i < s.vs_alloca_next ==> _`
         (qspec_then `i` mp_tac) >> simp[]) >>
     metis_tac[ghost_kept_at_def]) >>
  rpt strip_tac >> `i IN tn.t_mem` by metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS] >>
  metis_tac[ghost_kept_at_def]
QED

Finalise extcall_materialize_alloc_entry

Theorem extcall_materialize_alloc_unwrap_joint:
  (compile_expr cenv ty e sa = (vv,sm) /\
  compile_alloc_buffer n sm = (buf,mid) /\ fn_has_code sm mid func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sm /\ n < dimword (:256) /\
  (is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)) /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
    ~is_word_type (post_value_type cenv e) ==>
    type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
    type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
  (!tag op0. vv = StackValue tag op0 /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op0 G s) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G s) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx tv ee = (INL v,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
        eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt v (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x)) /\
  unwrap_value cenv vv mid = (op,sc) /\ fn_has_code mid sc func /\
  sm.cs_next_var <= mid.cs_next_var /\ sm.cs_next_id <= mid.cs_next_id ==>
  ?a w HG tt p v z G' tn'.
    ((!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK a,HG,tt) /\
      stmt_state_rel H ctx func cenv cx ee a /\
      ghost_inv_at (DF H) lo d cenv cx ee HG tt a /\
      vv_post H ctx func cenv cx e es sa sm s0 ee tv vv a) /\
    ~a.vs_halted /\ a.vs_current_bb = mid.cs_current_bb /\
    a.vs_inst_idx = LENGTH mid.cs_current_insts /\
    alloca_history func a /\ s.vs_alloca_next <= a.vs_alloca_next /\
    a.vs_memory = s.vs_memory /\ contract_storage a = contract_storage s /\
    contract_transient a = contract_transient s /\
    eval_operand buf.buf_operand a = SOME w /\
    FLOOKUP a.vs_allocas sm.cs_next_id = SOME (w2n w,n) /\
    w2n w + n < dimword (:256) /\ sm.cs_next_id < mid.cs_next_id /\
    buf.buf_operand = Var p /\ not_fresh_at mid p /\ ptr_covers HG tt p a n /\
    (!name b len. local_region cenv ee.scopes a name b len ==>
      regions_disjoint (w2n w) n b len) /\
    (!x. not_fresh_at sm x ==> lookup_var x a = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP a.vs_allocas aid = SOME entry) /\
    ghost_kept_at lo cenv ee sm G tn s HG tt /\
    ghost_kept_at lo cenv es sa Gi ti s0 HG tt /\
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv a /\
    ptr_vv_ok cx (post_value_type cenv e) tv vv ee HG tt a /\
    (!tag op0. vv = StackValue tag op0 /\ ~is_word_type (post_value_type cenv e) ==>
      ptr_buf_ok cenv e op0 HG a) /\
    (!tag q. vv = LocatedValue tag q /\ q.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e q.ptr_operand HG a) /\
    (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
      ?v. read_result cx tv ee = (INL v,ee) /\
        !rt u. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
          eval_operand (vv_operand vv) a = SOME u ==>
          w2n u + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tt.t_mem a.vs_memory mem ==>
            val_in_memory rt v (w2n u) mem))) /\
    (read_result cx tv ee = (INL v, ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (a, HG, tt) [] (OK z, G', tn') /\
       expr_post H ctx func cenv cx e es sa sc s0 ee v op z /\
       ghost_inv_at (DF H) lo d cenv cx ee G' tn' z) /\
    (~is_word_type (post_value_type cenv e) ==>
     vv_at cenv cx (post_value_type cenv e) sa sc ee tv
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
    expr_store_bound cx (expr_type e) v op z /\
    z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ a.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv e) v op G' tn' z /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G' z) /\
    (~is_word_type (post_value_type cenv e) ==>
     !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand op z = SOME w ==>
            type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G' tn' /\
    (!x. not_fresh_at mid x ==>
         lookup_var x z = lookup_var x a /\ FLOOKUP G' x = FLOOKUP HG x /\
         op_taint tn' (Var x) = op_taint tt (Var x)) /\
    wb_frame cenv ee ee mid a z /\
    ghost_kept_at lo cenv ee mid HG tt a G' tn') /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK z,G',tn'))
Proof
  strip_tac >> drule_all extcall_materialize_alloc_entry >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  disch_then (qx_choose_then `a` (qx_choose_then `w`
    (qx_choose_then `HG` (qx_choose_then `tt` (qx_choose_then `p` strip_assume_tac))))) >>
  `s0.vs_alloca_next <= a.vs_alloca_next` by decide_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e es sa sm s0 ee tv vv a /\
     ghost_inv_at (DF H) lo d cenv cx ee HG tt a` by metis_tac[] >>
  drule_all bodyFullUnwrapTheory.unwrap_value_origin_ptr >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  disch_then (qx_choose_then `v` (qx_choose_then `z`
    (qx_choose_then `G'` (qx_choose_then `tn'` strip_assume_tac)))) >>
  qexistsl_tac [`a`,`w`,`HG`,`tt`,`p`,`v`,`z`,`G'`,`tn'`] >>
  conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
     (s,G,tn) [] (OK a,HG,tt)` by metis_tac[] >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
     (a,HG,tt) [] (OK z,G',tn')` by metis_tac[] >>
  qpat_x_assum `gas_origin_ptr_path _ (s,G,tn) [] (OK a,HG,tt)`
    (mp_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
  disch_then (qspecl_then [`a`,`HG`,`tt`,`[]`,`OK z`,`G'`,`tn'`] mp_tac) >>
  simp[]
QED

Theorem extcall_materialize_unwrap_destination:
    ((!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK a,HG,tt) /\
      stmt_state_rel H ctx func cenv cx ee a /\
      ghost_inv_at (DF H) lo d cenv cx ee HG tt a /\
      vv_post H ctx func cenv cx e es sa sm s0 ee tv vv a) /\
    ~a.vs_halted /\ a.vs_current_bb = mid.cs_current_bb /\
    a.vs_inst_idx = LENGTH mid.cs_current_insts /\
    alloca_history func a /\ s.vs_alloca_next <= a.vs_alloca_next /\
    a.vs_memory = s.vs_memory /\ contract_storage a = contract_storage s /\
    contract_transient a = contract_transient s /\
    eval_operand buf.buf_operand a = SOME w /\
    FLOOKUP a.vs_allocas sm.cs_next_id = SOME (w2n w,n) /\
    w2n w + n < dimword (:256) /\ sm.cs_next_id < mid.cs_next_id /\
    buf.buf_operand = Var p /\ not_fresh_at mid p /\ ptr_covers HG tt p a n /\
    (!name b len. local_region cenv ee.scopes a name b len ==>
      regions_disjoint (w2n w) n b len) /\
    (!x. not_fresh_at sm x ==> lookup_var x a = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP a.vs_allocas aid = SOME entry) /\
    ghost_kept_at lo cenv ee sm G tn s HG tt /\
    ghost_kept_at lo cenv es sa Gi ti s0 HG tt /\
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv a /\
    ptr_vv_ok cx (post_value_type cenv e) tv vv ee HG tt a /\
    (!tag op0. vv = StackValue tag op0 /\ ~is_word_type (post_value_type cenv e) ==>
      ptr_buf_ok cenv e op0 HG a) /\
    (!tag q. vv = LocatedValue tag q /\ q.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e q.ptr_operand HG a) /\
    (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
      ?v. read_result cx tv ee = (INL v,ee) /\
        !rt u. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
          eval_operand (vv_operand vv) a = SOME u ==>
          w2n u + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tt.t_mem a.vs_memory mem ==>
            val_in_memory rt v (w2n u) mem))) /\
    (read_result cx tv ee = (INL v, ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (a, HG, tt) [] (OK z, G', tn') /\
       expr_post H ctx func cenv cx e es sa sc s0 ee v op z /\
       ghost_inv_at (DF H) lo d cenv cx ee G' tn' z) /\
    (~is_word_type (post_value_type cenv e) ==>
     vv_at cenv cx (post_value_type cenv e) sa sc ee tv
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
    expr_store_bound cx (expr_type e) v op z /\
    z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ a.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv e) v op G' tn' z /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G' z) /\
    (~is_word_type (post_value_type cenv e) ==>
     !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand op z = SOME w ==>
            type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G' tn' /\
    (!x. not_fresh_at mid x ==>
         lookup_var x z = lookup_var x a /\ FLOOKUP G' x = FLOOKUP HG x /\
         op_taint tn' (Var x) = op_taint tt (Var x)) /\
    wb_frame cenv ee ee mid a z /\
    ghost_kept_at lo cenv ee mid HG tt a G' tn') /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK z,G',tn')) ==>
    eval_operand buf.buf_operand z = SOME w /\ lookup_var p z = SOME w /\
    FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n w,n) /\
    ptr_covers G' tn' p z n /\
    mem_bytes_at (w2n w) n z.vs_memory = mem_bytes_at (w2n w) n a.vs_memory /\
    w2n w + n < dimword (:256)
Proof
  strip_tac >>
  `lookup_var p a = SOME w` by fs[eval_operand_def] >>
  `lookup_var p z = SOME w` by metis_tac[] >>
  `ptr_covers G' tn' p z n` by
    (fs[ptr_covers_def] >> metis_tac[]) >>
  fs[wb_frame_def] >>
  `mem_bytes_at (w2n w) n z.vs_memory = mem_bytes_at (w2n w) n a.vs_memory` by
    (first_x_assum irule >> simp[] >> conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _`
           (drule_then mp_tac) >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
     qexists `sm.cs_next_id` >> simp[]) >>
  simp[eval_operand_def]
QED

Theorem extcall_request_kwarg_materialize_outcome:
  body_expr_full_ok cx e /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env e es /\ ~expr_has_effect e /\
  ~is_word_type rt /\ ~is_word_type (expr_type e) /\
  compile_ext_call_kwarg compile_expr cenv rt EKDefault e sa = ((op,dt),sb) /\
  compile_ext_call_kwarg compile_expr cenv rt EKDefault (gas_shadow_expr e)
    shadow_sa = ((op,dt),shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\ dt = lowered_value_type cenv e /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      ptr_val_ok cx dt v op G tn t /\ ptr_mem_ok cx dt v op G tn t /\
      ptr_buf_ok cenv e op G t /\
      (!w. eval_operand op t = SOME w /\ type_memory_bytes cenv dt <> 0 ==>
        w2n w + type_memory_bytes cenv dt <= t.vs_alloca_next) /\
      (!x. op = Var x ==> not_fresh_at sb x) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      return_buf_frame d cenv sb t /\ pure_frame cenv func es sa s0 t /\
      (ee with <|gas_obs := []; outcomes := NONE; storage_trace := []|>) =
      (es with <|gas_obs := []; outcomes := NONE; storage_trace := []|>))
    (\H res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  `dt = lowered_value_type cenv e /\ ?vv sm.
    compile_expr cenv (expr_type e) e sa = (vv,sm) /\
    compile_materialize_vv cenv dt vv sm = (op,sb)` by
    metis_tac[extcall_request_kwarg_materialize_compile] >>
  gvs[compile_materialize_vv_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, pairTheory.pair_case_thm] >>
  Cases_on `compile_alloc_buffer (type_memory_bytes cenv (lowered_value_type cenv e)) sm` >>
  rename1 `compile_alloc_buffer _ sm = (buf,mid)` >>
  Cases_on `unwrap_value cenv vv mid` >>
  rename1 `unwrap_value cenv vv mid = (src,sc)` >>
  Cases_on `compile_store_memory cenv src buf.buf_operand
    (lowered_value_type cenv e) (lowered_value_type cenv e) sc` >>
  gvs[] >>
  Cases_on `compile_expr cenv (expr_type e) (gas_shadow_expr e) shadow_sa` >>
  rename1 `compile_expr _ _ (gas_shadow_expr e) shadow_sa = (sv,shadow_sm)` >>
  `sv = vv /\ gas_shadow_state sm shadow_sm` by
    (mp_tac (Q.SPECL [`cenv`,`expr_type e`,`e`, `T`]
       (cj 1 gasShadowCompileTheory.gas_shadow_compile_expr)) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  gvs[] >>
  rename1 `compile_store_memory _ _ _ _ _ sc = ((),sb)` >>
  `ci_mono sa sm` by
    (mp_tac (Q.SPECL [`cenv`,`expr_type e`,`e`,`sa`]
      (cj 1 stmtLoweringMonoTheory.ci_mono_compile_expr_sa)) >> simp[]) >>
  `ci_mono sm mid` by
    (mp_tac (Q.SPECL [`type_memory_bytes cenv (lowered_value_type cenv e)`,`sm`]
      ci_mono_compile_alloc_buffer) >> simp[]) >>
  `ci_mono mid sc` by
    (mp_tac (Q.SPECL [`cenv`,`sv`,`mid`] ci_mono_unwrap_value) >> simp[]) >>
  `ci_mono sc sb` by
    (mp_tac (Q.SPECL [`cenv`,`src`,`buf.buf_operand`,
       `lowered_value_type cenv e`,`lowered_value_type cenv e`,`sc`]
      ci_mono_compile_store_memory) >> simp[]) >>
  `cs_extends sm sb` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> fs[ci_mono_def] >> metis_tac[]) >>
  `fn_has_code sm mid func /\ fn_has_code mid sb func` by
    (irule fn_has_code_split >> fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code mid sc func /\ fn_has_code sc sb func` by
    (irule fn_has_code_split >> fs[ci_mono_def] >> metis_tac[]) >>
  `compile_materialize_vv cenv (lowered_value_type cenv e) sv
       shadow_sm = (buf.buf_operand,shadow_sb)` by
    (qpat_x_assum `compile_ext_call_kwarg _ _ _ _ (gas_shadow_expr e) _ = _`
       mp_tac >>
     simp[extcall_request_kwarg_materialize_compile] >>
     metis_tac[]) >>
  `ci_mono shadow_sa shadow_sm /\ ci_mono shadow_sm shadow_sb` by
    (mp_tac (Q.SPECL [`cenv`,`expr_type e`,`gas_shadow_expr e`,`shadow_sa`]
       (cj 1 stmtLoweringMonoTheory.ci_mono_compile_expr_sa)) >>
     mp_tac (Q.SPECL [`cenv`,`lowered_value_type cenv e`,`sv`,`shadow_sm`]
       ci_mono_compile_materialize_vv) >> simp[]) >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es` by
    (fs[Once body_expr_full_ok_def] >> metis_tac[]) >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then drule_all >>
  disch_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ P _` >>
  drule (Q.INST [`Q'` |-> `\H res ee G tn t. P H res ee G tn t /\ ~t.vs_halted`,
      `R'` |-> `\H res ee gt r. expr_exit res r`] gas_outcome_full_post_path) >>
  disch_then (qspec_then `P` mp_tac) >>
  (impl_tac
   >- (simp[] >> rpt strip_tac >>
       drule fragGasOriginPtrTheory.gas_origin_ptr_path_projections >> strip_tac >>
       metis_tac[fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted])) >>
  strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ P _` kall_tac >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_bind_all >>
  conj_tac >- simp[vyperStorageTraceTheory.storage_trace_frame_read_result] >>
  conj_tac
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_result >>
      goal_assum (drule_at Any) >> fs[]) >>
  conj_tac
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_result >>
      first_assum ACCEPT_TAC) >>
  conj_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  qexists `\H res ee G tn t. P H res ee G tn t /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_mono >> goal_assum (drule_at Any) >> simp[] >>
      rpt strip_tac >> Cases_on `res`
      >- (qpat_x_assum `expr_exit _ _` mp_tac >>
          simp[exprSimDefsTheory.expr_exit_def]) >>
      qexists `y` >> simp[] >>
      qpat_x_assum `expr_exit _ _` mp_tac >>
      simp[stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt gen_tac >> strip_tac >>
  Q.UNABBREV_TAC `P` >> BETA_TAC >>
  disj1_tac >>
  qpat_x_assum `storage_trace_domain cx st0 _` mp_tac >>
  rename1 `storage_trace_domain cx st0 ee.storage_trace` >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
      ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
    (mp_tac o BETA_RULE o Q.SPEC `storage_trace_horizon ee.storage_trace`) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  qexists `tv` >> simp[] >>
  `expr_body_pre cenv cx env e
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
      (INL tv,ee with gas_obs := [])` by
    (qpat_assum `!tail. eval_expr cx e _ = _`
       (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE [APPEND_NIL]))) >>
  `expr_sim_inv cenv cx env ee` by
    (drule_all exprSimSourceTheory.expr_body_pre_eval_result >> simp[]) >>
  `?rty. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty` by
    metis_tac[exprSimHypsTheory.post_type_evaluates] >>
  `!rty. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
      ~is_word_type (post_value_type cenv e) ==>
      type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rty /\
      type_memory_size rty < 2**64` by
    metis_tac[aggregateEvaluatedLayoutTheory.body_post_type_allocation_bound] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post H ctx func cenv cx e es sa sm s0 ee tv sv t /\
      ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
       (mp_tac o BETA_RULE o Q.SPEC `H`) >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  `!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v` by
    (rpt strip_tac >>
     `(do r <- eval_expr cx e; read_result cx r od)
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
        (INL v,ee with gas_obs := [])` by
       (simp[vyperStateTheory.bind_def] >>
        metis_tac[exprSimMemorySourceTheory.read_result_gas_obs]) >>
     drule_at (Pos last) exprSimHypsTheory.memory_rhs_read_post_typed >>
     disch_then (qspecl_then [`cenv`,`env`] mp_tac) >>
     simp[] >>
     fs[vyperTypeExprSoundnessTheory.value_runtime_typed_def,
        expr_body_pre_def, expr_sim_inv_def,
        vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def]) >>
  `type_memory_bytes cenv (lowered_value_type cenv e) < dimword (:256)` by
    (`type_memory_bytes cenv (lowered_value_type cenv e) <=
        type_memory_bytes cenv (expr_type e)` by
       metis_tac[exprSimHypsTheory.expr_body_pre_lowered_fits,
         abiEncodeArgsCaseTheory.abi_args_fits_memory_bytes] >>
     `type_memory_bytes cenv (expr_type e) < 2**64` by
       (fs[expr_body_pre_def] >>
        drule exprSimHypsTheory.alloc_limits_expr_type_alloc_ok >>
        simp[allocLimitsTheory.type_alloc_ok_def]) >>
     fs[wordsTheory.dimword_def] >> decide_tac) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
   sm.cs_next_var <= mid.cs_next_var /\ sm.cs_next_id <= mid.cs_next_id` by
    fs[exprLoweringPropsTheory.ci_mono_def] >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `!x. vv_operand sv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 exprOperandVarTheory.compiler_compile_var] >>
  `(is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e))` by
    metis_tac[exprSimIfExpWidenedPhysicalTypeTheory.post_value_type_nonword] >>
  drule_all extcall_materialize_alloc_unwrap_joint >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] strip_assume_tac) >>
  drule_all extcall_materialize_unwrap_destination >> strip_tac >>
  `~is_word_type (post_value_type cenv e)` by metis_tac[] >>
  `ptr_buf_ok cenv e src G' z` by metis_tac[] >>
  `value_has_type rty v` by metis_tac[] >>
  `(do r <- eval_expr cx e; read_result cx r od)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
      (INL v,ee with gas_obs := [])` by
    (simp[vyperStateTheory.bind_def] >>
     metis_tac[exprSimMemorySourceTheory.read_result_gas_obs]) >>
  drule_all abiEncodeArgsCaseTheory.abi_args_success_ready >> simp[] >> strip_tac >>
  `ptr_mem_ok cx (post_value_type cenv e) v src G' tn' z /\
   op_taint tn' src = {}` by fs[bodyPtrDefsTheory.ptr_val_ok_def] >>
  `arg_type_fits (lowered_value_type cenv e) (expr_type e)` by
    metis_tac[exprSimHypsTheory.expr_body_pre_lowered_fits] >>
  `ptr_mem_ok cx (lowered_value_type cenv e) v src G' tn' z` by
    (drule_all abiEncodeMaterializeTheory.materialize_post_lowered_classify >>
     strip_tac >- gvs[] >>
     irule bodyPtrIfExpMemoryTransportTheory.ptr_mem_ok_bytestring_transport >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `expr_post (storage_trace_horizon ee.storage_trace) ctx func cenv cx e
      es sa sc s0 ee v src z /\
   ghost_inv_at (DF (storage_trace_horizon ee.storage_trace)) lo d cenv cx ee G' tn' z` by
    metis_tac[] >>
  `?sw. eval_operand src z = SOME sw` by
    metis_tac[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def] >>
  `!x. src = Var x ==> not_fresh_at sc x` by
    (rpt strip_tac >> irule exprOperandVarTheory.compiler_unwrap_value_var >>
     qexistsl_tac [`cenv`,`src`,`mid`,`sv`] >> simp[] >>
     `!x. vv_operand sv = Var x ==> not_fresh_at mid x` by
       metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
     Cases_on `sv` >> fs[vv_operand_def]) >>
  `not_fresh_at sc p` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by
    metis_tac[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `op_taint tn' (Var p) = {}` by
    metis_tac[bodyPtrDefsTheory.ptr_covers_def] >>
  `(type_memory_size tv' <> 0 ==>
     ?x. src = Var x /\ ptr_covers G' tn' x z (type_memory_size tv') /\
       w2n sw + type_memory_size tv' <= z.vs_alloca_next)` by
    (strip_tac >>
     `?x b sz. src = Var x /\ FLOOKUP G' x = SOME (b,sz) /\
       b <= w2n sw /\ w2n sw + type_memory_size tv' <= b + sz` by
       metis_tac[bodyPtrDefsTheory.ptr_buf_ok_def] >>
     qexists_tac `x` >> conj_tac >- simp[] >> reverse conj_tac
     >- (qpat_x_assum `~is_word_type _ ==> !rt w. _` mp_tac >>
         simp[]) >>
     simp[bodyPtrDefsTheory.ptr_covers_def] >>
     conj_tac >- metis_tac[] >>
     qexists_tac `sw` >> fs[eval_operand_def]) >>
  `alloca_inv z` by
    metis_tac[loweringPostsTheory.expr_post_def,
      exprLoweringPropsTheory.stmt_state_rel_def] >>
  `w2n w + type_memory_size tv' <= z.vs_alloca_next` by
    metis_tac[venomMemDefsTheory.alloca_inv_def,
      venomMemDefsTheory.alloca_next_valid_def] >>
  `~z.vs_halted` by
    (qpat_x_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (t,_,_) _ (OK z,_,_)`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     simp[] >> strip_tac >>
     drule fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec >>
     simp[fragExecTheory.exit_result_def]) >>
  `~is_word_type (lowered_value_type cenv e)` by
    (drule_all abiEncodeMaterializeTheory.materialize_post_lowered_classify >>
     strip_tac >- metis_tac[] >>
     metis_tac[eventTopicValuePropsTheory.bytestring_type_not_word]) >>
  `compile_store_memory cenv src (Var p) (lowered_value_type cenv e)
      (lowered_value_type cenv e) sc = ((),sb)` by metis_tac[] >>
  `(type_memory_size tv' <> 0 ==>
      ptr_covers G' tn' p z (type_memory_size tv') /\
      w2n w + type_memory_size tv' <= z.vs_alloca_next)` by metis_tac[] >>
  drule extcallReturnDefaultMemoryJointTheory.return_default_memory_store_capacity_joint >>
  disch_then (drule_at (Pat `ptr_mem_ok _ _ _ _ _ _ _`)) >>
  simp[] >>
  disch_then (qspecl_then [`lo`, `func`, `gas_explicit_sites ctx shadow_ctx`,
                          `ctx`, `PG`] mp_tac) >>
  (impl_tac >- (simp[] >>
    qpat_x_assum `type_memory_size tv' <> 0 ==> ?x. _` mp_tac >>
    simp[arithmeticTheory.ADD_COMM])) >>
  disch_then (qx_choose_then `u` (qx_choose_then `Gf`
    (qx_choose_then `tm` strip_assume_tac))) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl [`Gf`, `ee`, `INL v`, `u`, `tm`] >>
  conj_tac >- (drule exprSimMemorySourceTheory.read_result_gas_obs >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  conj_tac >- (
    qpat_x_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> gas_origin_ptr_path _ (t,G1,tn1) _ (OK z,G',tn')` drule >>
    strip_tac >>
    qpat_x_assum `!D. gas_origin_ptr_path _ (z,G',tn') _ _` (qspec_then `DF H` assume_tac) >>
    qpat_x_assum `gas_origin_ptr_path _ (t,G1,tn1) _ (OK z,G',tn')`
      (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
    disch_then (qspecl_then [`z`, `G'`, `tn'`, `[]`, `OK u`, `Gf`, `tm`] mp_tac) >>
    simp[]) >>
  simp[] >>
  `u.vs_allocas = z.vs_allocas /\ u.vs_alloca_next = z.vs_alloca_next /\
   u.vs_call_ctx = z.vs_call_ctx /\ u.vs_accounts = z.vs_accounts /\
   u.vs_transient = z.vs_transient /\ u.vs_immutables = z.vs_immutables /\
   u.vs_current_bb = z.vs_current_bb` by
    (qpat_x_assum `u with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|> = z` mp_tac >>
     simp[venom_state_component_equality]) >>
  `ptr_covers Gf tm p u (type_memory_size tv')` by
    (qpat_x_assum `ptr_covers G' tn' p z _` mp_tac >>
     qpat_x_assum `!x. not_fresh_at sc x ==> _` (qspec_then `p` assume_tac) >>
     simp[ptr_covers_def] >> metis_tac[]) >>
  `ptr_mem_ok cx (lowered_value_type cenv e) v (Var p) Gf tm u` by
    (`val_store_size tv' v <= type_memory_size tv'` by
       metis_tac[exprSimPropsTheory.val_store_size_le] >>
     qpat_x_assum `ptr_covers Gf tm p u _` mp_tac >>
     simp[ptr_mem_ok_def, ptr_covers_def, eval_operand_def] >>
     strip_tac >> rpt strip_tac >>
     qpat_assum `FLOOKUP HG p = SOME _` (irule_at Any) >> decide_tac) >>
  `ptr_val_ok cx (lowered_value_type cenv e) v (Var p) Gf tm u` by
    (simp[ptr_val_ok_def] >> metis_tac[]) >>
  `ptr_buf_ok cenv e (Var p) Gf u` by
    (qpat_x_assum `ptr_covers Gf tm p u _` mp_tac >>
     simp[ptr_covers_def, ptr_buf_ok_def, eval_operand_def]) >>
  `!w'. eval_operand (Var p) u = SOME w' /\ type_memory_size tv' <> 0 ==>
     type_memory_size tv' + w2n w' <= u.vs_alloca_next` by
    simp[eval_operand_def] >>
  `not_fresh_at sb p` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
  simp[] >>
  `typed_copy_state_frame sc (w2n w) (type_memory_size tv') z u` by
    (simp[typed_copy_state_frame_def, typed_copy_frame_def] >>
     conj_tac >-
       (qpat_x_assum `u with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|> = z` mp_tac >>
        simp[venom_state_component_equality]) >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> gas_origin_ptr_path _ (a,HG,tt) _ _ /\ _` drule >>
  strip_tac >>
  `alloca_history func u` by
    (qpat_x_assum `!D. gas_origin_ptr_path _ (z,G',tn') _ _`
       (qspec_then `DF H` mp_tac) >>
     metis_tac[bodyFullPathHistoryTheory.body_full_path_alloca_history]) >>
  `stmt_state_rel H ctx func cenv cx ee z /\
   storage_well_formed_on cx ee (FST H) /\
   pure_frame cenv func es sa s0 z` by
    (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >> simp[]) >>
  simp[] >>
  `local_ptrs_reserved cenv mid /\ local_ptrs_reserved cenv sc /\
   sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var,
               arithmeticTheory.LESS_EQ_TRANS]) >>
  `!name b len. local_region cenv ee.scopes z name b len ==>
     regions_disjoint (w2n w) (type_memory_size tv') b len` by
    (rpt strip_tac >>
     `local_region cenv ee.scopes a name b len` by
       (qpat_assum `local_ptrs_reserved cenv mid`
          (mp_then Any mp_tac exprSimCopyTheory.copy_buffer_local_region_frame) >>
        disch_then (qspecl_then [`a`, `z`, `ee.scopes`, `name`, `b`, `len`] mp_tac) >>
        (impl_tac >- (rpt strip_tac >>
          qpat_x_assum `!x. not_fresh_at mid x ==> _` drule >> simp[])) >>
        simp[]) >> metis_tac[]) >>
  `?ai. MEM ai (fn_insts func) /\ ai.inst_opcode = ALLOCA /\
     FLOOKUP z.vs_allocas ai.inst_id = SOME (w2n w,type_memory_size tv')` by
    (`stmt_state_rel H ctx func cenv cx ee t` by
       metis_tac[loweringPostsTheory.vv_post_def] >>
     drule_all bodyPtrIfExpAllocCompilerTheory.compile_alloc_buffer_raw_step >>
     strip_tac >>
     qexists_tac `mk_inst sm.cs_next_id ALLOCA
       [Lit (n2w (type_memory_bytes cenv (lowered_value_type cenv e)))] [out]` >>
     simp[mk_inst_def]) >>
  `stmt_state_rel H ctx func cenv cx ee u` by
    (irule placeStoreDynPrepareTheory.place_typed_copy_alloca_state_frame >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`type_memory_size tv'`, `sc`] >> simp[] >>
     metis_tac[placeStoreDynPrepareTheory.place_typed_copy_alloca_state_frame]) >>
  simp[] >>
  conj_tac >-
    (irule (iffRL vyperStorageFootprintTheory.storage_well_formed_on_backends) >>
     qexists_tac `ee` >> simp[]) >>
  `return_buf_frame d cenv sb u` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[] >>
     reverse conj_tac >- (fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
     rpt strip_tac >>
     `not_fresh_at sm x /\ not_fresh_at mid x /\ not_fresh_at sc x` by
       metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
     qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     metis_tac[]) >>
  `ee with <|outcomes := NONE; gas_obs := []; storage_trace := []|> =
   es with <|outcomes := NONE; gas_obs := []; storage_trace := []|>` by
    (drule_all bodyIntCallJointPureSourceTheory.effect_free_eval_expr_frame >> simp[]) >>
  simp[] >>
  `!name b len. local_region cenv es.scopes s0 name b len ==>
     regions_disjoint (w2n w) (type_memory_size tv') b len` by
    (rpt strip_tac >>
     `local_region cenv ee.scopes z name b len` by
       (irule exprSimPropsTheory.local_region_frame_fwd >>
        qexistsl_tac [`s0`, `sa`, `es.scopes`] >> simp[] >>
        qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
          (strip_assume_tac o REWRITE_RULE [expr_post_def]) >> simp[]) >>
     metis_tac[]) >>
  `pure_frame cenv func es sa s0 u` by
    (irule exprSimPropsTheory.pure_frame_buffer_tail >>
     qexistsl_tac [`w2n w`, `type_memory_size tv'`,
       `mk_inst sm.cs_next_id ALLOCA
         [Lit (n2w (type_memory_bytes cenv (lowered_value_type cenv e)))] [p]`,
       `z`] >>
     simp[mk_inst_def] >>
     `stmt_state_rel H ctx func cenv cx ee t` by
       metis_tac[loweringPostsTheory.vv_post_def] >>
     drule_all bodyPtrIfExpAllocCompilerTheory.compile_alloc_buffer_raw_step >>
     strip_tac >>
     `out = p` by
       (qpat_x_assum `buf.buf_operand = Var out` mp_tac >> simp[]) >>
     conj_tac >-
       (rpt strip_tac >>
        qpat_x_assum `!name b len. local_region cenv es.scopes s0 name b len ==> _` drule >> simp[]) >>
     conj_tac >-
       (rpt strip_tac >>
        qpat_x_assum `!off len. _ \/ _ ==> mem_bytes_at _ _ u.vs_memory = _` irule >>
        fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
     qpat_x_assum `MEM (mk_inst sm.cs_next_id ALLOCA _ _) _` mp_tac >>
     simp[mk_inst_def]) >>
  simp[] >>
  `lo <= w2n w` by
    (fs[ptrDisciplineTheory.allocas_from_def] >> metis_tac[]) >>
  `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
     aid < sa.cs_next_id ==> off+sz <= w2n w \/
       w2n w + type_memory_size tv' <= off` by
    (rpt strip_tac >>
     `FLOOKUP z.vs_allocas aid = SOME (off,sz)` by
       metis_tac[loweringPostsTheory.expr_post_def] >>
     `aid <> sm.cs_next_id` by decide_tac >>
     qpat_x_assum `alloca_inv z` mp_tac >>
     simp[venomMemDefsTheory.alloca_inv_def,
          venomMemDefsTheory.allocas_non_overlapping_def] >>
     strip_tac >>
     qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _`
       (qspecl_then [`aid`, `sm.cs_next_id`, `off`, `sz`,
                     `w2n w`, `type_memory_size tv'`] mp_tac) >> simp[]) >>
  `!name entry q sz. lookup_scopes name ee.scopes = SOME entry /\
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var q) sz) ==>
     val_wf entry.type entry.value /\
     (!w' i. lookup_var q z = SOME w' /\ w2n w' <= i /\
       i < w2n w' + val_footprint entry.type entry.value ==>
       ~(w2n w <= i /\ i < w2n w + type_memory_size tv'))` by
    (rpt gen_tac >> strip_tac >>
     `?w'. lookup_var q z = SOME w' /\ val_wf entry.type entry.value` by
       (qpat_assum `stmt_state_rel H ctx func cenv cx ee z` mp_tac >>
        pure_rewrite_tac[exprLoweringPropsTheory.stmt_state_rel_def,
             loweringStateRelDefsTheory.state_rel_def,
             loweringStateRelDefsTheory.local_ptrs_rel_def] >>
        strip_tac >> qpat_x_assum `!name entry p sz. _ ==> ?w. _` drule_all >>
        metis_tac[]) >>
     simp[] >>
     drule_all exprSimPtrLiteralBufferTheory.literal_ptr_local_footprint_exterior >>
     simp[arithmeticTheory.ADD_COMM]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x)` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `ghost_inv_at (DF H) lo d cenv cx ee Gf tm u /\
   ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tm` by
    (`ghost_inv_at (DF H) lo d cenv cx ee Gf tm u /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tm /\
      (!rt v p. (rt,v,p) IN {} ==>
        !mem. mem_agree_outside tm.t_mem u.vs_memory mem ==>
          val_in_memory rt v p mem)` suffices_by simp[] >>
     irule extcall_slot_protected_resources >>
     qexistsl_tac [`G'`, `w2n w`, `type_memory_size tv'`, `z`, `sc`, `tn'`] >>
     simp[] >>
     conj_tac >-
       (rpt strip_tac >>
        qpat_x_assum `!name b len. local_region cenv es.scopes s0 name b len ==> _` drule >>
        simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
     conj_tac >-
       (rpt gen_tac >> strip_tac >>
        qpat_x_assum `!name entry q sz. _` drule_all >>
        simp[arithmeticTheory.ADD_COMM]) >>
     conj_tac >-
       (rpt strip_tac >>
        qpat_x_assum `!aid off sz. _ ==> _` drule_all >> decide_tac) >>
     rpt strip_tac >>
     qpat_x_assum `!i. i < w2n w \/ _ ==> _` irule >> decide_tac) >>
  qpat_x_assum `ghost_inv_at (DF H) lo d cenv cx ee Gf tm u` mp_tac >>
  simp[bodyPtrDefsTheory.ghost_inv_at_def] >>
  strip_tac >> simp[]
QED

Theorem extcall_tuple_alloc_entry:
  compile_alloc_buffer mem sf = (aa,sc) /\ fn_has_code sf sc func /\
  stmt_state_rel H ctx func cenv cx ee u /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sa /\
  mem < dimword(:256) /\
  sa.cs_next_id <= sb_saved.cs_next_id /\ sb_saved.cs_next_id <= sf.cs_next_id /\
  sa.cs_next_var <= sf.cs_next_var /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!k a n. FLOOKUP s0.vs_allocas k = SOME(a,n) ==>
    FLOOKUP u.vs_allocas k = SOME(a,n)) /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
    lookup_var x u = SOME w) ==>
  ?r w. run_inst_seq (emitted_insts sf sc) u = OK r /\
    stmt_state_rel H ctx func cenv cx ee r /\
    eval_operand aa.buf_operand r = SOME w /\
    FLOOKUP r.vs_allocas sf.cs_next_id = SOME(w2n w,mem) /\
    w2n w + mem < dimword(:256) /\ r.vs_memory = u.vs_memory /\
    sf.cs_next_id < sc.cs_next_id /\
    (!x. not_fresh_at sf x ==> lookup_var x r = lookup_var x u) /\
    (!k entry. FLOOKUP u.vs_allocas k = SOME entry ==>
      FLOOKUP r.vs_allocas k = SOME entry) /\
    (!k a n. k < sf.cs_next_id /\ FLOOKUP u.vs_allocas k = SOME(a,n) ==>
      regions_disjoint (w2n w) mem a n) /\
    (!name a n. local_region cenv ee.scopes r name a n ==>
      regions_disjoint (w2n w) mem a n) /\
    (?p. aa.buf_operand = Var p /\ not_fresh_at sc p) /\
    sb_saved.cs_next_id <= sf.cs_next_id /\
    (!k a n i. FLOOKUP s0.vs_allocas k = SOME(a,n) /\ k < sa.cs_next_id /\
      a <= i /\ i < a+n ==> ~(w2n w <= i /\ i < w2n w+mem)) /\
    (!name a n i. local_region cenv es.scopes s0 name a n /\
      a <= i /\ i < a+n ==> ~(w2n w <= i /\ i < w2n w+mem))
Proof
  strip_tac >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  drule_all exprSimAllocTheory.literal_alloc_buffer_run >>
  disch_then (qx_choose_then `r` (qx_choose_then `w` strip_assume_tac)) >>
  qexistsl_tac [`r`,`w`] >> simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >>
      `FLOOKUP u.vs_allocas k = SOME(a,n)` by metis_tac[] >>
      `k < sf.cs_next_id` by decide_tac >>
      `regions_disjoint (w2n w) mem a n` by metis_tac[] >>
      gvs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  rpt strip_tac >>
  `local_region cenv ee.scopes r name a n` by
    (irule exprSimPropsTheory.local_region_frame_fwd >>
     qexistsl_tac [`s0`,`sa`,`es.scopes`] >> simp[] >>
     rpt strip_tac >>
     `not_fresh_at sf x` by
       (irule loweringShapeDefsTheory.not_fresh_at_mono >>
        qexists_tac `sa` >> simp[]) >> metis_tac[]) >>
  `regions_disjoint (w2n w) mem a n` by metis_tac[] >>
  gvs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

(* Saved compiler provenance is fixed; only the endpoint is transported. *)
Theorem extcall_saved_resource_frame:
  let saved = \H s G tn (e,sv) v.
    ((?tag op0. sv = StackValue tag op0) \/
     (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
       ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
     (?p si sm0. sv = LocatedValue (lowered_value_type cenv e) p /\
       ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
       lowered_value_type cenv e = expr_type e /\
       compile_expr cenv (expr_type e) e si = (sv,sm0) /\
       sa_saved.cs_next_var <= si.cs_next_var /\ sa_saved.cs_next_id <= si.cs_next_id /\
       sm0.cs_next_var <= sb_saved.cs_next_var /\ sm0.cs_next_id <= sb_saved.cs_next_id)) /\
    (?raw. read_result cx raw ee = (INL v,ee) /\
      vv_holds cenv cx (lowered_value_type cenv e) raw sv ee s /\
      vv_at cenv cx (lowered_value_type cenv e) sa_saved sb_saved ee raw sv s /\
      ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn s /\
      vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee raw sv s) /\
    vv_storage_live H cx sv ee s /\
    (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
      ptr_buf_ok cenv e op G s) /\
    (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e p.ptr_operand G s) /\
    (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
      !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
        eval_operand (vv_operand sv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt v (w2n w) mem)) in
  saved H s G tn (e,sv) v /\
  eval_operand (vv_operand sv) t = eval_operand (vv_operand sv) s /\
  op_taint tn' (vv_operand sv) = op_taint tn (vv_operand sv) /\
  op_prov G' (vv_operand sv) = op_prov G (vv_operand sv) /\
  (!x. vv_operand sv = Var x ==> FLOOKUP G' x = FLOOKUP G x) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry) /\
  (!name b sz. local_region cenv ee.scopes s name b sz <=>
    local_region cenv ee.scopes t name b sz) /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  contract_storage t = contract_storage s /\
  contract_transient t = contract_transient s /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
  (!rt. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt ==>
    val_wf rt v) /\
  (!rt w. ~is_word_type (lowered_value_type cenv e) /\
    (vv_location sv = NONE \/ vv_location sv = SOME LocMemory \/
      cenv.ce_is_ctor /\ vv_location sv = SOME LocCode) /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
    eval_operand (vv_operand sv) s = SOME w ==>
    mem_bytes_at (w2n w) (val_footprint rt v) t.vs_memory =
      mem_bytes_at (w2n w) (val_footprint rt v) s.vs_memory /\
    (!i. w2n w <= i /\ i < w2n w + val_footprint rt v /\ i IN tn'.t_mem ==>
      i IN tn.t_mem)) ==>
  saved H t G' tn' (e,sv) v
Proof
  simp_tac (srw_ss()) [LET_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?raw. _` strip_assume_tac >>
  `vv_at cenv cx (lowered_value_type cenv e) sa_saved sb_saved ee raw sv t` by
    (irule abiEncodeMaterializeTheory.materialize_vv_at_alloc_frame >>
     qexistsl_tac [`s`,`sb_saved`] >> simp[]) >>
  `vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee raw sv t` by
    (Cases_on `sv` >>
     gvs[exprSimMemDefsTheory.vv_store_bound_def, vv_operand_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t` by
    (Cases_on `sv`
     >- (gvs[vv_holds_def, expr_val_rel_def, vv_operand_def, vv_location_def] >>
         rpt strip_tac >> Cases_on `is_word_type (lowered_value_type cenv e)`
         >- metis_tac[] >>
         simp[] >> irule exprSimPropsTheory.val_in_memory_footprint_agree >>
         conj_tac >- metis_tac[] >> qexists_tac `s.vs_memory` >> metis_tac[]) >>
     rename1 `LocatedValue tag p` >>
     `tag = lowered_value_type cenv e /\ ~is_word_type (lowered_value_type cenv e)` by
       (qpat_assum `(?tag op0. _) \/ _` mp_tac >> simp[] >> gvs[]) >>
     qpat_x_assum `(?tag op0. _) \/ _` kall_tac >>
     Cases_on `p.ptr_location = LocMemory`
     >- (gvs[vv_holds_def, vv_operand_def, vv_location_def] >>
         rpt strip_tac >> irule exprSimPropsTheory.val_in_memory_footprint_agree >>
         conj_tac >- metis_tac[] >> qexists_tac `s.vs_memory` >> metis_tac[]) >>
     Cases_on `p.ptr_location` >>
     gvs[vv_holds_def, vv_operand_def, storage_holds_def, immutable_holds_def] >>
     metis_tac[]) >>
  `ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G' tn' t` by
    (Cases_on `sv`
     >- (gvs[ptr_vv_ok_def, vv_operand_def, vv_location_def] >>
         irule logValueFramePtrTheory.ptr_val_ok_footprint_frame >>
         qexistsl_tac [`G`,`s`,`tn`] >> simp[] >> metis_tac[]) >>
     rename1 `LocatedValue tag p` >>
     `~is_word_type (lowered_value_type cenv e)` by
       (qpat_assum `(?tag op0. _) \/ _` mp_tac >> simp[] >> gvs[]) >>
     qpat_x_assum `(?tag op0. _) \/ _` kall_tac >>
     Cases_on `p.ptr_location = LocMemory`
     >- (`ptr_val_ok cx (lowered_value_type cenv e) v p.ptr_operand G tn s` by
           gvs[ptr_vv_ok_def, ptr_val_ok_def] >>
         `ptr_val_ok cx (lowered_value_type cenv e) v p.ptr_operand G' tn' t` by
           (irule logValueFramePtrTheory.ptr_val_ok_footprint_frame >>
            qexistsl_tac [`G`,`s`,`tn`] >>
            gvs[vv_operand_def, vv_location_def] >> metis_tac[]) >>
         gvs[ptr_vv_ok_def, ptr_val_ok_def]) >>
     gvs[ptr_vv_ok_def, vv_operand_def] >>
     gvs[contract_storage_def, contract_transient_def,
         vfmStateTheory.lookup_account_def] >> metis_tac[]) >>
  conj_tac >- (qexists_tac `raw` >> simp[]) >>
  conj_tac
  >- (Cases_on `sv` >> gvs[vv_storage_live_def, vv_operand_def]) >>
  conj_tac
  >- (rpt strip_tac >> irule logValueFramePtrTheory.ptr_buf_ok_frame >>
      qexistsl_tac [`G`,`s`] >> gvs[vv_operand_def]) >>
  conj_tac
  >- (rpt strip_tac >> irule logValueFramePtrTheory.ptr_buf_ok_frame >>
      qexistsl_tac [`G`,`s`] >> gvs[vv_operand_def]) >>
  strip_tac >>
  `~is_word_type (lowered_value_type cenv e)` by
    (qpat_x_assum `(?tag op0. _) \/ _` mp_tac >>
     Cases_on `sv` >> gvs[vv_location_def] >> rpt strip_tac >> gvs[]) >>
  rpt strip_tac >>
  irule logValueFramePtrTheory.robust_val_in_memory_footprint_frame >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`s.vs_memory`,`t.vs_memory`,`tn.t_mem`,`tn'.t_mem`] >>
  metis_tac[]
QED

Theorem extcall_saved_resources_frame:
  let saved = \H s G tn (e,sv) v.
    ((?tag op0. sv = StackValue tag op0) \/
     (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
       ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
     (?p si sm0. sv = LocatedValue (lowered_value_type cenv e) p /\
       ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
       lowered_value_type cenv e = expr_type e /\
       compile_expr cenv (expr_type e) e si = (sv,sm0) /\
       sa_saved.cs_next_var <= si.cs_next_var /\ sa_saved.cs_next_id <= si.cs_next_id /\
       sm0.cs_next_var <= sb_saved.cs_next_var /\ sm0.cs_next_id <= sb_saved.cs_next_id)) /\
    (?raw. read_result cx raw ee = (INL v,ee) /\
      vv_holds cenv cx (lowered_value_type cenv e) raw sv ee s /\
      vv_at cenv cx (lowered_value_type cenv e) sa_saved sb_saved ee raw sv s /\
      ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn s /\
      vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee raw sv s) /\
    vv_storage_live H cx sv ee s /\
    (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
      ptr_buf_ok cenv e op G s) /\
    (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e p.ptr_operand G s) /\
    (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
      !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
        eval_operand (vv_operand sv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt v (w2n w) mem)) in
  LIST_REL (saved H s G tn) (ZIP (xs,svs)) vs /\ LENGTH xs = LENGTH svs /\
  LIST_REL (\e v. ?rt.
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
    value_has_type rt v /\ val_wf rt v /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size rt /\
    type_memory_size rt < 2**64 /\
    (is_word_type (lowered_value_type cenv e) ==> type_memory_size rt = 32)) xs vs /\
  (!e sv v. MEM ((e,sv),v) (ZIP (ZIP (xs,svs),vs)) ==>
    eval_operand (vv_operand sv) t = eval_operand (vv_operand sv) s /\
    op_taint tn' (vv_operand sv) = op_taint tn (vv_operand sv) /\
    op_prov G' (vv_operand sv) = op_prov G (vv_operand sv) /\
    (!x. vv_operand sv = Var x ==> FLOOKUP G' x = FLOOKUP G x) /\
    (!rt w. ~is_word_type (lowered_value_type cenv e) /\
      (vv_location sv = NONE \/ vv_location sv = SOME LocMemory \/
        cenv.ce_is_ctor /\ vv_location sv = SOME LocCode) /\
      evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
      eval_operand (vv_operand sv) s = SOME w ==>
      mem_bytes_at (w2n w) (val_footprint rt v) t.vs_memory =
        mem_bytes_at (w2n w) (val_footprint rt v) s.vs_memory /\
      (!i. w2n w <= i /\ i < w2n w + val_footprint rt v /\ i IN tn'.t_mem ==>
        i IN tn.t_mem))) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry) /\
  (!name b sz. local_region cenv ee.scopes s name b sz <=>
    local_region cenv ee.scopes t name b sz) /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  contract_storage t = contract_storage s /\
  contract_transient t = contract_transient s /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans ==>
  LIST_REL (saved H t G' tn') (ZIP (xs,svs)) vs
Proof
  simp_tac (srw_ss()) [LET_THM] >>
  map_every qid_spec_tac [`svs`,`vs`] >>
  Induct_on `xs` >- simp[] >> pop_assum (mk_asm "saved-ih") >> rpt gen_tac >>
  namedCases_on `vs` ["", "v vs0"] >- simp[] >>
  namedCases_on `svs` ["", "sv svs0"] >- simp[] >>
  simp_tac (srw_ss()) [ZIP, LIST_REL_def, LENGTH, MEM] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac
  >- (asm_x "saved-ih" kall_tac >>
      qpat_assum `!e sv v. _ \/ MEM _ _ ==> _`
        (qspecl_then [`h`,`sv`,`v`] mp_tac) >> simp[] >> strip_tac >>
      match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM] extcall_saved_resource_frame) >>
      simp[] >> conj_tac
      >- (qpat_x_assum `?rt. _` strip_assume_tac >> rpt strip_tac >> gvs[]) >>
      first_assum MATCH_ACCEPT_TAC) >>
  asm_x "saved-ih" irule >> simp[] >> metis_tac[]
QED

(* The staging invariant keeps original positional compiler witnesses.  The
   let-bound predicates below are local notation, not new logical constants. *)
Theorem extcall_saved_slot_separation:
  alloca_inv s /\ FLOOKUP s.vs_allocas aid = SOME (b,cap) /\
  sb_saved.cs_next_id <= aid /\ off+n <= cap /\
  (!name a z. local_region cenv ee.scopes s name a z ==>
    b+cap <= a \/ a+z <= b) /\
  (val_footprint rt v = 0 \/
   (?k a z. FLOOKUP s.vs_allocas k = SOME (a,z) /\
     k < sb_saved.cs_next_id /\ a <= p /\ p+val_footprint rt v <= a+z) \/
   (?name a z. local_region cenv ee.scopes s name a z /\
     a <= p /\ p+val_footprint rt v <= a+z)) ==>
  !i. p <= i /\ i < p+val_footprint rt v ==>
    ~(b+off <= i /\ i < b+off+n)
Proof
  strip_tac
  >- simp[]
  >- (`k <> aid` by decide_tac >>
      `a+z <= b \/ b+cap <= a` by
        metis_tac[venomMemDefsTheory.alloca_inv_def,
          venomMemDefsTheory.allocas_non_overlapping_def] >>
      rpt strip_tac >> decide_tac) >>
  `b+cap <= a \/ a+z <= b` by metis_tac[] >>
  rpt strip_tac >> decide_tac
QED

Theorem extcall_request_full:
  !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx env ty ann
   is_static skip fname arg_types ret_type opts args dflt es.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env
      (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
         args dflt) es /\
    (!s'' target t nargs s'3' results t'.
       eval_exprs cx (TAKE 1 args) s'' = (INL target,t) /\
       nargs = LENGTH arg_types /\
       eval_exprs cx (TAKE nargs (DROP 1 args)) s'3' =
         (INL results,t') ==>
       body_exprs_full_ok cx (DROP (1 + nargs) args)) /\
    (!s'' target t nargs.
       eval_exprs cx (TAKE 1 args) s'' = (INL target,t) /\
       nargs = LENGTH arg_types ==>
       body_exprs_full_ok cx (TAKE nargs (DROP 1 args))) /\
    body_exprs_full_ok cx (TAKE 1 args) ==>
    !st0 sa sb shadow_sa shadow_sb vv s0 G0 tn0 Q.
      compile_expr cenv ty
        (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
           args dflt) sa = (vv, sb) /\
      compile_expr cenv ty
        (gas_shadow_expr
           (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
              args dflt)) shadow_sa = (vv, shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\
      fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible
        (eval_expr cx
           (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
              args dflt)) expr_vv_res_ok es /\
      return_buf_frame d cenv sa s0 /\
      alloca_history func s0 /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!sp sr u result_op addr_op value_op gas_op buf_op call_offset call_len
        has_default default_op default_ty target_v rest target value_opt
        calldata ee t G tn.
         (* the lowered call step, sp to sr *)
         comp_ignore_bind
           (if ret_type = NoneT /\ ~skip then compile_extcodesize_check addr_op
            else comp_return ())
           (comp_bind
              (if is_static then
                 emit_op STATICCALL
                   [gas_op; addr_op; call_offset; call_len; buf_op;
                    Lit (n2w (abi_size_bound cenv.ce_struct_fields
                       (if needs_external_call_wrap ret_type
                        then TupleT [ret_type] else ret_type)))]
               else
                 emit_op CALL
                   [gas_op; addr_op; value_op; call_offset; call_len; buf_op;
                    Lit (n2w (abi_size_bound cenv.ce_struct_fields
                       (if needs_external_call_wrap ret_type
                        then TupleT [ret_type] else ret_type)))])
           (\success. comp_bind (fresh_label "extcall_fail") (\fail_lbl.
            comp_bind (fresh_label "extcall_cont") (\cont_lbl.
            comp_ignore_bind
              (emit_inst JNZ [success; Label cont_lbl; Label fail_lbl] [])
            (comp_ignore_bind (new_block fail_lbl)
            (comp_bind (emit_op RETURNDATASIZE []) (\rds.
            comp_bind (compile_alloc_buffer 0) (\fail_buf.
            comp_ignore_bind
              (emit_void RETURNDATACOPY [fail_buf.buf_operand; Lit 0w; rds])
            (comp_ignore_bind (emit_inst REVERT [fail_buf.buf_operand; rds] [])
               (new_block cont_lbl)))))))))) sp = (u, sr) /\
         (* the lowered return handling, sr to sb *)
         (if ret_type = NoneT then comp_return (Lit 0w)
          else if has_default then
            comp_bind (compile_alloc_buffer (type_memory_bytes cenv ret_type))
              (\r. compile_default_return_path cenv ret_type default_ty
                     buf_op r.buf_operand default_op addr_op skip
                     (abi_static_size cenv.ce_struct_fields
                        (if needs_external_call_wrap ret_type
                         then TupleT [ret_type] else ret_type))
                     (abi_size_bound cenv.ce_struct_fields
                        (if needs_external_call_wrap ret_type
                         then TupleT [ret_type] else ret_type))
                     (type_to_abi_dec_info cenv.ce_struct_fields cenv
                        (if needs_external_call_wrap ret_type
                         then TupleT [ret_type] else ret_type)))
          else
            comp_bind (compile_alloc_buffer (type_memory_bytes cenv ret_type))
              (\r. comp_bind (compile_return_value_decode
                          (abi_static_size cenv.ce_struct_fields
                             (if needs_external_call_wrap ret_type
                              then TupleT [ret_type] else ret_type))
                          (abi_size_bound cenv.ce_struct_fields
                             (if needs_external_call_wrap ret_type
                              then TupleT [ret_type] else ret_type)))
              (\hi_op. comp_ignore_bind
                 (compile_abi_decode_to_buf r.buf_operand (Lit 0w) MLOAD
                    buf_op hi_op
                    (type_to_abi_dec_info cenv.ce_struct_fields cenv
                       (if needs_external_call_wrap ret_type
                        then TupleT [ret_type] else ret_type)))
                 (comp_return r.buf_operand)))) sr = (result_op, sb) /\
         vv = (if ret_type = NoneT then StackValue ann result_op
               else LocatedValue ann (mk_ptr result_op LocMemory)) /\
         fn_has_code sp sr func /\ fn_has_code sr sb func /\
         (* the source's request *)
         LENGTH rest = LENGTH arg_types + LENGTH opts /\
         ext_call_opts_ok is_static opts /\
         dest_AddressV target_v = SOME target /\
         value_opt =
           (if is_static then NONE
            else case ext_call_kwarg EKValue opts
                        (DROP (LENGTH arg_types) rest) of
                   NONE => SOME 0
                 | SOME v => dest_NumV v) /\
         build_ext_calldata (get_tenv cx) fname arg_types
           (TAKE (LENGTH arg_types) rest) = SOME calldata /\
         (* source and memory at t *)
         extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp
           is_static addr_op value_op gas_op buf_op call_offset call_len
           (abi_size_bound cenv.ce_struct_fields
              (if needs_external_call_wrap ret_type
               then TupleT [ret_type] else ret_type))
           target value_opt calldata has_default default_op default_ty
           (ext_call_kwarg EKDefault opts (DROP (LENGTH arg_types) rest)) ee t /\
         alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
         (* pointer at t *)
         (!H. valid_horizon cx st0 H ee.storage_trace ==>
            ghost_inv_at (DF H) lo d cenv cx ee G tn t) /\
         ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
         EVERY (\op. op_taint tn op = {})
           [addr_op; value_op; gas_op; buf_op; call_offset; call_len;
            default_op] /\
         (?ao az. eval_operand call_offset t = SOME ao /\
            eval_operand call_len t = SOME az /\
            (w2n az <> 0 ==> w2n ao + w2n az <= t.vs_alloca_next) /\
            (!i. w2n ao <= i /\ i < w2n ao + w2n az ==> i NOTIN tn.t_mem) /\
            (w2n az <> 0 ==>
             ?v b sz. call_offset = Var v /\ FLOOKUP G v = SOME (b,sz) /\
                      b <= w2n ao /\ w2n ao + w2n az <= b + sz)) /\
         (!dv. ext_call_kwarg EKDefault opts (DROP (LENGTH arg_types) rest) =
            SOME dv /\ ~is_word_type default_ty ==>
            ptr_mem_ok cx default_ty dv default_op G tn t /\
            (type_memory_bytes cenv default_ty <> 0 ==>
             ?x b sz w. default_op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
               eval_operand default_op t = SOME w /\ b <= w2n w /\
               w2n w + type_memory_bytes cenv default_ty <= b + sz)) /\
         (abi_size_bound cenv.ce_struct_fields
            (if needs_external_call_wrap ret_type
             then TupleT [ret_type] else ret_type) <> 0 ==>
          ?v b sz ro. buf_op = Var v /\ FLOOKUP G v = SOME (b,sz) /\
            eval_operand buf_op t = SOME ro /\ b <= w2n ro /\
            w2n ro + abi_size_bound cenv.ce_struct_fields
              (if needs_external_call_wrap ret_type
               then TupleT [ret_type] else ret_type) <= b + sz) ==>
         gas_outcome_full
           (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
           (cx_tops cx) cx st0
           (eval_ext_call cx is_static skip (fname,arg_types,ret_type) opts
              (target_v :: rest)) (ee, t, G, tn)
           Q (\H res ee gt r. expr_exit res r)) ==>
      gas_outcome_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        (cx_tops cx) cx st0
        (eval_expr cx
           (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
              args dflt)) (es, s0, G0, tn0)
        Q (\H res ee gt r. expr_exit res r)
Proof
  (* A caller-local staging assertion: the caller derives both word-class
     directions from expr_body_pre, rather than forgetting source typing. *)
  `!xs cenv svs vs tuple_op off sc se tops ctx cx env ee func DF lo
     sa_saved sb_saved st0 pre protected bx G tn s aid b cap es sa s0 G0 tn0 d
     explicit PG.
  let tys = MAP (lowered_value_type cenv) xs in
  let robust = \rt v p s tn. val_wf rt v /\
    !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory rt v p mem in
  let covered = \rt v p sc s.
    val_footprint rt v = 0 \/
    (?k a n. FLOOKUP s.vs_allocas k = SOME (a,n) /\ k < sc.cs_next_id /\
      a <= p /\ p + val_footprint rt v <= a+n /\
      !name q z. local_region cenv ee.scopes s name q z ==>
        a+n <= q \/ q+z <= a) \/
    (?name a n. local_region cenv ee.scopes s name a n /\
      a <= p /\ p + val_footprint rt v <= a+n) in
  LENGTH svs = LENGTH xs /\ LENGTH vs = LENGTH xs /\
  compile_extcall_store_values cenv (ZIP (svs,tys)) tuple_op off sc = ((),se) /\
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env ee /\
  EVERY (\e. ~expr_has_effect e /\
    (is_word_type (lowered_value_type cenv e) <=> is_word_type (expr_type e))) xs /\
  fn_has_code sc se func /\ fn_inst_ids_distinct func /\
  ctx_inst_ids_distinct ctx /\ MEM func ctx.ctx_functions /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  local_ptrs_reserved cenv sa_saved /\
  sa_saved.cs_next_var <= sb_saved.cs_next_var /\
  sa_saved.cs_next_id <= sb_saved.cs_next_id /\
  sb_saved.cs_next_var <= sc.cs_next_var /\ sb_saved.cs_next_id <= sc.cs_next_id /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa_saved x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa_saved x) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    LIST_REL (\(e,sv) v.
      ((?tag op0. sv = StackValue tag op0) \/
       (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
         ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
       (?p si sm0. sv = LocatedValue (lowered_value_type cenv e) p /\
         ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
         lowered_value_type cenv e = expr_type e /\
         compile_expr cenv (expr_type e) e si = (sv,sm0) /\
         sa_saved.cs_next_var <= si.cs_next_var /\ sa_saved.cs_next_id <= si.cs_next_id /\
         sm0.cs_next_var <= sb_saved.cs_next_var /\ sm0.cs_next_id <= sb_saved.cs_next_id)) /\
      (?raw. read_result cx raw ee = (INL v,ee) /\
        vv_holds cenv cx (lowered_value_type cenv e) raw sv ee s /\
        vv_at cenv cx (lowered_value_type cenv e) sa_saved sb_saved ee raw sv s /\
        ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn s /\
        vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee raw sv s) /\
      vv_storage_live H cx sv ee s /\
      (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
        ptr_buf_ok cenv e op G s) /\
      (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv e p.ptr_operand G s) /\
      (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
        !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
          eval_operand (vv_operand sv) s = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
            val_in_memory rt v (w2n w) mem))) (ZIP (xs,svs)) vs) /\
  EVERY (\sv. !x. vv_operand sv = Var x ==> not_fresh_at sc x) svs /\
  LIST_REL (\e v. ?rt.
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
    value_has_type rt v /\ val_wf rt v /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size rt /\
    type_memory_size rt < 2**64 /\
    (is_word_type (lowered_value_type cenv e) ==> type_memory_size rt = 32)) xs vs /\
  (!rt v p. MEM (rt,v,p) pre ==>
    robust rt v p s tn /\ b <= p /\ p + val_footprint rt v <= b+off) /\
  (!rt v p. (rt,v,p) IN protected ==>
    robust rt v p s tn /\ covered rt v p sc s /\
    (!i. p <= i /\ i < p+val_footprint rt v ==>
      ~(b+off <= i /\ i < b+off+SUM (MAP (type_memory_bytes cenv) tys)))) /\
  tuple_op = Var bx /\ not_fresh_at sc bx /\ eval_operand tuple_op s = SOME (n2w b) /\
  FLOOKUP G bx = SOME (b,cap) /\ op_taint tn tuple_op = {} /\
  FLOOKUP s.vs_allocas aid = SOME (b,cap) /\
  sb_saved.cs_next_id <= aid /\ aid < sc.cs_next_id /\ lo <= b /\
  (!k a n i. FLOOKUP s0.vs_allocas k = SOME (a,n) /\ k < sa.cs_next_id /\
    (!name q z. local_region cenv es.scopes s0 name q z ==> a+n <= q \/ q+z <= a) /\
    a <= i /\ i < a+n ==>
    ~(b+off <= i /\ i < b+off+SUM (MAP (type_memory_bytes cenv) tys))) /\
  (!name a n i. local_region cenv es.scopes s0 name a n /\ a <= i /\ i < a+n ==>
    ~(b+off <= i /\ i < b+off+SUM (MAP (type_memory_bytes cenv) tys))) /\
  off + SUM (MAP (type_memory_bytes cenv) tys) <= cap /\
  b+cap <= s.vs_alloca_next /\ b+cap < 2**256 /\
  (!name a n. local_region cenv ee.scopes s name a n ==> b+cap <= a \/ a+n <= b) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  sa.cs_next_var <= sa_saved.cs_next_var /\ sa.cs_next_id <= sa_saved.cs_next_id /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  return_buf_frame d cenv sc s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  ?t G' tn'.
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,G',tn') /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx ee G' tn' t) /\
    ~t.vs_halted /\ t.vs_current_bb = se.cs_current_bb /\
    t.vs_inst_idx = LENGTH se.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn' /\ return_buf_frame d cenv se t /\
    (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!k a. FLOOKUP s.vs_allocas k = SOME a ==> FLOOKUP t.vs_allocas k = SOME a) /\
    eval_operand tuple_op t = SOME (n2w b) /\ FLOOKUP G' bx = SOME (b,cap) /\
    op_taint tn' tuple_op = {} /\ FLOOKUP t.vs_allocas aid = SOME (b,cap) /\
    (!rt v p. MEM (rt,v,p) pre ==> robust rt v p t tn') /\
    (!rt v p. (rt,v,p) IN protected ==> robust rt v p t tn') /\
    (!i. i < LENGTH xs ==> ?rt.
      evaluate_type (get_tenv cx) (EL i tys) = SOME rt /\
      robust rt (EL i vs)
        (b+off+SUM (MAP (type_memory_bytes cenv) (TAKE i tys))) t tn')` by
  (rpt gen_tac >>
  map_every qid_spec_tac [`protected`,`pre`,`off`,`tn`,`G`,`s`,`sc`,`svs`,`vs`] >>
  Induct_on `xs`
  >- (simp[] >> rpt gen_tac >> strip_tac >>
      gvs[compile_extcall_store_values_def, comp_return_def] >>
      qexistsl_tac [`s`,`G`,`tn`] >>
      simp[gas_origin_ptr_path_rules] >> metis_tac[]) >>
  rpt gen_tac >> simp[] >> strip_tac >>
  qpat_x_assum `is_word_type (lowered_value_type cenv h) = is_word_type (expr_type h)`
    (mk_asm "head-word-class") >>
  `is_word_type (lowered_value_type cenv h) ==> is_word_type (expr_type h)` by
    (asm "head-word-class" mp_tac >> simp[]) >>
  qpat_x_assum `!vs' svs sc' s'' G' tn' off' pre' protected'. _` (mk_asm "tuple-ih") >>
  Cases_on `svs` >- gvs[] >>
  rename1 `ZIP (h::xs,saved::svs_tail)` >>
  qpat_x_assum `compile_extcall_store_values _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_extcall_store_values_def, comp_bind_def,
       comp_ignore_bind_def, AllCaseEqs()] >> strip_tac >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op ADD [Var bx; Lit (n2w off)] sc = (dst,su)` >>
  pairarg_tac >> gvs[] >>
  rename1 `unwrap_value cenv saved su = (src,ss)` >>
  pairarg_tac >> gvs[] >>
  rename1 `compile_extcall_store_values cenv _ (Var bx) _ stail = ((),se)` >>
  `ci_mono sc su` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono su ss` by metis_tac[ci_mono_unwrap_value, pairTheory.SND] >>
  `ci_mono ss stail` by
    (qpat_x_assum `(if _ then _ else _) ss = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `is_word_type (lowered_value_type cenv h)` >>
     Cases_on `is_bytestring_type (lowered_value_type cenv h)` >>
     simp[] >> metis_tac[ci_mono_emit_void, ci_mono_compile_store_bytestring, pairTheory.SND]) >>
  `ci_mono stail se` by metis_tac[ci_mono_compile_extcall_store_values, pairTheory.SND] >>
  `fn_has_code sc su func /\ fn_has_code su ss func /\
   fn_has_code ss stail func /\ fn_has_code stail se func` by
    (qpat_x_assum `fn_has_code sc se func` mp_tac >>
     qpat_x_assum `ci_mono sc su` mp_tac >>
     qpat_x_assum `ci_mono su ss` mp_tac >>
     qpat_x_assum `ci_mono ss stail` mp_tac >>
     qpat_x_assum `ci_mono stail se` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[ci_mono_def, cs_extends_trans, fn_has_code_split]) >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off) /\
   op_taint tn (Lit (n2w off)) = {}` by simp[eval_operand_def, op_taint_def] >>
  drule_all (attribute_emit_binop_path_ptr |> Q.INST
    [`opc` |-> `ADD`, `f` |-> `word_add`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`,`G`,`ARB`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `op_taint ta (Var out) = {}` >>
  qmatch_asmsub_abbrev_tac `step_prov PG G inst u` >>
  qabbrev_tac `Ga = step_prov PG G inst u` >>
  qabbrev_tac `q = (update_var out (n2w b + n2w off) s with
    vs_inst_idx := SUC s.vs_inst_idx)` >>
  `!out. step_inst_base (mk_inst sc.cs_next_id ADD
      [Var bx; Lit (n2w off)] [out]) s =
     OK (update_var out (n2w b + n2w off) s)` by
    simp[Once step_inst_base_def, venomInstTheory.mk_inst_def, exec_pure2_def,
      eval_operand_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK q,Ga,ta)` by
    (rpt strip_tac >>
     `allocas_from lo s` by metis_tac[ghost_inv_at_def] >>
     drule_at (Pat `emit_op _ _ _ = _`) typed_copy_origin_ptr_binop_path >>
     simp[] >> disch_then drule_all >>
     disch_then (mp_tac o cj 2) >>
     simp[Abbr `q`, Abbr `Ga`, Abbr `ta`, Abbr `u`] >> metis_tac[]) >>
  suspend "protected_cons") >>
  pop_assum (mk_asm "typed-tuple-staging") >>
  suspend "request_main"
QED

Resume extcall_request_full[protected_cons]:
  drule emitted_insts_emit_op >> strip_tac >>
  `~not_fresh_at sc out` by
    (gvs[loweringStateRelDefsTheory.not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `!x. not_fresh_at sc x ==> x <> out` by metis_tac[] >>
  `!x. not_fresh_at sc x ==>
    lookup_var x q = lookup_var x s /\ FLOOKUP Ga x = FLOOKUP G x /\
    op_taint ta (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> simp[Abbr `q`, Abbr `u`, lookup_var_def, update_var_def,
      finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
  `q.vs_memory = s.vs_memory /\ q.vs_allocas = s.vs_allocas /\
   q.vs_alloca_next = s.vs_alloca_next /\ q.vs_call_ctx = s.vs_call_ctx /\
   q.vs_accounts = s.vs_accounts /\ q.vs_transient = s.vs_transient /\
   q.vs_immutables = s.vs_immutables` by
    simp[Abbr `q`, Abbr `u`, update_var_def] >>
  `local_ptrs_reserved cenv sc` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sa_saved` >> simp[] >> decide_tac) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee q /\
    ghost_inv_at (DF H) lo d cenv cx ee Ga ta q` by
    (gen_tac >> strip_tac >> conj_tac
     >- (simp[Abbr `q`, Abbr `u`, stmt_state_rel_inst_idx] >>
         irule stmt_state_rel_update_var >>
         metis_tac[exprSimOperandsTheory.fresh_not_local_ptr]) >>
     irule ghost_inv_at_exterior_frame >>
     qexistsl_tac [`G`,`ee`,`s`,`sc`,`tn`] >> simp[]) >>
  `!op. (!x. op = Var x ==> not_fresh_at sc x) ==>
    eval_operand op q = eval_operand op s /\
    op_taint ta op = op_taint tn op /\ op_prov Ga op = op_prov G op` by
    (gen_tac >> strip_tac >> Cases_on `op` >>
     simp[eval_operand_def, op_taint_def, op_prov_def,
       Abbr `q`, Abbr `u`, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
  `!name a n. local_region cenv ee.scopes q name a n <=>
    local_region cenv ee.scopes s name a n` by
    (irule exprSimPtrLiteralBufferTheory.literal_ptr_local_region_frame >>
     qexists_tac `sc` >> simp[]) >>
  `!ty raw sv. (!x. vv_operand sv = Var x ==> not_fresh_at sc x) ==>
    vv_holds cenv cx ty raw sv ee s ==>
    vv_holds cenv cx ty raw sv ee q` by
    (rpt gen_tac >> strip_tac >> strip_tac >>
     irule exprSimVVFrameTheory.vv_holds_vars_frame >>
     qexists_tac `s` >> simp[contract_storage_def, contract_transient_def]) >>
  `!ty raw sv. (!x. vv_operand sv = Var x ==> not_fresh_at sc x) ==>
    vv_at cenv cx ty sa_saved sb_saved ee raw sv s ==>
    vv_at cenv cx ty sa_saved sb_saved ee raw sv q` by
    (rpt gen_tac >> strip_tac >> strip_tac >>
     irule exprSimVVFrameTheory.vv_at_vars_frame >>
     qexistsl_tac [`s`,`sb_saved`] >> simp[]) >>
  `!ty raw sv. (!x. vv_operand sv = Var x ==> not_fresh_at sc x) ==>
    ptr_vv_ok cx ty raw sv ee G tn s ==>
    ptr_vv_ok cx ty raw sv ee Ga ta q` by
    (rpt gen_tac >> strip_tac >> strip_tac >>
     simp[Abbr `q`, Abbr `u`] >>
     irule (SRULE [] assign_base_field_vv_update) >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`G`,`tn`] >> simp[] >> metis_tac[]) >>
  `!ty lt raw sv. (!x. vv_operand sv = Var x ==> not_fresh_at sc x) ==>
    vv_store_bound cx ty lt ee raw sv s ==>
    vv_store_bound cx ty lt ee raw sv q` by
    (rpt gen_tac >> strip_tac >> strip_tac >>
     `eval_operand (vv_operand sv) q = eval_operand (vv_operand sv) s` by metis_tac[] >>
     qpat_x_assum `q.vs_alloca_next = s.vs_alloca_next` mp_tac >>
     qpat_x_assum `eval_operand (vv_operand sv) q = _` mp_tac >>
     qpat_x_assum `vv_store_bound _ _ _ _ _ _ s` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `sv` >>
     simp[exprSimMemDefsTheory.vv_store_bound_def, vv_operand_def] >>
     metis_tac[]) >>
  `!H sv. (!x. vv_operand sv = Var x ==> not_fresh_at sc x) ==>
    (vv_storage_live H cx sv ee q <=> vv_storage_live H cx sv ee s)` by
    (rpt gen_tac >> strip_tac >>
     `eval_operand (vv_operand sv) q = eval_operand (vv_operand sv) s` by metis_tac[] >>
     pop_assum mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     Cases_on `sv` >> simp[vv_operand_def, vv_storage_live_def]) >>
  `!e op. (!x. op = Var x ==> not_fresh_at sc x) ==>
    (ptr_buf_ok cenv e op Ga q <=> ptr_buf_ok cenv e op G s)` by
    (rpt gen_tac >> strip_tac >> simp[ptr_buf_ok_def] >> metis_tac[]) >>
  mp_tac (extcall_saved_resources_frame |> INST_TYPE [alpha |-> ``:256``] |> Q.INST
    [`t` |-> `q`, `G'` |-> `Ga`, `tn'` |-> `ta`,
     `svs` |-> `svs_tail`, `vs` |-> `ys`] |> Q.GEN `H`) >>
  qmatch_goalsub_abbrev_tac `LET _ saved_rel` >>
  pure_rewrite_tac [LET_THM] >> BETA_TAC >>
  disch_then (mk_asm "saved-add-frame") >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    LIST_REL (saved_rel H q Ga ta) (ZIP (xs,svs_tail)) ys` by
    (rpt strip_tac >> asm_x "tuple-ih" kall_tac >>
     asm_x "saved-add-frame" irule >>
     simp[contract_storage_def, contract_transient_def] >>
     conj_tac
     >- (rpt gen_tac >> strip_tac >>
         `MEM sv svs_tail` by
           (qpat_x_assum `MEM ((e,sv),_) _` mp_tac >>
            qpat_x_assum `LENGTH svs_tail = _` mp_tac >>
            qpat_x_assum `LENGTH ys = _` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
            gvs[listTheory.MEM_ZIP] >>
            gvs[listTheory.EL_MEM, listTheory.EL_ZIP]) >>
         `!x. vv_operand sv = Var x ==> not_fresh_at sc x` by
           (qpat_x_assum `EVERY _ svs_tail` mp_tac >>
            qpat_x_assum `MEM sv svs_tail` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
         simp[] >> metis_tac[]) >>
     simp[Abbr `saved_rel`] >>
     qpat_x_assum `!H. valid_horizon _ _ H _ ==> (_ /\ LIST_REL _ _ _)`
       (qspec_then `H` mp_tac) >> simp[]) >>
  mp_tac (extcall_saved_resource_frame |> INST_TYPE [alpha |-> ``:256``] |>
    Q.INST [`t` |-> `q`, `G'` |-> `Ga`, `tn'` |-> `ta`,
      `e` |-> `h`, `sv` |-> `saved`] |> Q.GEN `H`) >>
  qmatch_goalsub_abbrev_tac `LET _ head_rel` >>
  `head_rel = saved_rel` by simp[Abbr `head_rel`, Abbr `saved_rel`] >>
  pop_assum SUBST_ALL_TAC >>
  pure_rewrite_tac [LET_THM] >> BETA_TAC >>
  disch_then (mk_asm "head-add-frame") >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    saved_rel H q Ga ta (h,saved) v` by
    (rpt strip_tac >> asm_x "tuple-ih" kall_tac >>
     asm_x "head-add-frame" irule >>
     simp[contract_storage_def, contract_transient_def] >>
     qpat_x_assum `!H. valid_horizon _ _ H _ ==> (_ /\ LIST_REL _ _ _)`
       (qspec_then `H` mp_tac) >>
     qpat_x_assum `evaluate_type _ (lowered_value_type cenv h) = SOME rt` mp_tac >>
     qpat_x_assum `valid_horizon cx st0 H ee.storage_trace` mp_tac >>
     qpat_x_assum `Abbrev (saved_rel = _)`
       (fn th => POP_ASSUM_LIST (K all_tac) >> assume_tac th) >>
     simp[Abbr `saved_rel`]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by
    (qpat_x_assum `storage_trace_domain _ _ _` mp_tac >>
     rewrite_tac[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> saved_rel H q Ga ta _ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  simp_tac (srw_ss()) [Abbr `saved_rel`] >>
  disch_then (map_every (mk_asm "head-at-add") o single) >>
  `~q.vs_halted /\ q.vs_current_bb = su.cs_current_bb /\
   q.vs_inst_idx = LENGTH su.cs_current_insts` by
    (drule loweringShapeRulesTheory.emit_op_facts >> strip_tac >>
     simp[Abbr `q`, Abbr `u`, update_var_def]) >>
  `alloca_history func q` by
    (drule_all bodyPtrMakeArrayEmissionTheory.emit_op_fetch_boundary >> strip_tac >>
     qpat_x_assum `alloca_history func s` mp_tac >>
     simp[allocaHistoryTheory.alloca_history_def, Abbr `q`, Abbr `u`, update_var_def] >>
     strip_tac >> rpt strip_tac >>
     `bb' = bb` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
     Cases_on `k < LENGTH sc.cs_current_insts` >- metis_tac[] >>
     `k = LENGTH sc.cs_current_insts` by decide_tac >>
     gvs[Abbr `inst`, venomInstTheory.mk_inst_def]) >>
  `?z Gu tu.
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (q,Ga,ta) [] (OK z,Gu,tu) /\
      stmt_state_rel H ctx func cenv cx ee z /\
      ghost_inv_at (DF H) lo d cenv cx ee Gu tu z) /\
    expr_val_rel cx (lowered_value_type cenv h) v src z /\
    ptr_val_ok cx (lowered_value_type cenv h) v src Gu tu z /\
    (~is_word_type (lowered_value_type cenv h) ==> ptr_buf_ok cenv h src Gu z) /\
    expr_store_bound cx (expr_type h) v src z /\
    (~is_word_type (lowered_value_type cenv h) ==>
      !w. eval_operand src z = SOME w ==>
        type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ~z.vs_halted /\ z.vs_current_bb = ss.cs_current_bb /\
    z.vs_inst_idx = LENGTH ss.cs_current_insts /\
    alloca_history func z /\ q.vs_alloca_next <= z.vs_alloca_next /\
    (!x. not_fresh_at su x ==>
      lookup_var x z = lookup_var x q /\ FLOOKUP Gu x = FLOOKUP Ga x /\
      op_taint tu (Var x) = op_taint ta (Var x)) /\
    wb_frame cenv ee ee su q z /\
    ghost_kept_at lo cenv ee su Ga ta q Gu tu` by
    suspend "unwrap_joint" >>
  suspend "store_tail"
QED

Resume extcall_request_full[unwrap_joint]:
  asm_x "tuple-ih" kall_tac >>
  asm_x "saved-add-frame" kall_tac >>
  asm_x "head-add-frame" kall_tac >>
  asm_x "head-at-add" mp_tac >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "head-form") strip_assume_tac) >>
  Cases_on `(?tag op. saved = StackValue tag op) \/
    (?p. saved = LocatedValue (lowered_value_type cenv h) p /\
       ~is_word_type (lowered_value_type cenv h) /\ p.ptr_location = LocMemory)`
  >- suspend "unwrap_identity" >>
  qpat_x_assum `~(_ \/ _)`
    (strip_assume_tac o REWRITE_RULE [DE_MORGAN_THM]) >>
  asm_x "head-form" mp_tac >> simp[] >> strip_tac >>
  `post_value_type cenv h = lowered_value_type cenv h` by
    metis_tac[post_value_type_lowered] >>
  `ci_mono si sm0` by
    (qpat_x_assum `compile_expr _ _ _ si = _` (fn th =>
       mp_tac (Q.SPECL [`cenv`, `expr_type h`, `h`, `si`]
         (CONJUNCT1 exprLoweringPropsTheory.compile_expr_ci_mono)) >>
       rewrite_tac[th, pairTheory.SND])) >>
  `si.cs_next_var <= sm0.cs_next_var /\ si.cs_next_id <= sm0.cs_next_id` by
    (qpat_x_assum `ci_mono si sm0` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[ci_mono_def]) >>
  `local_ptrs_reserved cenv si` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sa_saved` >> simp[]) >>
  `local_ptrs_reserved cenv sm0` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `si` >> simp[]) >>
  `!x. vv_operand saved = Var x ==> not_fresh_at sm0 x` by
    metis_tac[exprOperandVarTheory.compiler_compile_var] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    (stmt_state_rel H ctx func cenv cx ee q /\
     storage_well_formed_on cx ee (FST H) /\
     vv_storage_live H cx saved ee q /\
     (?raw. read_result cx raw ee = (INL v,ee) /\
       vv_holds cenv cx (post_value_type cenv h) raw saved ee q)) /\
    ghost_inv_at (DF H) lo d cenv cx ee Ga ta q` by
    (rpt strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H _ ==> saved_rel H q Ga ta _ _`
       drule >>
     qpat_x_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ q /\ _`
       drule >>
     qpat_x_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ s /\ _`
       drule >>
     qpat_x_assum `post_value_type cenv h = _` mp_tac >>
     qpat_x_assum `Abbrev (saved_rel = _)`
       (fn th => POP_ASSUM_LIST (K all_tac) >> assume_tac th) >>
     simp_tac (srw_ss()) [] >> metis_tac[]) >>
  `vv_store_bound cx (expr_type h) (lowered_value_type cenv h) ee
     (Value v) saved q` by
    (qpat_x_assum `saved = LocatedValue _ _` (fn th => rewrite_tac[th]) >>
     irule exprSimMemDefsTheory.vv_store_bound_nonmem >> simp[]) >>
  `ptr_vv_ok cx (post_value_type cenv h) (Value v) saved ee Ga ta q` by
    (qpat_x_assum `ptr_vv_ok _ _ raw saved _ _ _ _` mp_tac >>
     qpat_x_assum `saved = LocatedValue _ _` mp_tac >>
     qpat_x_assum `p.ptr_location <> LocMemory` mp_tac >>
     qpat_x_assum `post_value_type cenv h = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[ptr_vv_ok_def]) >>
  `ghost_kept_at lo cenv ee si Ga ta q Ga ta` by
    simp[ghost_kept_at_def] >>
  `sm0.cs_next_var <= su.cs_next_var /\ sm0.cs_next_id <= su.cs_next_id` by
    (qpat_x_assum `ci_mono sc su` mp_tac >>
     qpat_x_assum `sm0.cs_next_var <= sb_saved.cs_next_var` mp_tac >>
     qpat_x_assum `sm0.cs_next_id <= sb_saved.cs_next_id` mp_tac >>
     qpat_x_assum `sb_saved.cs_next_var <= sc.cs_next_var` mp_tac >>
     qpat_x_assum `sb_saved.cs_next_id <= aid` mp_tac >>
     qpat_x_assum `aid < sc.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[ci_mono_def] >> decide_tac) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x)` by
    (qpat_x_assum `!x sz. cenv.ce_return_buf = _ ==> not_fresh_at sa_saved x` mp_tac >>
     qpat_x_assum `!x sz. cenv.ce_return_pc = _ ==> not_fresh_at sa_saved x` mp_tac >>
     qpat_x_assum `sa_saved.cs_next_var <= si.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
  drule_at (Pat `compile_expr _ _ _ _ = _`)
    extcall_saved_nonmemory_unwrap_origin_ptr >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
  disch_then (mp_tac o Q.INST [`rty` |-> `rt`] o SPEC_ALL) >>
  impl_tac
  >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, REFL_TAC,
        simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def]]
      >- (qpat_x_assum `~is_word_type (lowered_value_type cenv h)` mp_tac >>
          qpat_x_assum `lowered_value_type cenv h = expr_type h` mp_tac >>
          POP_ASSUM_LIST (K all_tac) >> metis_tac[])
      >- (qpat_x_assum `evaluate_type (get_tenv cx) (lowered_value_type cenv h) = SOME rt` mp_tac >>
          qpat_x_assum `type_memory_bytes cenv (lowered_value_type cenv h) = type_memory_size rt` mp_tac >>
          qpat_x_assum `type_memory_size rt < 18446744073709551616` mp_tac >>
          qpat_x_assum `lowered_value_type cenv h = expr_type h` mp_tac >>
          POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[])
      >- (qpat_x_assum `evaluate_type (get_tenv cx) (lowered_value_type cenv h) = SOME rt` mp_tac >>
          qpat_x_assum `lowered_value_type cenv h = expr_type h` mp_tac >>
          POP_ASSUM_LIST (K all_tac) >> simp[]) >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> (_ /\ LIST_REL _ _ _)`
        (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
      qpat_x_assum `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) _` mp_tac >>
      qpat_x_assum `evaluate_type (get_tenv cx) (lowered_value_type cenv h) = SOME rt` mp_tac >>
      qpat_x_assum `saved = LocatedValue _ p` mp_tac >>
      qpat_x_assum `lowered_value_type cenv h = expr_type h` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[]) >>
  strip_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (q,Ga,ta) [] (OK z,G',tn') /\
    stmt_state_rel H ctx func cenv cx ee z /\
    ghost_inv_at (DF H) lo d cenv cx ee G' tn' z` by
    (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _ /\ expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[expr_post_def] >> metis_tac[]) >>
  `expr_val_rel cx (post_value_type cenv h) v src z` by
    (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _ /\ expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _` drule >>
     POP_ASSUM_LIST (K all_tac) >> simp[expr_post_def] >> metis_tac[]) >>
  `~z.vs_halted` by
    (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _ /\ stmt_state_rel _ _ _ _ _ _ z /\ _` drule >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     drule gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
  qexistsl_tac [`z`, `G'`, `tn'`] >>
  simp[GSYM post_value_type_lowered] >>
  qpat_x_assum `expr_val_rel cx (post_value_type cenv h) v src z` mp_tac >>
  qpat_x_assum `ptr_val_ok cx (post_value_type cenv h) v src G' tn' z` mp_tac >>
  qpat_x_assum `~is_word_type (post_value_type cenv h) ==> ptr_buf_ok _ _ _ _ _` mp_tac >>
  qpat_x_assum `~is_word_type (post_value_type cenv h) ==> !rt w. _` mp_tac >>
  qpat_x_assum `evaluate_type (get_tenv cx) (lowered_value_type cenv h) = SOME rt` mp_tac >>
  qpat_x_assum `~is_word_type (lowered_value_type cenv h)` mp_tac >>
  qpat_x_assum `lowered_value_type cenv h = expr_type h` mp_tac >>
  qpat_x_assum `post_value_type cenv h = lowered_value_type cenv h` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> simp[]
QED

Resume extcall_request_full[unwrap_identity]:
  drule_all (extcall_saved_identity_unwrap |> Q.INST [`sa` |-> `su`]) >>
  disch_then (qspec_then `su` strip_assume_tac) >>
  `src = vv_operand saved /\ ss = su` by
    (qpat_x_assum `unwrap_value cenv saved su = (src,ss)` mp_tac >>
     (simp[])) >>
  `~is_word_type (lowered_value_type cenv h) ==>
    !w. eval_operand (vv_operand saved) q = SOME w ==>
      type_memory_size rt = 0 \/
      w2n w + type_memory_size rt <= q.vs_alloca_next` by
    (rpt strip_tac >>
     `~is_word_type (expr_type h)` by
       (asm "head-word-class" mp_tac >> simp[]) >>
     qpat_assum `vv_store_bound _ _ _ _ _ saved q` mp_tac >>
     qpat_assum `evaluate_type _ (lowered_value_type cenv h) = SOME rt` mp_tac >>
     qpat_assum `~is_word_type (expr_type h)` mp_tac >>
     qpat_assum `eval_operand (vv_operand saved) q = SOME w` mp_tac >>
     qpat_assum `(?tag op. saved = StackValue tag op) \/ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `saved` >>
     simp[exprSimMemDefsTheory.vv_store_bound_def, vv_operand_def] >>
     metis_tac[]) >>
  qexistsl_tac [`q`,`Ga`,`ta`] >>
  simp[gas_origin_ptr_path_rules, exprSimWordArgsTheory.wb_frame_refl,
       ghost_kept_at_def, ghost_kept_def] >>
  qpat_x_assum `(?tag op. saved = StackValue tag op) \/ _` mp_tac >>
  qpat_x_assum `read_result cx raw ee = (INL v,ee)` mp_tac >>
  qpat_x_assum `ptr_vv_ok _ _ _ saved _ _ _ q` mp_tac >>
  qpat_x_assum `vv_store_bound _ _ _ _ _ saved q` mp_tac >>
  qpat_x_assum `!tag op. saved = StackValue tag op /\ _ ==> _` mp_tac >>
  qpat_x_assum `!tag p. saved = LocatedValue tag p /\ _ ==> _` mp_tac >>
  qpat_x_assum `!op. (!x. op = Var x ==> _) ==> _` mp_tac >>
  qpat_x_assum `!x. vv_operand saved = Var x ==> _` mp_tac >>
  qpat_x_assum `evaluate_type _ (lowered_value_type cenv h) = SOME rt` mp_tac >>
  qpat_x_assum `is_word_type (lowered_value_type cenv h) ==> is_word_type (expr_type h)` mp_tac >>
  qpat_x_assum `q.vs_alloca_next = s.vs_alloca_next` mp_tac >>
  qpat_x_assum `!x. not_fresh_at sc x ==> lookup_var x q = _ /\ _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  gvs[vv_operand_def, ptr_vv_ok_def, ptr_val_ok_def,
      exprSimMemDefsTheory.vv_store_bound_def,
      exprSimMemDefsTheory.expr_store_bound_def, ptr_buf_ok_def]
  >- metis_tac[]
  >- (rpt strip_tac >>
      qpat_x_assum `!w. eval_operand p.ptr_operand s = SOME w /\ _ ==> _`
        drule >> simp[] >> strip_tac >>
      qexistsl_tac [`x`,`b`,`sz`] >> metis_tac[]) >>
  metis_tac[]
QED

Resume extcall_request_full[store_tail]:
  `not_fresh_at su out` by
    (qpat_assum `emit_op ADD _ sc = (dst,su)` mp_tac >>
     qpat_assum `dst = Var out` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> drule loweringShapeRulesTheory.emit_op_facts >>
     strip_tac >> gvs[]) >>
  `not_fresh_at ss out` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono, ci_mono_def] >>
  `lookup_var out q = SOME (n2w (b+off))` by
    simp[Abbr `q`, Abbr `u`, update_var_def, lookup_var_def,
      finite_mapTheory.FLOOKUP_UPDATE, wordsTheory.word_add_n2w] >>
  `lookup_var out z = SOME (n2w (b+off))` by metis_tac[] >>
  `FLOOKUP Ga out = SOME (b,cap)` by
    (simp[Abbr `Ga`, Abbr `inst`, step_prov_def, out_prov_def,
      op_prov_def, set_prov_def, first_prov_def, venomInstTheory.mk_inst_def,
      finite_mapTheory.FLOOKUP_UPDATE]) >>
  `FLOOKUP Gu out = SOME (b,cap) /\ op_taint tu (Var out) = {}` by
    (qpat_assum `!x. not_fresh_at su x ==> _` (qspec_then `out` mp_tac) >>
     simp[]) >>
  `b+off < dimword (:256) /\ b+off+type_memory_size rt <= b+cap` by
    (simp[wordsTheory.dimword_def] >> decide_tac) >>
  `ptr_covers Gu tu out z (type_memory_size rt)` by
    (simp[ptr_covers_def] >> qexistsl_tac [`n2w (b+off)`,`b`,`cap`] >>
     simp[]) >>
  `?sw. eval_operand src z = SOME sw` by
    (qpat_assum `expr_val_rel cx _ v src z` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[expr_val_rel_def] >> metis_tac[]) >>
  `op_taint tu src = {}` by
    (qpat_assum `ptr_val_ok _ _ _ src Gu tu z` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[ptr_val_ok_def]) >>
  `~is_word_type (lowered_value_type cenv h) ==>
    !mem. mem_agree_outside tu.t_mem z.vs_memory mem ==>
      val_in_memory rt v (w2n sw) mem` by
    (qpat_assum `ptr_val_ok _ _ _ src Gu tu z` mp_tac >>
     qpat_assum `evaluate_type _ (lowered_value_type cenv h) = SOME rt` mp_tac >>
     qpat_assum `eval_operand src z = SOME sw` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[ptr_val_ok_def, ptr_mem_ok_def] >> metis_tac[]) >>
  `~is_word_type (lowered_value_type cenv h) /\ type_memory_size rt <> 0 ==>
    ?x. src = Var x /\ ptr_covers Gu tu x z (type_memory_size rt)` by
    (qpat_assum `~is_word_type _ ==> ptr_buf_ok _ _ src Gu z` mp_tac >>
     qpat_assum `type_memory_bytes cenv _ = type_memory_size rt` mp_tac >>
     qpat_assum `eval_operand src z = SOME sw` mp_tac >>
     qpat_assum `op_taint tu src = {}` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[ptr_buf_ok_def, ptr_covers_def] >> rpt strip_tac >>
     gvs[eval_operand_def] >> metis_tac[]) >>
  `!x. src = Var x ==> not_fresh_at ss x` by
    (qpat_assum `unwrap_value cenv saved su = (src,ss)` mp_tac >>
     qpat_assum `!x. vv_operand saved = Var x ==> not_fresh_at sc x` mp_tac >>
     qpat_assum `ci_mono sc su` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     `case saved of StackValue ty v => (!x. v = Var x ==> not_fresh_at su x)
       | LocatedValue ty p => (!x. p.ptr_operand = Var x ==> not_fresh_at su x)` by
       (Cases_on `saved` >> gvs[vv_operand_def, ci_mono_def] >>
        metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
     drule_all exprOperandVarTheory.compiler_unwrap_value_var >> simp[]) >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path _ (q,Ga,ta) _ (OK z,Gu,tu) /\ _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     qpat_assum `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[ghost_inv_at_def]) >>
  `b+off+type_memory_size rt <= z.vs_alloca_next` by
    (qpat_assum `b+cap <= s.vs_alloca_next` mp_tac >>
     (bossLib.simp [])) >>
  `?r Gr tr.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (z,Gu,tu) [] (OK r,Gr,tr)) /\
    typed_copy_state_frame ss (b+off) (type_memory_size rt) z r /\
    ~r.vs_halted /\ r.vs_current_bb = stail.cs_current_bb /\
    r.vs_inst_idx = LENGTH stail.cs_current_insts /\
    tr.t_imm = tu.t_imm /\ tr.t_stor = tu.t_stor /\ tr.t_trans = tu.t_trans /\
    (!i. ~(b+off <= i /\ i < b+off+type_memory_size rt) ==>
      (i IN tr.t_mem <=> i IN tu.t_mem)) /\
    (!mem. mem_agree_outside tr.t_mem r.vs_memory mem ==>
      val_in_memory rt v (b+off) mem) /\
    (!x. not_fresh_at ss x ==>
      FLOOKUP Gr x = FLOOKUP Gu x /\ op_taint tr (Var x) = op_taint tu (Var x))` by
    (Cases_on `is_word_type (lowered_value_type cenv h)`
     >- suspend "store_word" >>
     Cases_on `~is_bytestring_type (lowered_value_type cenv h) /\ type_memory_size rt = 0`
     >- suspend "store_zero" >>
     suspend "store_capacity") >>
  suspend "stored_tail"
QED

Resume extcall_request_full[store_word]:
  `type_memory_size rt = 32` by simp[] >>
  `emit_void MSTORE [Var out;src] ss = ((),stail)` by
    (qpat_assum `(if is_word_type _ then _ else _) ss = _` mp_tac >>
     qpat_assum `dst = Var out` mp_tac >>
     qpat_assum `is_word_type (lowered_value_type cenv h)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `w2n (n2w (b+off) : bytes32) = b+off` by simp[wordsTheory.w2n_n2w] >>
  `ptr_covers Gu tu out z 32 /\
   w2n (n2w (b+off) : bytes32)+32 <= z.vs_alloca_next` by
    (qpat_assum `ptr_covers Gu tu out z (type_memory_size rt)` mp_tac >>
     qpat_assum `b+off+type_memory_size rt <= z.vs_alloca_next` mp_tac >>
     qpat_assum `type_memory_size rt = 32` mp_tac >>
     qpat_assum `w2n (n2w (b+off) : bytes32) = b+off` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  drule_all extcall_slot_mstore_origin >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `sw = typed_val_to_w256 rt v` by
    (qpat_assum `expr_val_rel cx _ v src z` mp_tac >>
     qpat_assum `eval_operand src z = SOME sw` mp_tac >>
     qpat_assum `evaluate_type _ (lowered_value_type cenv h) = SOME rt` mp_tac >>
     qpat_assum `is_word_type (lowered_value_type cenv h)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[expr_val_rel_def]) >>
  `val_in_memory rt v (b+off) (mstore (b+off) sw z).vs_memory` by
    (drule_all exprSimPropsTheory.val_in_memory_word >>
     disch_then (qspecl_then [`b+off`, `(mstore (b+off) sw z).vs_memory`] mp_tac) >>
     simp[valueEncodingPropsTheory.mstore_mem_word_at_same]) >>
  qexistsl_tac [`t`,`Gu`,`tn'`] >>
  simp[typed_copy_mstore_state_frame, op_taint_def] >>
  rpt strip_tac >>
  irule assignBasePtrLocalStoreTheory.assign_base_ptr_clean_window_robust_value >>
  conj_tac >- simp[] >>
  qexistsl_tac [`(mstore (b+off) sw z).vs_memory`,`32`,`tu.t_mem`] >>
  simp[] >>
  qpat_assum `val_wf rt v` mp_tac >>
  qpat_assum `type_memory_size rt = 32` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  metis_tac[exprSimPropsTheory.val_footprint_le_store_size,
    exprSimPropsTheory.val_store_size_le, arithmeticTheory.LESS_EQ_TRANS]
QED

Resume extcall_request_full[store_capacity]:
  `compile_store_memory cenv src (Var out)
     (lowered_value_type cenv h) (lowered_value_type cenv h) ss = ((),stail)` by
    (qpat_assum `(if is_word_type _ then _ else _) ss = _` mp_tac >>
     qpat_assum `dst = Var out` mp_tac >>
     qpat_assum `~is_word_type (lowered_value_type cenv h)` mp_tac >>
     qpat_assum `~(~is_bytestring_type (lowered_value_type cenv h) /\ _)` mp_tac >>
     qpat_assum `type_memory_bytes cenv _ = type_memory_size rt` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `is_bytestring_type (lowered_value_type cenv h)` >>
     Cases_on `type_memory_size rt` >>
     simp[compile_store_memory_def, compile_copy_memory_def]) >>
  `ptr_mem_ok cx (lowered_value_type cenv h) v src Gu tu z` by
    (qpat_assum `ptr_val_ok _ _ _ src Gu tu z` mp_tac >>
     qpat_assum `~is_word_type (lowered_value_type cenv h)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[ptr_val_ok_def]) >>
  `type_memory_size rt + 64 < dimword (:256)` by
    (qpat_assum `type_memory_size rt < 18446744073709551616` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[wordsTheory.dimword_def]) >>
  `w2n (n2w (b+off) : bytes32) = b+off` by simp[wordsTheory.w2n_n2w] >>
  `(type_memory_size rt <> 0 ==>
     ?x. src = Var x /\ ptr_covers Gu tu x z (type_memory_size rt) /\
         w2n sw + type_memory_size rt <= z.vs_alloca_next) /\
   (type_memory_size rt <> 0 ==>
     ptr_covers Gu tu out z (type_memory_size rt) /\
     w2n (n2w (b+off) : bytes32) + type_memory_size rt <= z.vs_alloca_next)` by
    (qpat_assum `~is_word_type _ /\ type_memory_size rt <> 0 ==> _` mp_tac >>
     qpat_assum `~is_word_type _ ==> !w. eval_operand src z = SOME w ==> _` mp_tac >>
     qpat_assum `~is_word_type (lowered_value_type cenv h)` mp_tac >>
     qpat_assum `eval_operand src z = SOME sw` mp_tac >>
     qpat_assum `ptr_covers Gu tu out z (type_memory_size rt)` mp_tac >>
     qpat_assum `b+off+type_memory_size rt <= z.vs_alloca_next` mp_tac >>
     qpat_assum `w2n (n2w (b+off) : bytes32) = b+off` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  drule_all (extcallReturnDefaultMemoryJointTheory.return_default_memory_store_capacity_joint
    |> Q.INST [`sty` |-> `rt`] |> SRULE []) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `r` (qx_choose_then `Gr` (qx_choose_then `tr` mp_tac)))) >>
  qpat_assum `w2n (n2w (b+off) : bytes32) = b+off` mp_tac >>
  qpat_assum `z.vs_inst_idx = LENGTH ss.cs_current_insts` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >>
  qexistsl_tac [`r`,`Gr`,`tr`] >>
  simp[typed_copy_state_frame_def, typed_copy_frame_def] >>
  conj_tac
  >- (conj_tac
      >- (qpat_x_assum `r with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|> = z` mp_tac >>
          simp[venom_state_component_equality]) >>
      rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Resume extcall_request_full[store_zero]:
  FAIL_TAC "store-zero"
QED

Resume extcall_request_full[stored_tail]:
  FAIL_TAC "stored-tail"
QED

(* (1) Operands and request, at (DF H, lo): the operand judgments run the
   lowering up to the extcodesize check against the source up to the built
   calldata, on one witness; whatever runs the rest of eval_ext_call from a
   ready request (source, memory and pointer facts at t), with the lowered
   call step at sp and the return handling at sr, runs the whole call.
   The pointer side of a ready request: the call's operands are untainted,
   the calldata bytes are untainted and lie inside the site call_offset
   points into, and the return buffer lies inside the site buf_op points
   into. *)
Theorem extcall_request_kwargs_outcome_from_step:
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       Inv [] [] H es G0 tn0 s0) /\
  (!pre e suf vals mid G tn t.
     xs = pre ++ e::suf /\ LENGTH vals = LENGTH pre /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
          Inv pre vals H mid G tn t) ==>
     gas_outcome_full
       (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (cx_tops cx) cx st0
       (bind (eval_expr cx e) (read_result cx)) (mid,t,G,tn)
       (\H res ee G' tn' u. ?v. res = INL v /\
          Inv (pre ++ [e]) (vals ++ [v]) H ee G' tn' u)
       (\H res ee gt r. expr_exit res r)) /\
  (!vals mid G tn t.
     LENGTH vals = LENGTH xs /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
          Inv xs vals H mid G tn t) ==>
     gas_outcome_full
       (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (cx_tops cx) cx st0 (return ([] : value list)) (mid,t,G,tn)
       (\H res ee G' tn' u. res = INL [] /\
          Inv xs vals H ee G' tn' u)
       (\H res ee gt r. expr_exit res r)) ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_exprs cx xs) (es,s0,G0,tn0)
    (\H res ee G tn t. ?vs. res = INL vs /\
       LENGTH vs = LENGTH xs /\ Inv xs vs H ee G tn t)
    (\H res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  `!remaining pre vals mid t G tn.
     xs = pre ++ remaining /\ LENGTH vals = LENGTH pre /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
       Inv pre vals H mid G tn t) ==>
     gas_outcome_full
       (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (cx_tops cx) cx st0 (eval_exprs cx remaining) (mid,t,G,tn)
       (\H res ee G' tn' u. ?ws. res = INL ws /\
         LENGTH ws = LENGTH remaining /\ Inv xs (vals ++ ws) H ee G' tn' u)
       (\H res ee gt r. expr_exit res r)` by
    (Induct >> rpt gen_tac >> strip_tac
     >- (gvs[] >> simp[Once evaluate_def] >>
         irule gas_outcome_full_post_mono >>
         first_x_assum (irule_at Any) >> simp[] >> metis_tac[]) >>
     rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >>
     irule gas_outcome_full_bind_all >>
     conj_tac
     >- (gen_tac >> BETA_TAC >> irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
         simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
              vyperStorageTraceTheory.storage_trace_frame_return]) >>
     conj_tac
     >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
         goal_assum (drule_at Any) >> fs[]) >>
     conj_tac
     >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >>
         first_assum ACCEPT_TAC) >>
     conj_tac
     >- (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
         simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
              vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
     qexists `\H res ee G' tn' u. ?v. res = INL v /\
       Inv (pre ++ [h]) (vals ++ [v]) H ee G' tn' u` >>
     reverse conj_tac
     >- (irule gas_outcome_full_post_mono >>
         qpat_x_assum `!pre e suf vals mid G tn t. _` (irule_at Any) >>
         qexistsl [`vals`,`remaining`,`pre`] >> simp[] >>
         rpt strip_tac >> Cases_on `res` >>
         fs[exprSimDefsTheory.expr_exit_def,stmtSimPropsTheory.expr_exit_INR_type]) >>
     rpt gen_tac >> BETA_TAC >> strip_tac >>
     `valid_horizon cx st0 (storage_trace_horizon mid'.storage_trace)
        mid'.storage_trace` by
       fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
     `?v. res = INL v` by metis_tac[] >>
     qpat_x_assum `res = INL v` SUBST_ALL_TAC >> simp[] >>
     qpat_x_assum `!pre vals mid t G tn. _`
       (qspecl_then [`pre ++ [h]`,`vals ++ [v]`,`mid'`,`t'`,`G1`,`tn1`] mp_tac) >>
     (impl_tac >- fs[APPEND_ASSOC]) >> disch_tac >>
     drule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`)
       (Q.INST [`f` |-> `SUM_MAP (CONS v) I`,
       `source'` |-> `bind (eval_exprs cx remaining) (\vs. return (v::vs))`]
       (INST_TYPE [alpha |-> ``:value list``, beta |-> ``:value list``]
         gas_outcome_full_source_map)) >>
     disch_then (qspecl_then [`v`,`remaining`] mp_tac) >>
     impl_tac
     >- (simp[] >> gen_tac >> Cases_on `eval_exprs cx remaining es'` >>
         Cases_on `q` >> simp[vyperStateTheory.bind_def,vyperStateTheory.return_def]) >>
     disch_tac >>
     irule gas_outcome_full_post_mono >> goal_assum (drule_at Any) >>
     simp[] >> conj_tac
     >- (rpt strip_tac >> gvs[] >>
         qpat_x_assum `Inv _ _ _ _ _ _ _` mp_tac >>
         pure_rewrite_tac[GSYM APPEND_ASSOC,APPEND] >> simp[]) >>
     rpt strip_tac >> gvs[] >> rename1 `expr_exit (SUM_MAP _ _ rv) r` >>
     Cases_on `rv` >> fs[exprSimDefsTheory.expr_exit_def]) >>
  first_x_assum (qspecl_then [`xs`,`[]`,`[]`,`es`,`s0`,`G0`,`tn0`] mp_tac) >>
  simp[]
QED

Resume extcall_request_full[request_main]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule bodyFullExtCallRequestInterfacesTheory.extcall_request_source_boundary >>
  strip_tac >>
  Cases_on `args` >- gvs[] >>
  rename1 `ExtCall stat skip (fname,arg_types,ret_type) opts` >>
  fs[] >>
  drule_all bodyFullExtCallRequestInterfacesTheory.extcall_request_operands_code_slice >>
  strip_tac >>
  qpat_assum `compile_expr cenv ty (gas_shadow_expr _) shadow_sa = _`
    (mp_tac o SIMP_RULE (srw_ss()) [gas_shadow_expr_def]) >>
  disch_then (mp_then Any mp_tac
    bodyFullExtCallRequestInterfacesTheory.extcall_request_operands_code_slice) >>
  disch_then drule >> strip_tac >>
  rename1 `lower_value compile_expr cenv (BaseT AddressT)
     (gas_shadow_expr h) shadow_sa = (shadow_ao,shadow_s1)` >>
  qpat_assum `compile_external_call_kwargs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s5 = _`
    (mp_then Any mp_tac
      bodyFullExtCallRequestInterfacesTheory.extcall_request_buffer_layout) >>
  strip_tac >>

  `shadow_ao = ao /\ gas_shadow_state s1 shadow_s1` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`, `ty` |-> `BaseT AddressT`, `e` |-> `h`]
       gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value) >>
     rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  qpat_x_assum `shadow_ao = ao` SUBST_ALL_TAC >>
  qpat_x_assum `ann = ret_type` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `vv = _` SUBST_ALL_TAC >>
  rename1 `compile_ext_call_args compile_expr cenv _ _ _ shadow_s1 = (shadow_av,shadow_s2)` >>
  `gas_shadow_compiles
    (compile_ext_call_args compile_expr cenv (DROP (LENGTH arg_types) t)
      (MAP (lowered_value_type cenv) (TAKE (LENGTH arg_types) t))
      (TAKE (LENGTH arg_types) t))
    (compile_ext_call_args compile_expr cenv
      (MAP gas_shadow_expr (DROP (LENGTH arg_types) t))
      (MAP (lowered_value_type cenv) (TAKE (LENGTH arg_types) t))
      (MAP gas_shadow_expr (TAKE (LENGTH arg_types) t)))` by
    (irule (SIMP_RULE bool_ss []
       (Q.INST [`sh` |-> `T`] gasShadowCompileHelpersTheory.gas_shadow_compiles_ext_call_args)) >>
     simp[gasShadowCompileTheory.gas_shadow_compile_expr]) >>
  `shadow_av = av /\ gas_shadow_state s2 shadow_s2` by
    (qpat_x_assum `gas_shadow_compiles (compile_ext_call_args _ _ _ _ _) _` mp_tac >>
     rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`s1`,`shadow_s1`] mp_tac) >>
     fs[GSYM listTheory.MAP_TAKE,GSYM listTheory.MAP_DROP,
       listTheory.MAP_MAP_o,combinTheory.o_DEF,SF boolSimps.ETA_ss]) >>
  gvs[] >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `expr_body_pre cenv cx env h es` by metis_tac[] >>
  `gas_admissible (bind (eval_expr cx h) (read_result cx)) expr_res_ok es` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  once_rewrite_tac[exprSimExtCallCaseTheory.eval_extcall_stages] >>
  simp[Once TAKE_def, Once DROP_def] >>
  mp_tac (Q.INST [`addr` |-> `h`, `ao` |-> `ao`, `cenv` |-> `cenv`, `d` |-> `d`,
      `env` |-> `env`, `sa` |-> `sa`, `sb` |-> `s1`,
      `shadow_func` |-> `shadow_func`, `shadow_sa` |-> `shadow_sa`,
      `shadow_sb` |-> `shadow_s1`, `tops` |-> `tops`]
    bodyFullExtCallRequestHeadTheory.extcall_request_head_outcome) >>
  impl_tac >- simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ P _` >>
  drule (Q.INST [`Q'` |-> `\H res ee G tn t. P H res ee G tn t /\ ~t.vs_halted`,
      `R'` |-> `\H res ee gt r. expr_exit res r`] gas_outcome_full_post_path) >>
  disch_then (qspec_then `P` mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      drule fragGasOriginPtrTheory.gas_origin_ptr_path_projections >> strip_tac >>
      metis_tac[fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted]) >>
  strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ P _` kall_tac >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_bind_all >>
  conj_tac
  >- (rpt gen_tac >> BETA_TAC >>
      irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      reverse conj_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
      gen_tac >> BETA_TAC >> irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      reverse conj_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
      gen_tac >> simp[vyperStorageTraceTheory.storage_trace_frame_ext_call]) >>
  conj_tac
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_values >>
      goal_assum (drule_at Any) >> fs[]) >>
  conj_tac
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_values >>
      first_assum ACCEPT_TAC) >>
  conj_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  qexists `\H res ee G tn t. P H res ee G tn t /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_mono >> goal_assum (drule_at Any) >> simp[] >>
      rpt strip_tac >> Cases_on `res`
      >- (qpat_x_assum `expr_exit _ _` mp_tac >>
          simp[exprSimDefsTheory.expr_exit_def]) >>
      qexists `y` >> simp[] >>
      qpat_x_assum `expr_exit _ _` mp_tac >>
      simp[stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt gen_tac >> strip_tac >>
  Q.UNABBREV_TAC `P` >> BETA_TAC >>
  disj1_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
      mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (mp_tac o BETA_RULE o Q.SPEC `storage_trace_horizon mid.storage_trace`) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  strip_tac >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  qexists `[v]` >> conj_tac >- REFL_TAC >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid t' /\
     storage_well_formed_on cx mid (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t'` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
       (mp_tac o BETA_RULE o Q.SPEC `H`) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     simp[expr_post_def] >> rpt strip_tac >> first_assum ACCEPT_TAC) >>
  `expr_sim_inv cenv cx env mid` by
    (`expr_sim_inv cenv cx env (mid with gas_obs := [])` suffices_by simp[] >>
     irule (cj 1 abiEncodeArgsTypingTheory.abi_encode_args_success_typed) >>
     qexistsl_tac [`[h]`, `es with gas_obs := gas_explicit marks s0.vs_gas_readings`, `[v]`] >>
     simp[] >>
     qpat_assum `!tail. eval_exprs cx [h] _ = _` (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE [APPEND_NIL]))) >>
  `body_exprs_full_ok cx (TAKE (LENGTH arg_types) t)` by
    (qpat_assum `!tail. eval_exprs cx [h] _ = _`
       (qspec_then `[]` (mp_tac o PURE_REWRITE_RULE [APPEND_NIL])) >>
     disch_then (fn th => qpat_x_assum
       `!s target u. eval_exprs cx [h] s = _ ==> _` (mp_tac o C MATCH_MP th)) >> simp[]) >>
  `sa.cs_next_var <= s1.cs_next_var` by
    (qpat_assum `lower_value compile_expr cenv (BaseT AddressT) h sa = _`
       (mp_then Any mp_tac exprSimSourceTheory.expr_body_pre_lower_value_word_shape) >>
     simp[is_word_type_def] >>
     disch_then (qspecl_then [`cx`,`env`,`es`] mp_tac) >> simp[]) >>
  `local_ptrs_reserved cenv s1` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `return_buf_frame d cenv s1 t'` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[] >>
     metis_tac[expr_post_def]) >>
  `EVERY (\e. ~expr_has_effect e) t` by
    (drule bodyFullExtCallRequestInterfacesTheory.extcall_request_tail_effect_free >> simp[]) >>
  `!e st. MEM e (TAKE (LENGTH arg_types) t) /\ expr_sim_inv cenv cx env st ==>
      expr_body_pre cenv cx env e st` by
    metis_tac[rich_listTheory.MEM_TAKE] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qpat_assum `compile_ext_call_args compile_expr cenv _ _ _ shadow_s1 = (av,shadow_s2)`
    (assume_tac o REWRITE_RULE [GSYM MAP_TAKE, GSYM MAP_DROP]) >>
  `EVERY (\e. ~expr_has_effect e)
     (TAKE (LENGTH arg_types) t ++ DROP (LENGTH arg_types) t)` by
    (pure_rewrite_tac[TAKE_DROP] >> first_assum ACCEPT_TAC) >>
  drule_all extcall_request_positional_outcome >>
  disch_then (qspec_then `PG` assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Pargs _` >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_bind_all >>
  conj_tac
  >- (rpt gen_tac >> BETA_TAC >>
      irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.storage_trace_frame_ext_call,
           vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  conj_tac
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_values >>
      goal_assum (drule_at Any) >> fs[]) >>
  conj_tac
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_values >>
      first_assum ACCEPT_TAC) >>
  conj_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  qexists `Pargs` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_mono >> goal_assum (drule_at Any) >> simp[] >>
      rpt strip_tac >> Cases_on `res`
      >- (qpat_x_assum `expr_exit _ _` mp_tac >>
          simp[exprSimDefsTheory.expr_exit_def]) >>
      qexists `y` >> simp[] >>
      qpat_x_assum `expr_exit _ _` mp_tac >>
      simp[stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt gen_tac >> strip_tac >>
  Q.UNABBREV_TAC `Pargs` >> BETA_TAC >>
  disj1_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid'.storage_trace)
      mid'.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H mid'.storage_trace ==> _`
    (mp_tac o BETA_RULE o Q.SPEC `storage_trace_horizon mid'.storage_trace`) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  strip_tac >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  qexists `vs` >> conj_tac >- REFL_TAC >>
  FAIL_TAC "keyword-outcome"
QED

Finalise extcall_request_full
