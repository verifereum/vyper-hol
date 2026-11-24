Theory createCtorRawEntryMods
Ancestors
  createCtorRawEntry createExprSizeExitDefsMods
  bodyFullExtCallDirectState bodyFullMemoryFrames bodyFullAbiEncodeCopy
  bodyPtrMakeArrayPrimitiveInstall bodyPtrMakeArrayEmission
  abiEncoderWindowLeaves abiEncoderWindowPhase typedCopyOriginPtrBase
  abiBuiltinAllocation emitHelperProps fragGasOrigin fragExec context
  gasEventsFuel exprLoweringProps venomMemDefs abiEncoderWindowContract
  venomExecSemantics venomState venomInst words
  list arithmetic finite_map pred_set createCtorBlueprintEntryMods
  bodyFullStoreSlotsAddresses abiDecodePtrBytesTail abiEncoderWindowSequence ptrDiscipline bodyPtrDefs
  exprSimAbiEncodeExecFrame exprSimAbiEncodeFramedArrayBody ghostPcTransportPtr
  loweringPosts freshWrites assignTuplePtrCopyLen memoryReadProps
  fragGasOriginPtr exprSimProps bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit typedMemoryCopy loweringSlice loweringStateRelDefs

(* Each instruction in the raw prologue is nonterminating and is not an
   INVOKE.  The supplied origin edge therefore fixes its result. *)

Theorem raw_entry_copy_observed[local]:
  emit_void MCOPY [Var root;Var src;len] a = ((),b) /\
  fn_has_code a b func /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  lookup_var root s = SOME w /\ lookup_var src s = SOME p /\
  eval_operand len s = SOME n /\ gas_origin_edge F explicit ctx func s marks (OK t) ==>
  t = (mcopy (w2n w) (w2n p) (w2n n) s) with vs_inst_idx := SUC s.vs_inst_idx
Proof
  strip_tac >> drule_all emit_void_fetch_boundary >> strip_tac >>
  `step_inst_base (mk_inst a.cs_next_id MCOPY [Var root;Var src;len] []) s =
   OK (mcopy (w2n w) (w2n p) (w2n n) s)` by
    simp[step_inst_base_opcode_eqs,mk_inst_def,eval_operand_def] >>
  gvs[gas_origin_edge_def,step_inst_non_invoke,exit_result_def,mk_inst_def,is_terminator_def]
QED

Theorem raw_entry_copy_window[local]:
  emit_void MCOPY [Var root;Var src;len] a = ((),b) /\
  fn_has_code a b func /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\ ~s.vs_halted /\
  alloca_inv s /\ alloca_room ctx func s /\
  lookup_var root s = SOME w /\ lookup_var src s = SOME p /\
  eval_operand len s = SOME n /\
  t = (mcopy (w2n w) (w2n p) (w2n n) s) with vs_inst_idx := SUC s.vs_inst_idx ==>
  window_phase ctx func a b {} [(w2n w,w2n n)] s t
Proof
  strip_tac >> qpat_assum `t = _` SUBST1_TAC >>
  `eval_operand (Var root) s = SOME (n2w (w2n w)) /\
   eval_operand (Var src) s = SOME (n2w (w2n p)) /\
   eval_operand len s = SOME (n2w (w2n n))` by simp[eval_operand_def] >>
  `w2n w < dimword(:256) /\ w2n p < dimword(:256) /\ w2n n < dimword(:256)` by simp[w2n_lt] >>
  drule_all window_emit_copy_run >> simp[] >> strip_tac >>
  `ci_mono a b` by metis_tac[ci_mono_emit_void,pairTheory.SND] >>
  `window_seq a b s (mcopy (w2n w) (w2n p) (w2n n) s)` by
    fs[abiEncoderWindowSequenceTheory.window_seq_def,ci_mono_def,
       mcopy_def,write_memory_with_expansion_def,lookup_var_def] >>
  `alloca_inv (mcopy (w2n w) (w2n p) (w2n n) s) /\
   alloca_room ctx func (mcopy (w2n w) (w2n p) (w2n n) s) /\
   window_alloca_growth s (mcopy (w2n w) (w2n p) (w2n n) s)` by
    (fs[alloca_inv_def,allocas_non_overlapping_def,alloca_next_valid_def,
        alloca_room_def,pending_alloca_size_def,window_alloca_growth_def,
        mcopy_def,write_memory_with_expansion_def] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> rw[] >> fs[]) >>
  `abi_encoder_registered_effect {} [(w2n w,w2n n)] s
      (mcopy (w2n w) (w2n p) (w2n n) s)` by
    simp[abiEncoderPrimitiveEffectTheory.abi_encoder_registered_output_copy] >>
  `SUC (LENGTH a.cs_current_insts) = LENGTH b.cs_current_insts` by
    (drule_all emit_void_fetch_boundary >> strip_tac >> simp[]) >>
  qpat_assum `s.vs_inst_idx = LENGTH a.cs_current_insts` SUBST1_TAC >>
  pop_assum SUBST1_TAC >> irule window_seq_phase >>
  simp[mcopy_def,write_memory_with_expansion_def]
QED

(* The physical endpoint selects one taint result, valid at every admissible floor. *)

Theorem raw_entry_copy_step[local]:
  compile_copy_memory_dynamic (Var root) (Var src) len a = ((),b) /\
  fn_has_code a b func /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\ ~s.vs_halted /\
  alloca_inv s /\ alloca_room ctx func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  lookup_var root s = SOME w /\ lookup_var src s = SOME p /\
  eval_operand len s = SOME n /\ op_taint tn len = {} /\
  ptr_covers G tn root s (w2n n) /\ ptr_covers G tn src s (w2n n) /\
  w2n w + w2n n <= s.vs_alloca_next /\ w2n p + w2n n <= s.vs_alloca_next /\
  gas_origin_edge F explicit ctx func s marks (OK t) ==>
  ?tf. window_phase ctx func a b {} [(w2n w,w2n n)] s t /\
       typed_copy_state_frame a (w2n w) (w2n n) s t /\
       abi_encode_exec_frame func s t /\
       t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
       (!x. lookup_var x t = lookup_var x s) /\
       (!k D. allocas_from k s ==>
          gas_origin_ptr_path (D,k,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G,tf)) /\
       tf.t_var = tn.t_var /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
       tf.t_imm = tn.t_imm /\
       (!i. (i < w2n w \/ w2n w + w2n n <= i) /\ i IN tf.t_mem ==> i IN tn.t_mem)
Proof
  simp_tac bool_ss [compile_copy_memory_dynamic_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all raw_entry_copy_observed >> disch_tac >>
  drule_all raw_entry_copy_window >> disch_tac >>
  drule_all emit_void_fetch_boundary >> strip_tac >>
  qabbrev_tac `i = mk_inst a.cs_next_id MCOPY [Var root;Var src;len] []` >>
  qabbrev_tac `r = mcopy (w2n w) (w2n p) (w2n n) s` >>
  `inst_mem_below_frontier i s /\ inst_dload_in_section i s` by
    simp[Abbr `i`,mk_inst_def,unitTransformDefsTheory.inst_mem_below_frontier_def,
         memSafeRunTheory.inst_dload_in_section_def,
         contextCodegenRelTheory.source_memory_read_ranges_def,
         codegenRelTheory.sized_source_write_range_def,
         codegenRelTheory.source_memory_write_ranges_def,eval_operand_def] >>
  `typed_copy_state_frame a (w2n w) (w2n n) s t /\
   abi_encode_exec_frame func s t /\
   t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   (!x. lookup_var x t = lookup_var x s)` by
    (qpat_assum `t = _` SUBST1_TAC >> simp[Abbr `r`,
     typedMemoryCopyTheory.typed_copy_mcopy_state_frame,
     exprSimAbiEncodeExecFrameTheory.abi_encode_exec_frame_mcopy,
     exprSimAbiEncodeExecFrameTheory.abi_encode_exec_frame_inst_idx,
     mcopy_def,write_memory_with_expansion_def,lookup_var_def]) >>
  `!k D. allocas_from k s ==>
     gas_origin_ptr_path (D,k,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G,step_taint i s r tn)` by
    (rpt strip_tac >> qpat_assum `t = _` SUBST1_TAC >>
     qunabbrev_tac `i` >> qunabbrev_tac `r` >>
     irule abi_encode_mcopy_origin_path >> simp[] >> qexists_tac `bb` >> simp[]) >>
  qpat_x_assum `t = _` kall_tac >>
  qexists_tac `step_taint i s r tn` >> asm_rewrite_tac[] >>
  `eval_operand (Var root) s = SOME w /\ eval_operand (Var src) s = SOME p` by
    simp[eval_operand_def] >>
  simp[Abbr `i`,Abbr `r`,fragExecPtrTheory.mcopy_operand_ghost_frame,
       decoderGhostFramePtrTheory.step_taint_nonmemory_frame,mk_inst_def] >>
  rpt strip_tac >> fs[] >> decide_tac
QED

Theorem ctor_raw_destination_actual_mods:
  compile_alloc_buffer capacity se = (buf,a) /\ fn_has_code se a func /\
  compile_copy_memory_dynamic buf.buf_operand (Var src) (Var len) a = ((),b) /\
  fn_has_code a b func /\ emit_op ADD [buf.buf_operand;Var len] b = (dst,c) /\
  fn_has_code b c func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce se /\
  capacity < dimword (:256) /\ w2n n <= capacity /\
  not_fresh_at se src /\ not_fresh_at se len /\
  lookup_var src s = SOME p /\ lookup_var len s = SOME n /\
  ptr_covers G tn src s (w2n n) /\ op_taint tn (Var len) = {} /\
  w2n p + w2n n <= s.vs_alloca_next /\
  (!x z. ce.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at se x) /\
  (!x z. ce.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at se x) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\
    immutable_frame_mods func ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = se.cs_current_bb /\ s.vs_inst_idx = LENGTH se.cs_current_insts /\
  gas_origin_edge F explicit ctx func s am (OK u) /\
  gas_origin_edge F explicit ctx func u bm (OK t) /\
  gas_origin_edge F explicit ctx func t cm (OK v) ==>
  ?root pbase out Gv tv inst.
    buf.buf_operand = Var root /\ dst = Var out /\
    inst = mk_inst se.cs_next_id ALLOCA [Lit (n2w capacity)] [root] /\
    MEM inst (fn_insts func) /\ not_local_ptr ce ee.scopes root /\
    abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      se.cs_next_id pbase capacity root out (w2n n) [] c v Gv tv /\
    pure_frame ce func ee se s v /\
    (!x. not_fresh_at se x ==> lookup_var x v = lookup_var x s /\
      FLOOKUP Gv x = FLOOKUP G x /\ op_taint tv (Var x) = op_taint tn (Var x)) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK v,Gv,tv))
Proof
  cheat
QED

(* At floor zero only the common part of the ghost invariant remains. *)
Theorem raw_entry_saved_view[local]:
  abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst off prefix a u Gu tu <=>
  abi_encode_saved_state ctx func ce cx st0 ee DF 0 d se s G tn
    shared pbase capacity root dst off prefix a u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    immutable_frame_mods func ce cx ee u /\
    (!i. i < lo /\ i IN tu.t_mem ==>
      imm_section_dead_mods ce (mem_bytes_at 0 lo u.vs_memory) i) /\
    (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==>
      FLOOKUP Gu x = NONE /\ op_taint tu (Var x) = {}) /\
    allocas_from lo u /\ lo <= u.vs_alloca_next)
Proof
  simp_tac bool_ss [abi_encode_saved_state_mods_def, abi_encode_saved_state_def,
    ghost_inv_at_mods_def, ghost_inv_at_def, ghost_kept_at_def,
    allocas_from_def, DECIDE ``!n:num. ~(n < 0) /\ 0 <= n``,
    IMP_CONJ_THM, FORALL_AND_THM] >>
  CONV_TAC (AC_CONV (CONJ_ASSOC, CONJ_COMM))
QED

(* Preserve the immutable relation of every module, not just the active one. *)

Theorem raw_entry_registered_immutable_frame[local]:
  immutable_frame_mods func ce cx ee u /\ local_ptrs_reserved ce se /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP u.vs_allocas inst.inst_id = SOME (pbase,capacity) /\
  typed_copy_state_frame se pbase capacity u v ==>
  immutable_frame_mods func ce cx ee v
Proof
  strip_tac >>
  qpat_assum `typed_copy_state_frame _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def]) >>
  `v.vs_data_section = u.vs_data_section /\ v.vs_allocas = u.vs_allocas /\
   v.vs_alloca_next = u.vs_alloca_next` by
    (qpat_assum `_ = u`
      (mp_tac o AP_TERM ``\z. (z.vs_data_section,z.vs_allocas,z.vs_alloca_next)``) >> simp[]) >>
  `!src id b sz. local_region (ce with ce_module := src) ee.scopes v id b sz ==>
    local_region (ce with ce_module := src) ee.scopes u id b sz` by
    (simp[local_region_def] >> rpt strip_tac >>
     `not_fresh_at se p` by metis_tac[local_ptrs_reserved_def] >> metis_tac[]) >>
  fs[immutable_frame_mods_def, immutables_rel_mods_def, immutable_alloca_sep_mods_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> irule immutables_rel_mem_agree >>
      qexists_tac `u` >> simp[] >> conj_tac
      >- fs[typed_copy_frame_def] >>
      disch_tac >> rpt gen_tac >> strip_tac >>
      qpat_assum `!src tops. ALOOKUP ce.ce_modules src = SOME tops ==> immutable_alloca_sep _ _ _ _ _`
        (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [immutable_alloca_sep_def])) >>
      `regions_disjoint off (type_memory_size tv) pbase capacity` by metis_tac[] >>
      fs[typed_copy_frame_def, loweringStateRelDefsTheory.regions_disjoint_def]) >>
  rpt gen_tac >> strip_tac >> irule immutable_alloca_sep_fields >>
  qexistsl_tac [`u`,`ee`] >> simp[] >> metis_tac[]
QED

Theorem raw_entry_saved_phase_mods[local]:
  abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root root 0 [] a u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  ci_mono a c /\ window_phase ctx func a c {} outs u v /\
  abi_encode_exec_frame func u v /\
  (!D. gas_origin_ptr_path (D,0,explicit,ctx,func,PG) (u,Gu,tu) [] (OK v,Gv,tv)) /\
  (!x. not_fresh_at a x ==>
    FLOOKUP Gv x = FLOOKUP Gu x /\ op_taint tv (Var x) = op_taint tu (Var x)) /\
  tv.t_stor = tu.t_stor /\ tv.t_trans = tu.t_trans /\ tv.t_imm = tu.t_imm /\
  EVERY (\(p,n). pbase <= p /\ p+n <= pbase+capacity) outs /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_id = shared /\ inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  (!i. EVERY (\(p,n). i < p \/ p+n <= i) outs /\ i IN tv.t_mem ==> i IN tu.t_mem) /\
  typed_copy_state_frame se pbase capacity u v ==>
  (pure_frame ce func ee se u v /\ wb_frame ce ee ee se u v) /\
  abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root root 0 [] c v Gv tv
Proof
  simp_tac bool_ss [raw_entry_saved_view] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `(pure_frame ce func ee se u v /\ wb_frame ce ee ee se u v) /\
   abi_encode_saved_state ctx func ce cx st0 ee DF 0 d se s G tn
     shared pbase capacity root root 0 [] c v Gv tv` by
    (irule abi_encode_saved_state_phase_pure >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qexistsl_tac [`Gu`,`PG`,`a`,`explicit`,`{}:num set`,`outs`,`tu`] >>
     asm_simp_tac (srw_ss()) [] >>
     qexistsl_tac [`inst`,`root`] >> simp[]) >>
  asm_rewrite_tac[] >> qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> immutable_frame_mods _ _ _ _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `abi_encode_saved_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_def]) >>
  `lo <= pbase` by
    (qpat_assum `allocas_from lo u` (drule_then irule o REWRITE_RULE [allocas_from_def]) >> simp[]) >>
  conj_tac
  >- (irule raw_entry_registered_immutable_frame >>
      qpat_assum `typed_copy_state_frame _ _ _ u v` (irule_at Any) >>
      qexists_tac `inst` >> simp[]) >>
  qpat_assum `typed_copy_state_frame _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def]) >>
  `v.vs_allocas = u.vs_allocas /\ v.vs_alloca_next = u.vs_alloca_next` by
    (qpat_assum `_ = u` (mp_tac o AP_TERM ``\z. (z.vs_allocas,z.vs_alloca_next)``) >> simp[]) >>
  `mem_bytes_at 0 lo v.vs_memory = mem_bytes_at 0 lo u.vs_memory` by fs[typed_copy_frame_def] >>
  `!i. i < lo /\ i IN tv.t_mem ==> i IN tu.t_mem` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >>
     simp_tac bool_ss [EVERY_MEM, pairTheory.FORALL_PROD] >> rpt strip_tac >>
     qpat_assum `EVERY _ outs`
       (drule_then strip_assume_tac o SRULE [EVERY_MEM, pairTheory.FORALL_PROD]) >>
     simp[] >> decide_tac) >>
  asm_rewrite_tac[] >> conj_tac
  >- (rpt strip_tac >> qpat_assum `!i. i < lo /\ i IN tu.t_mem ==> _` irule >> simp[]) >>
  reverse conj_tac >-
    (qpat_assum `v.vs_allocas = u.vs_allocas` (fn th =>
       PURE_REWRITE_TAC [allocas_from_def, th]) >>
     qpat_assum `allocas_from lo u` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  qx_gen_tac `x` >> strip_tac >>
  `not_fresh_at se x` by metis_tac[local_ptrs_reserved_imm_base] >>
  `not_fresh_at a x` by metis_tac[not_fresh_at_mono] >>
  qpat_assum `!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> _`
    (qspec_then `x` mp_tac) >>
  qpat_assum `!x. not_fresh_at a x ==> FLOOKUP Gv x = _ /\ _`
    (qspec_then `x` mp_tac) >> simp[]
QED
