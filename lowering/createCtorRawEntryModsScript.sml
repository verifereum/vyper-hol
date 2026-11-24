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
  fragGasOriginPtr exprSimProps

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
