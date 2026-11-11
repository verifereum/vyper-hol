(* Check the full ranges accessed by the actual tuple staging instructions. *)
Theory abiTupleEncodeMemoryChecks
Ancestors
  abiTupleEncodePrepare abiTupleEncodeSlot abiTupleEncodeResult abiTupleEncodeInput
  abiBuiltinPrefix abiDecoderDynamicLoopSetup abiEncoderWindowSequence
  bodyLiteralBufferMemory allocaFootprint instMemFrontier fragExecMem
  abiBuiltinAllocation venomMemDefs finite_map
  compileEnv emitHelperProps exprLoweringProps venomState venomExecSemantics
  words list arithmetic abiBuiltinEncodeWord exprLowering emitHelper abiDecoderContract abiDecoderGuards context abiTupleProps venomInst abiDecoderReentry

Theorem abi_tuple_encode_write_mem_ok[local]:
  (if is_word_type ty then emit_void MSTORE [dst;op]
   else compile_copy_memory dst op (type_memory_bytes ce ty)) st = ((),final) /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\
  d+type_memory_bytes ce ty <= s.vs_alloca_next /\
  abi_tuple_encode_input sf ce ty at av op next lo hi s /\
  (~is_word_type ty ==> ?p. eval_operand op s = SOME (n2w p) /\
    p < dimword (:256) /\ p+type_memory_bytes ce ty <= s.vs_alloca_next) ==>
  run_inst_seq_mem_ok (emitted_insts st final) s
Proof
  Cases_on `is_word_type ty`
  >- (simp[abi_tuple_encode_input_def] >> rpt strip_tac >>
      `type_memory_bytes ce ty = 32` by metis_tac[abi_builtin_encode_word_info] >>
      drule emit_mstore_mem_ok >> disch_then irule >> simp[]) >>
  simp[] >> strip_tac >>
  Cases_on `type_memory_bytes ce ty = 0`
  >- (gvs[compile_copy_memory_def, comp_return_def] >>
      simp[emitted_insts_def, run_inst_seq_mem_ok_def]) >>
  `emit_void MCOPY [dst;op;Lit (n2w (type_memory_bytes ce ty))] st = ((),final)` by
    (Cases_on `type_memory_bytes ce ty` >> gvs[compile_copy_memory_def]) >>
  `type_memory_bytes ce ty < dimword (:256)` by fs[abi_tuple_encode_input_def] >>
  drule emit_mcopy_mem_ok >> disch_then irule >> simp[eval_operand_def] >> metis_tac[]
QED

Theorem abi_tuple_encode_slot_mem_ok[local]:
  compile_abi_tuple_slot ce buf off op ty st = ((),final) /\
  eval_operand buf s = SOME (n2w baddr) /\ baddr+off < dimword (:256) /\ lo <= hi /\
  baddr+off+type_memory_bytes ce ty <= s.vs_alloca_next /\
  abi_tuple_encode_input sf ce ty at av op st.cs_next_var lo hi s /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  (~is_word_type ty ==> ?p. eval_operand op s = SOME (n2w p) /\
    p < dimword (:256) /\ p+type_memory_bytes ce ty <= s.vs_alloca_next) ==>
  run_inst_seq_mem_ok (emitted_insts st final) s
Proof
  strip_tac >> drule abi_tuple_encode_slot_shape >> strip_tac >>
  qpat_x_assum `compile_abi_tuple_slot _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [compile_abi_tuple_slot_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >>
  rename1 `emit_op ADD [buf;Lit (n2w off)] st = (dst,address_st)` >>
  qpat_assum `emit_op ADD _ _ = _` (fn eq =>
    qpat_x_assum `(\(dst,cs'). _) _ = _` (assume_tac o SIMP_RULE (srw_ss()) [eq])) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `address_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule abi_builtin_emit_add >>
  disch_then (qspecl_then [`s`, `limit_st`, `n2w off`, `n2w baddr`] mp_tac) >>
  simp[eval_operand_def] >> strip_tac >>
  qpat_assum `abi_builtin_prefix _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  `abi_tuple_encode_input sf ce ty at av op address_st.cs_next_var lo hi t` by
    (irule abi_tuple_encode_input_transport >> conj_tac >- simp[] >> qexistsl_tac [`st.cs_next_var`, `s`] >>
     simp[abi_decode_frame_def] >> decide_tac) >>
  `eval_operand dst t = SOME (n2w (baddr+off))` by simp[eval_operand_def, word_add_n2w] >>
  `baddr+off+type_memory_bytes ce ty <= t.vs_alloca_next` by simp[] >>
  `(~is_word_type ty ==> ?p. eval_operand op t = SOME (n2w p) /\
    p < dimword (:256) /\ p+type_memory_bytes ce ty <= t.vs_alloca_next)` by
    metis_tac[abi_tuple_encode_input_def] >>
  `run_inst_seq_mem_ok (emitted_insts address_st final) t` by
    (drule_all abi_tuple_encode_write_mem_ok >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts st address_st) s` by
    (drule emit_op_mem_ok >> disch_then irule >> simp[] >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  drule_all abi_tuple_encode_write >> strip_tac >>
  `emitted_insts st final = emitted_insts st address_st ++ emitted_insts address_st final` by
    metis_tac[emitted_insts_append, inst_extends_def] >>
  qpat_x_assum `emitted_insts st final = _` SUBST1_TAC >>
  irule run_inst_seq_mem_ok_append_run >> simp[]
QED

Theorem abi_tuple_encode_bounds_transport[local]:
  !xs ats avs. abi_tuple_encode_inputs sf ce xs ats avs next lo hi s /\
  EVERY (\(op,ty). ~is_word_type ty ==> ?p. eval_operand op s = SOME (n2w p) /\
    p < dimword (:256) /\ p+type_memory_bytes ce ty <= s.vs_alloca_next) xs /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w) ==>
  EVERY (\(op,ty). ~is_word_type ty ==> ?p. eval_operand op t = SOME (n2w p) /\
    p < dimword (:256) /\ p+type_memory_bytes ce ty <= t.vs_alloca_next) xs
Proof
  Induct >- simp[] >> gen_tac >> PairCases_on `h` >>
  simp[abi_tuple_encode_inputs_def] >> rpt gen_tac >> strip_tac >> gvs[] >>
  conj_tac
  >- (strip_tac >> `abi_decoder_operand_live next h0` by fs[abi_tuple_encode_input_def] >>
      metis_tac[LESS_EQ_TRANS]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem abi_tuple_encode_sequence_mem_ok:
  !xs ce buf off st final s baddr ats avs lo hi.
  compile_store_abi_tuple ce buf off xs st = ((),final) /\
  eval_operand buf s = SOME (n2w baddr) /\ abi_decoder_operand_live st.cs_next_var buf /\
  lo <= baddr+off /\ baddr+off+abi_tuple_bytes ce xs <= hi /\ hi < dimword (:256) /\
  abi_tuple_encode_inputs sf ce xs ats avs st.cs_next_var lo hi s /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  hi <= s.vs_alloca_next /\
  EVERY (\(op,ty). ~is_word_type ty ==> ?p. eval_operand op s = SOME (n2w p) /\
    p < dimword (:256) /\ p+type_memory_bytes ce ty <= s.vs_alloca_next) xs ==>
  run_inst_seq_mem_ok (emitted_insts st final) s
Proof
  Induct
  >- (simp[compile_store_abi_tuple_def, comp_return_def] >> rpt strip_tac >> gvs[] >>
      simp[emitted_insts_def, run_inst_seq_mem_ok_def]) >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp_tac bool_ss [abi_tuple_encode_store_cons, comp_ignore_bind_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[abi_tuple_encode_inputs_def] >>
  rename1 `compile_abi_tuple_slot ce buf off h0 h1 st = ((),middle)` >>
  rename1 `abi_tuple_encode_input sf ce h1 at av h0 st.cs_next_var lo hi s` >>
  rename1 `abi_tuple_encode_inputs sf ce xs ats avs st.cs_next_var lo hi s` >>
  drule abi_tuple_encode_slot_shape >> strip_tac >>
  drule abi_tuple_encode_store_shape >> strip_tac >>
  `middle.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= middle.cs_next_var /\
   baddr+off < dimword (:256) /\ lo <= hi /\ baddr+off+type_memory_bytes ce h1 <= hi /\
   lo <= baddr+(off+type_memory_bytes ce h1) /\
   baddr+(off+type_memory_bytes ce h1)+abi_tuple_bytes ce xs <= hi /\
   baddr+off+type_memory_bytes ce h1 <= s.vs_alloca_next` by
    (fs[abi_tuple_bytes_def] >> decide_tac) >>
  `run_inst_seq_mem_ok (emitted_insts st middle) s` by
    (drule_all abi_tuple_encode_slot_mem_ok >> simp[]) >>
  drule_all abi_tuple_encode_result_slot >> strip_tac >>
  drule_all abi_tuple_encode_tail_inputs >> strip_tac >>
  qpat_assum `abi_tuple_encode_result _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_tuple_encode_result_def]) >>
  rename1 `run_inst_seq (emitted_insts st middle) s = OK t` >>
  `eval_operand buf t = SOME (n2w baddr)` by metis_tac[] >>
  `abi_decoder_operand_live middle.cs_next_var buf` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `EVERY (\(op,ty). ~is_word_type ty ==> ?p. eval_operand op t = SOME (n2w p) /\
    p < dimword (:256) /\ p+type_memory_bytes ce ty <= t.vs_alloca_next) xs` by
    (irule abi_tuple_encode_bounds_transport >> metis_tac[LESS_EQ_REFL]) >>
  `run_inst_seq_mem_ok (emitted_insts middle final) t` by
    (qpat_x_assum `abi_tuple_encode_inputs _ _ _ _ _ st.cs_next_var _ _ s` kall_tac >>
     qpat_x_assum `!ce buf off st final s baddr ats avs lo hi. _` drule >>
     disch_then (drule_at (Pat `abi_tuple_encode_inputs _ _ _ _ _ _ _ _ _`)) >>
     simp[GSYM ADD_ASSOC] >> disch_then (qspec_then `baddr` mp_tac) >>
     `baddr < dimword (:256)` by decide_tac >>
     simp[] >> (impl_tac >- decide_tac) >> simp[]) >>
  `emitted_insts st final = emitted_insts st middle ++ emitted_insts middle final` by
    metis_tac[emitted_insts_append, inst_extends_def] >>
  qpat_x_assum `emitted_insts st final = _` SUBST1_TAC >>
  irule run_inst_seq_mem_ok_append_run >> simp[]
QED

Theorem abi_tuple_encode_stage_mem_ok:
  compile_alloc_buffer (abi_tuple_bytes ce xs) st = (source_buf,allocated) /\
  compile_store_abi_tuple ce source_buf.buf_operand 0 xs allocated = ((),staged) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ sb = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (sb,abi_tuple_bytes ce xs)) /\
  sb+abi_tuple_bytes ce xs < dimword (:256) /\ alloca_next_valid initial /\
  abi_tuple_encode_inputs sf ce xs ats avs st.cs_next_var sb (sb+abi_tuple_bytes ce xs) initial /\
  staged.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  EVERY (\(op,ty). ~is_word_type ty ==> ?p. eval_operand op initial = SOME (n2w p) /\
    p < dimword (:256) /\ p+type_memory_bytes ce ty <= initial.vs_alloca_next) xs ==>
  run_inst_seq_mem_ok (emitted_insts st staged) initial
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_tuple_encode_stage_shape >> strip_tac >>
  drule abi_tuple_encode_alloc_shape >> strip_tac >>
  `abi_tuple_bytes ce xs < dimword (:256) /\ allocated.cs_next_var <= limit_st.cs_next_var /\
   st.cs_next_var <= allocated.cs_next_var` by decide_tac >>
  drule_all abi_builtin_alloc_buffer_frame >> strip_tac >>
  rename1 `abi_builtin_allocation_frame st.cs_next_var st.cs_next_id _ initial addressed` >>
  qpat_assum `abi_builtin_allocation_frame _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_allocation_frame_def]) >>
  `FLOOKUP (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce xs) initial).vs_allocas
    st.cs_next_id = SOME (sb,abi_tuple_bytes ce xs)` by
    (gvs[abi_builtin_allocate_state_def, FLOOKUP_UPDATE]) >>
  `run_inst_seq_mem_ok (emitted_insts st allocated) initial` by
    (drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule emit_op_mem_ok >> disch_then irule >> simp[] >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  drule_all alloca_site_frontier >> strip_tac >>
  `sb+abi_tuple_bytes ce xs <= addressed.vs_alloca_next /\
   initial.vs_alloca_next <= addressed.vs_alloca_next` by
    (gvs[abi_builtin_allocate_state_def] >> decide_tac) >>
  `abi_tuple_encode_inputs sf ce xs ats avs allocated.cs_next_var sb (sb+abi_tuple_bytes ce xs) addressed` by
    (irule abi_tuple_encode_inputs_transport >>
     simp[abi_decode_frame_def] >> metis_tac[]) >>
  `EVERY (\(op,ty). ~is_word_type ty ==> ?p. eval_operand op addressed = SOME (n2w p) /\
    p < dimword (:256) /\ p+type_memory_bytes ce ty <= addressed.vs_alloca_next) xs` by
    (irule abi_tuple_encode_bounds_transport >> metis_tac[]) >>
  `run_inst_seq_mem_ok (emitted_insts allocated staged) addressed` by
    (drule abi_tuple_encode_sequence_mem_ok >>
     disch_then (drule_at (Pat `abi_tuple_encode_inputs _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> disch_then (qspecl_then [`limit_st`, `sb`] mp_tac) >>
     `sb < dimword (:256)` by decide_tac >> simp[]) >>
  drule abi_tuple_encode_store_shape >> strip_tac >>
  `emitted_insts st staged = emitted_insts st allocated ++ emitted_insts allocated staged` by
    metis_tac[emitted_insts_append, inst_extends_def] >>
  qpat_x_assum `emitted_insts st staged = _` SUBST1_TAC >>
  irule run_inst_seq_mem_ok_append_run >> simp[]
QED
