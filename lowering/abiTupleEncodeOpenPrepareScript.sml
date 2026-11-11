Theory abiTupleEncodeOpenPrepare
Ancestors
  abiTupleEncodePrepare abiTupleEncodeOpenSlot abiTupleEncodeOpenResult
  abiTupleEncodeOpenInput abiTupleEncodeOpenMemory abiTupleProps
  exprLowering context compileEnv emitHelperProps exprLoweringProps venomInst words list rich_list arithmetic
  abiDecoderReentry abiDecoderContract abiDecoderFrameCompose venomState venomExecSemantics
  abiBuiltinAllocation emitHelper abiDecoderGuards abiDecoderRange finite_map abiEncoderSequence abiDecoderLoop
  fragExec instIdxIndep abiBuiltinEncodeResources abiBuiltinEncodeInput
  loweringStateRelDefs

Theorem abi_tuple_encode_open_result_slot:
  compile_abi_tuple_slot ce buf off op ty st = ((),final) /\
  eval_operand buf s = SOME (n2w baddr) /\ baddr+off < dimword (:256) /\ lo <= hi /\
  abi_tuple_encode_open_input sf ce ty at av op st.cs_next_var lo hi s /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. abi_tuple_encode_open_result sf ce [(op,ty)] [at] [av] st final limit_st (baddr+off) s actual
Proof
  strip_tac >> drule_all abi_tuple_encode_open_slot_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st final) s = OK actual` >> qexists_tac `actual` >>
  asm_simp_tac (srw_ss()) [abi_tuple_encode_open_result_def, abi_tuple_encode_open_memory_def, abi_tuple_bytes_def]
QED

Theorem abi_tuple_encode_open_tail_inputs:
  abi_tuple_encode_open_result sf ce [(op,ty)] [at] [av] st middle limit_st d s t /\
  abi_tuple_encode_open_inputs sf ce xs ats avs st.cs_next_var lo hi s /\
  st.cs_next_var <= middle.cs_next_var /\ lo <= d /\ d+type_memory_bytes ce ty <= hi ==>
  abi_tuple_encode_open_inputs sf ce xs ats avs middle.cs_next_var lo hi t
Proof
  strip_tac >> qpat_assum `abi_tuple_encode_open_result _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE (srw_ss()) [abi_tuple_encode_open_result_def, abi_tuple_bytes_def]) >>
  `lo <= hi` by decide_tac >>
  `abi_decode_frame lo (hi-lo) s t` by
    (irule abi_decode_frame_widen >> qexistsl_tac [`d`, `type_memory_bytes ce ty`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  drule_all abi_tuple_encode_open_inputs_transport >> simp[]
QED

Theorem abi_tuple_encode_open_sequence:
  !xs ce buf off st final s baddr ats avs lo hi.
  compile_store_abi_tuple ce buf off xs st = ((),final) /\
  eval_operand buf s = SOME (n2w baddr) /\ abi_decoder_operand_live st.cs_next_var buf /\
  lo <= baddr+off /\ baddr+off+abi_tuple_bytes ce xs <= hi /\ hi < dimword (:256) /\
  abi_tuple_encode_open_inputs sf ce xs ats avs st.cs_next_var lo hi s /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. abi_tuple_encode_open_result sf ce xs ats avs st final limit_st (baddr+off) s actual
Proof
  Induct
  >- (simp[compile_store_abi_tuple_def, comp_return_def, abi_tuple_encode_open_inputs_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `s` >>
      simp[abi_tuple_encode_open_result_def, emitted_insts_def, run_inst_seq_def, inst_extends_refl,
        abi_tuple_encode_open_memory_def, abi_tuple_bytes_def, abi_decode_frame_def]) >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp_tac bool_ss [abi_tuple_encode_store_cons, comp_ignore_bind_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[abi_tuple_encode_open_inputs_def] >>
  rename1 `compile_abi_tuple_slot ce buf off h0 h1 st = ((),middle)` >>
  rename1 `abi_tuple_encode_open_input sf ce h1 head_at head_av h0 st.cs_next_var lo hi s` >>
  rename1 `abi_tuple_encode_open_inputs sf ce xs tail_ats tail_avs st.cs_next_var lo hi s` >>
  drule abiTupleEncodeSlotTheory.abi_tuple_encode_slot_shape >> strip_tac >>
  drule abi_tuple_encode_store_shape >> strip_tac >>
  `middle.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= middle.cs_next_var /\
   baddr+off < dimword (:256) /\ lo <= hi /\ baddr+off+type_memory_bytes ce h1 <= hi /\
   lo <= baddr+(off+type_memory_bytes ce h1) /\
   baddr+(off+type_memory_bytes ce h1)+abi_tuple_bytes ce xs <= hi` by
    (fs[abi_tuple_bytes_def] >> decide_tac) >>
  drule_all abi_tuple_encode_open_result_slot >> strip_tac >>
  rename1 `abi_tuple_encode_open_result sf ce [(h0,h1)] [head_at] [head_av] st middle limit_st (baddr+off) s written` >>
  drule_all abi_tuple_encode_open_tail_inputs >> strip_tac >>
  qpat_assum `abi_tuple_encode_open_result _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_tuple_encode_open_result_def]) >>
  `eval_operand buf written = SOME (n2w baddr)` by (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live middle.cs_next_var buf` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss []) >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [ADD_ASSOC]) >>
  qpat_x_assum `!ce buf off st final s baddr ats avs lo hi. _`
    (qspecl_then [`ce`, `buf`, `off+type_memory_bytes ce h1`, `middle`, `final`, `written`,
      `baddr`, `tail_ats`, `tail_avs`, `lo`, `hi`] (mp_tac o PURE_REWRITE_RULE [ADD_ASSOC])) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  rename1 `abi_tuple_encode_open_result sf ce xs tail_ats tail_avs middle final limit_st _ written actual` >>
  qexists_tac `actual` >>
  irule abi_tuple_encode_open_result_cons >>
  goal_assum (drule_at Any) >> asm_simp_tac bool_ss [ADD_ASSOC]
QED

Theorem abi_tuple_encode_open_stage_sequence:
  compile_alloc_buffer (abi_tuple_bytes ce xs) st = (source_buf,allocated) /\
  compile_store_abi_tuple ce source_buf.buf_operand 0 xs allocated = ((),staged) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ sb = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (sb,abi_tuple_bytes ce xs)) /\
  sb+abi_tuple_bytes ce xs < dimword (:256) /\
  abi_tuple_encode_open_inputs sf ce xs ats avs st.cs_next_var sb (sb+abi_tuple_bytes ce xs) initial /\
  staged.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st staged) initial = OK actual /\ inst_extends st staged /\
    eval_operand source_buf.buf_operand actual = SOME (n2w sb) /\
    abi_tuple_encode_open_memory sf ce xs ats avs sb actual.vs_memory /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame sb (abi_tuple_bytes ce xs) initial actual /\
    actual.vs_allocas = (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce xs) initial).vs_allocas /\
    actual.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce xs) initial).vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_tuple_encode_stage_shape >> strip_tac >> drule abi_tuple_encode_alloc_shape >> strip_tac >>
  `abi_tuple_bytes ce xs < dimword (:256) /\ allocated.cs_next_var <= limit_st.cs_next_var /\
   st.cs_next_var <= allocated.cs_next_var` by decide_tac >>
  drule_all abi_builtin_alloc_buffer_frame >> strip_tac >>
  rename1 `abi_builtin_allocation_frame st.cs_next_var st.cs_next_id _ initial addressed` >>
  qpat_assum `abi_builtin_allocation_frame _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_allocation_frame_def]) >>
  `abi_tuple_encode_open_inputs sf ce xs ats avs allocated.cs_next_var sb (sb+abi_tuple_bytes ce xs) addressed` by
    (irule abi_tuple_encode_open_inputs_transport >> conj_tac >- decide_tac >>
     qexistsl_tac [`st.cs_next_var`, `initial`] >>
     asm_simp_tac bool_ss [abi_decode_frame_def] >> decide_tac) >>
  `?encoded. abi_tuple_encode_open_result sf ce xs ats avs allocated staged limit_st sb addressed encoded` by
    (irule (GEN_ALL (SIMP_RULE (srw_ss()) [] (Q.INST [`off` |-> `0:num`] (SPEC_ALL abi_tuple_encode_open_sequence)))) >>
     goal_assum (drule_at Any) >> asm_simp_tac bool_ss [] >>
     qpat_assum `allocated.cs_next_var = _` (fn th => pure_rewrite_tac [GSYM th]) >>
     conj_tac >- (qexists_tac `source_buf.buf_operand` >> asm_simp_tac bool_ss []) >>
     qexistsl_tac [`sb+abi_tuple_bytes ce xs`, `sb`] >> asm_simp_tac (srw_ss()) []) >>
  qpat_assum `abi_tuple_encode_open_result _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_tuple_encode_open_result_def]) >>
  `eval_operand source_buf.buf_operand encoded = SOME (n2w sb)` by
    (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `abi_decode_frame sb (abi_tuple_bytes ce xs) initial encoded` by
    (irule abi_decode_frame_trans >> qexists_tac `addressed` >> asm_simp_tac bool_ss [abi_decode_frame_def]) >>
  `run_inst_seq (emitted_insts st staged) initial = OK encoded /\ inst_extends st staged` by
    (irule abi_decode_sequence_chain >> goal_assum (drule_at Any) >> asm_simp_tac (srw_ss()) []) >>
  qexists_tac `encoded` >> asm_simp_tac bool_ss [] >> qx_genl_tac [`older`, `older_word`] >> strip_tac >>
  `eval_operand older addressed = SOME older_word` by (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  qpat_x_assum `!op w. abi_decoder_operand_live allocated.cs_next_var op /\ _ ==> _` irule >>
  asm_simp_tac bool_ss [] >> irule abi_decoder_operand_live_mono >>
  qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem abi_tuple_encode_open_stage_reach:
  compile_alloc_buffer (abi_tuple_bytes ce xs) st = (source_buf,allocated) /\
  compile_store_abi_tuple ce source_buf.buf_operand 0 xs allocated = ((),staged) /\
  fn_has_code st staged func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ sb = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (sb,abi_tuple_bytes ce xs)) /\
  sb+abi_tuple_bytes ce xs < dimword (:256) /\
  abi_tuple_encode_open_inputs sf ce xs ats avs st.cs_next_var sb (sb+abi_tuple_bytes ce xs) initial /\
  staged.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand source_buf.buf_operand actual = SOME (n2w sb) /\
    abi_tuple_encode_open_memory sf ce xs ats avs sb actual.vs_memory /\ fresh_vars_wrt limit_st actual /\
    abi_decode_frame sb (abi_tuple_bytes ce xs) initial actual /\
    actual.vs_allocas = (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce xs) initial).vs_allocas /\
    actual.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce xs) initial).vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = staged.cs_current_bb /\ actual.vs_inst_idx = LENGTH staged.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_tuple_encode_stage_shape >> strip_tac >>
  drule_all abi_tuple_encode_open_stage_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st staged) initial = OK encoded` >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH staged.cs_current_insts` >>
  gvs[abi_decode_frame_def, fresh_vars_wrt_def, eval_op_inst_idx] >> first_assum ACCEPT_TAC
QED
