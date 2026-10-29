Theory abiTupleEncodeStage
Ancestors
  abiTupleEncodeCode abiTupleProps abiBuiltinAllocation abiDecoderReentry compileEnv context
  emitHelper emitHelperProps exprLoweringProps venomInst words list rich_list arithmetic
  abiTupleEncodeSequence abiTupleEncodeResult abiTupleEncodeMemory abiTupleEncodeInput
  abiDecoderContract abiDecoderFrameCompose abiDecoderGuards venomState venomExecSemantics
  finite_map abiEncoderSequence abiDecoderLoop fragExec instIdxIndep

(* ===== Code ===== *)

(* Allocation plus all tuple writes stays in its actual containing block. *)

Theorem abi_tuple_encode_alloc_shape:
  compile_alloc_buffer n st = (buf,allocated) ==>
  allocated.cs_next_var = st.cs_next_var+1 /\ allocated.cs_next_id = st.cs_next_id+1 /\
  allocated.cs_blocks = st.cs_blocks /\ allocated.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts allocated.cs_current_insts /\ inst_extends st allocated /\
  abi_decoder_operand_live allocated.cs_next_var buf.buf_operand /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st allocated)
Proof
  simp[compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    fresh_var_def, fresh_id_def, emit_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def, abi_decoder_operand_live_def,
    abi_decoder_older_vars_def, DROP_LENGTH_APPEND, IS_PREFIX_APPEND, is_terminator_def, mk_inst_def]
QED

Theorem abi_tuple_encode_stage_shape:
  compile_alloc_buffer n st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0 xs allocated = ((),staged) ==>
  staged.cs_next_var = st.cs_next_var+1+LENGTH xs /\ st.cs_next_id < staged.cs_next_id /\
  staged.cs_blocks = st.cs_blocks /\ staged.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts staged.cs_current_insts /\ inst_extends st staged /\
  allocated.cs_next_var <= staged.cs_next_var /\ abi_decoder_operand_live staged.cs_next_var buf.buf_operand /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st staged)
Proof
  strip_tac >> drule abi_tuple_encode_alloc_shape >> strip_tac >>
  drule abi_tuple_encode_store_shape >> strip_tac >>
  `inst_extends st staged` by
    (irule inst_extends_trans >> qexists_tac `allocated` >> asm_simp_tac bool_ss []) >>
  `isPREFIX st.cs_current_insts staged.cs_current_insts` by
    (irule isPREFIX_TRANS >> qexists_tac `allocated.cs_current_insts` >> asm_simp_tac bool_ss []) >>
  `emitted_insts st staged = emitted_insts st allocated ++ emitted_insts allocated staged` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `allocated.cs_next_var <= staged.cs_next_var` by decide_tac >>
  `abi_decoder_operand_live staged.cs_next_var buf.buf_operand` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `allocated.cs_next_var` >> asm_simp_tac bool_ss []) >>
  asm_simp_tac (srw_ss()) [EVERY_APPEND] >> decide_tac
QED

(* ===== Sequence ===== *)

(* Execute allocation and complete tuple construction, including site reuse. *)

Theorem abi_tuple_encode_stage_sequence:
  compile_alloc_buffer (abi_tuple_bytes ce xs) st = (source_buf,allocated) /\
  compile_store_abi_tuple ce source_buf.buf_operand 0 xs allocated = ((),staged) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ sb = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (sb,abi_tuple_bytes ce xs)) /\
  sb+abi_tuple_bytes ce xs < dimword (:256) /\
  abi_tuple_encode_inputs sf ce xs ats avs st.cs_next_var sb (sb+abi_tuple_bytes ce xs) initial /\
  staged.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st staged) initial = OK actual /\ inst_extends st staged /\
    eval_operand source_buf.buf_operand actual = SOME (n2w sb) /\
    abi_tuple_encode_memory sf ce xs ats avs sb actual.vs_memory /\
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
  `abi_tuple_encode_inputs sf ce xs ats avs allocated.cs_next_var sb (sb+abi_tuple_bytes ce xs) addressed` by
    (mp_tac (Q.INST [`next` |-> `st.cs_next_var`, `later` |-> `allocated.cs_next_var`,
      `lo` |-> `sb:num`, `hi` |-> `sb+abi_tuple_bytes ce xs`, `s` |-> `initial:venom_state`,
      `t` |-> `addressed:venom_state`] (SPEC_ALL abi_tuple_encode_inputs_transport)) >>
     impl_tac >- (asm_simp_tac bool_ss [abi_decode_frame_def] >> decide_tac) >> simp[]) >>
  mp_tac (SIMP_RULE (srw_ss()) [] (Q.INST [`buf` |-> `source_buf.buf_operand`, `off` |-> `0:num`,
    `st` |-> `allocated`, `final` |-> `staged`, `s` |-> `addressed:venom_state`,
    `baddr` |-> `sb:num`, `lo` |-> `sb:num`, `hi` |-> `sb+abi_tuple_bytes ce xs`]
    (SPEC_ALL abi_tuple_encode_sequence))) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, asm_simp_tac bool_ss [] >> decide_tac]) >>
  strip_tac >> rename1 `abi_tuple_encode_result sf ce xs ats avs allocated staged limit_st sb addressed encoded` >>
  qpat_assum `abi_tuple_encode_result _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_tuple_encode_result_def]) >>
  `eval_operand source_buf.buf_operand encoded = SOME (n2w sb)` by
    (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `abi_decode_frame sb (abi_tuple_bytes ce xs) initial encoded` by
    (irule abi_decode_frame_trans >> qexists_tac `addressed` >> asm_simp_tac bool_ss [abi_decode_frame_def]) >>
  `run_inst_seq (emitted_insts st staged) initial = OK encoded /\ inst_extends st staged` by
    (mp_tac (Q.INST [`st1` |-> `allocated`, `st2` |-> `staged`, `s` |-> `initial:venom_state`,
      `s1` |-> `addressed:venom_state`, `s2` |-> `encoded:venom_state`] abi_decode_sequence_chain) >>
     asm_simp_tac bool_ss []) >>
  qexists_tac `encoded` >> asm_simp_tac bool_ss [] >> qx_genl_tac [`older`, `older_word`] >> strip_tac >>
  `eval_operand older addressed = SOME older_word` by (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  qpat_x_assum `!op w. abi_decoder_operand_live allocated.cs_next_var op /\ _ ==> _` irule >>
  asm_simp_tac bool_ss [] >> irule abi_decoder_operand_live_mono >>
  qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss [] >> decide_tac
QED

(* ===== Reach ===== *)

(* Reach the real encoder entry after allocation and all tuple writes. *)

Theorem abi_tuple_encode_stage_reach:
  compile_alloc_buffer (abi_tuple_bytes ce xs) st = (source_buf,allocated) /\
  compile_store_abi_tuple ce source_buf.buf_operand 0 xs allocated = ((),staged) /\
  fn_has_code st staged func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ sb = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (sb,abi_tuple_bytes ce xs)) /\
  sb+abi_tuple_bytes ce xs < dimword (:256) /\
  abi_tuple_encode_inputs sf ce xs ats avs st.cs_next_var sb (sb+abi_tuple_bytes ce xs) initial /\
  staged.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand source_buf.buf_operand actual = SOME (n2w sb) /\
    abi_tuple_encode_memory sf ce xs ats avs sb actual.vs_memory /\ fresh_vars_wrt limit_st actual /\
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
  drule_all abi_tuple_encode_stage_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st staged) initial = OK encoded` >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH staged.cs_current_insts` >>
  gvs[abi_decode_frame_def, fresh_vars_wrt_def, eval_op_inst_idx] >> first_assum ACCEPT_TAC
QED
