Theory abiEncoderArrayTailInit
Ancestors
  abiEncoderArrayCode abiDecoderIndexInit compileEnv context emitHelperProps exprLoweringProps
  emitHelper venomInst words list rich_list arithmetic abiEncoderComplexPrefix
  abiDecoderReentryAddress abiDecoderReentryAddress abiDecoderArrayInitExec
  abiDecoderAllocation abiDecoderReentry abiDecoderArrayHeader abiDecoderGuards
  abiDecoderContract abiDecoderFrame venomExecSemantics venomMemProps venomState finite_map
  abiEncoderSequence abiEncoderArrayRound abiEncoderArrayMemory abiEncoderArrayExit
  abiEncoderMembersDefs abiEncoderChildInputs abiDecoderEffect abiDecoderPrimitiveLoopFrames
  abiDecoderLoop fragExec valueEncoding contractABI pred_set

(* ===== Code ===== *)

(* The actual dynamic-array initializer allocates and stores the computed head length. *)

Libs monadsyntax

Definition abi_encode_array_tail_init_def:
  abi_encode_array_tail_init count_op asz =
    do buf <- compile_alloc_buffer 32;
       offset <- emit_op MUL [count_op;Lit (n2w asz)];
       emit_void MSTORE [buf.buf_operand;offset];
       return buf.buf_operand
    od
End

Theorem abi_encode_array_dynamic_init_split:
  abi_encode_array_dynamic_init count_op asz =
    do ip <- abi_decode_index_init;
       dyn_ptr <- abi_encode_array_tail_init count_op asz;
       return (ip,dyn_ptr)
    od
Proof
  simp_tac bool_ss [FUN_EQ_THM, abi_encode_array_dynamic_init_def, abi_encode_array_tail_init_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_encode_array_tail_init_trace:
  abi_encode_array_tail_init count_op asz st = (dyn_ptr,st') ==>
  ?buf c1 offset c2.
    compile_alloc_buffer 32 st = (buf,c1) /\ dyn_ptr = buf.buf_operand /\
    emit_op MUL [count_op;Lit (n2w asz)] c1 = (offset,c2) /\
    emit_void MSTORE [buf.buf_operand;offset] c2 = ((),st')
Proof
  simp_tac bool_ss [abi_encode_array_tail_init_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, LET_THM] >> pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `compile_alloc_buffer 32 st = (buf,c1)` >>
  rename1 `emit_op MUL [count_op;Lit (n2w asz)] c1 = (offset,c2)` >>
  qexistsl_tac [`buf`, `c1`, `offset`, `c2`] >> asm_simp_tac bool_ss []
QED

Theorem abi_encode_array_tail_init_shape:
  abi_encode_array_tail_init count_op asz st = (dyn_ptr,st') ==>
  dyn_ptr = Var (STRING #"%" (toString st.cs_next_var)) /\
  st'.cs_next_var = st.cs_next_var+2 /\ st'.cs_next_id = st.cs_next_id+3 /\
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\ inst_extends st st' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st st')
Proof
  simp[abi_encode_array_tail_init_def, compile_alloc_buffer_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, is_terminator_def, mk_inst_def]
QED

(* ===== Sequence ===== *)

(* The computed head length uses the existing cursor observation contract at that value. *)

Theorem abi_encode_array_tail_init_sequence:
  abi_encode_array_tail_init count_op asz st = (dyn_ptr,st') /\
  eval_operand count_op initial = SOME (n2w cnt) /\ abi_decoder_operand_live st.cs_next_var count_op /\
  abi_decoder_budget first last b cap initial /\ st.cs_next_id IN abi_decoder_ids first last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    abi_encoder_complex_prefix_post [(AbiPrimWord,cnt*asz,0,F)] dyn_ptr st.cs_next_var st.cs_next_id
      limit_st first last b cap initial actual
Proof
  strip_tac >> drule abi_encode_array_tail_init_trace >> strip_tac >>
  drule abi_encode_array_tail_init_shape >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  `c1.cs_next_var <= limit_st.cs_next_var /\ c2.cs_next_var <= limit_st.cs_next_var /\
   st.cs_next_var <= c1.cs_next_var` by decide_tac >>
  drule_all abi_decoder_alloc_buffer_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) initial = OK allocated` >>
  `eval_operand count_op allocated = SOME (n2w cnt)` by asm_simp_tac bool_ss [] >>
  mp_tac (Q.INST [`opc` |-> `MUL`, `lhs` |-> `count_op`, `rhs` |-> `Lit (n2w asz)`,
    `out` |-> `offset`, `a` |-> `n2w cnt:bytes32`, `b` |-> `n2w asz:bytes32`,
    `st` |-> `c1`, `st'` |-> `c2`, `s` |-> `allocated:venom_state`] abi_decoder_binary_reentry) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) allocated = OK prepared` >>
  `abi_decoder_operand_live c1.cs_next_var dyn_ptr` by
    (asm_simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     rpt strip_tac >> decide_tac) >>
  `eval_operand buf.buf_operand prepared = SOME (n2w p)` by
    (qpat_assum `!op. abi_decoder_operand_live c1.cs_next_var op ==> _`
      (qspec_then `dyn_ptr` mp_tac) >> gvs[]) >>
  `eval_operand offset prepared = SOME (n2w (cnt*asz))` by
    fs[word_mul_n2w, MULT_COMM, eval_operand_def, lookup_var_update_var] >>
  drule abi_decoder_budget_word_bound >> strip_tac >> `p < dimword (:256)` by decide_tac >>
  `run_inst_seq (emitted_insts c2 st') prepared = OK (mstore p (n2w (cnt*asz)) prepared)` by
    (drule_all abi_decode_store_sequence >> asm_simp_tac (srw_ss()) [w2n_n2w]) >>
  `inst_extends st c1 /\ inst_extends c2 st'` by
    (conj_tac >- (drule abi_decode_alloc_buffer_inst_extends >> simp[]) >>
     drule inst_extends_emit_void >> simp[]) >>
  `run_inst_seq (emitted_insts st c2) initial = OK prepared /\ inst_extends st c2` by
    (drule_all abi_decode_sequence_chain >> asm_simp_tac bool_ss []) >>
  `run_inst_seq (emitted_insts st st') initial = OK (mstore p (n2w (cnt*asz)) prepared)` by
    (drule_all abi_decode_sequence_chain >> asm_simp_tac bool_ss []) >>
  `abi_decoder_budget first last b cap prepared` by
    (drule_all abi_decoder_budget_transport >> asm_simp_tac bool_ss []) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op prepared = eval_operand op initial` by
    (rpt strip_tac >> `abi_decoder_operand_live c1.cs_next_var op` by
       (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss []) >>
     asm_simp_tac bool_ss []) >>
  `abi_decode_frame p 32 prepared (mstore p (n2w (cnt*asz)) prepared)` by irule abi_decode_mstore_frame >>
  qexists_tac `mstore p (n2w (cnt*asz)) prepared` >> asm_simp_tac bool_ss [] >>
  pure_rewrite_tac [abi_encoder_complex_prefix_post_def] >> qexists_tac `p` >>
  gvs[fresh_vars_wrt_mstore, eval_operand_mstore, abi_decode_frame_def, mload_mstore_same,
    mstore_def, write_memory_with_expansion_def] >> first_assum ACCEPT_TAC
QED

(* ===== Prepare ===== *)

(* Actual computed tail-cursor initialization preserves the source and empty output prefix. *)

Theorem abi_encode_array_tail_init_reach:
  abi_encode_array_tail_init count_op asz st = (dyn_ptr,st') /\ fn_has_code st st' func /\
  eval_operand count_op initial = SOME (n2w cnt) /\ abi_decoder_operand_live st.cs_next_var count_op /\
  abi_decoder_budget first last b cap initial /\ st.cs_next_id IN abi_decoder_ids first last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_encoder_complex_prefix_post [(AbiPrimWord,cnt*asz,0,F)] dyn_ptr st.cs_next_var st.cs_next_id
      limit_st first last b cap initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encode_array_tail_init_shape >> strip_tac >>
  drule_all abi_encode_array_tail_init_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') initial = OK encoded` >>
  `~encoded.vs_halted` by fs[abi_encoder_complex_prefix_post_def] >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH st'.cs_current_insts` >> gvs[]
QED

Theorem abi_encoder_array_tail_init_prepare:
  abi_encode_array_tail_init count_op asz st = (dyn_ptr,owner_st) /\ fn_has_code st owner_st func /\
  abi_encoder_array_memory ei asz msz T ty avs st src dst sb source_cap d output_size b cap 0 initial /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\ abi_decoder_operand_live st.cs_next_var count_op /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ lo <= st.cs_next_id /\
  owner_st.cs_next_id <= hi /\ hi <= last /\ owner_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ready slot.
    abi_encoder_array_memory ei asz msz T ty avs owner_st src dst sb source_cap d output_size b cap 0 ready /\
    abi_encoder_cursor T dyn_ptr st.cs_next_id slot first lo owner_st
      (LENGTH avs*abi_member_head_size ty) ready /\
    abi_decoder_effect first last st.cs_next_id hi st.cs_next_var limit_st d output_size b cap initial ready /\
    ready.vs_current_bb = owner_st.cs_current_bb /\ ready.vs_inst_idx = LENGTH owner_st.cs_current_insts /\
    ~ready.vs_halted /\ abi_decode_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encode_array_tail_init_shape >> strip_tac >> drule abi_encoder_array_exit_inputs >> strip_tac >>
  `st.cs_next_id IN abi_decoder_ids first last` by
    (simp_tac std_ss [abi_decoder_ids_def, GSPECIFICATION] >> decide_tac) >>
  mp_tac (Q.INST [`cnt` |-> `LENGTH (avs:abi_value list)`, `st'` |-> `owner_st`]
    abi_encode_array_tail_init_reach) >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  qpat_assum `abi_encoder_array_memory _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_memory_def]) >>
  qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (assume_tac o List.last o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  `abi_decoder_effect first last st.cs_next_id hi st.cs_next_var limit_st d output_size b cap initial ready` by
    (mp_tac (Q.INST [`infos` |-> `[(AbiPrimWord,LENGTH (avs:abi_value list)*asz,0,F)]`,
      `site` |-> `st.cs_next_id`, `next` |-> `st.cs_next_var`, `outsz` |-> `output_size:num`,
      `actual` |-> `ready:venom_state`] abi_encoder_complex_prefix_effect) >>
     impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> asm_simp_tac bool_ss []) >>
  qpat_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ _ ready`
    (qx_choose_then `slot` (MAP_EVERY assume_tac o CONJUNCTS) o
      PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >>
  `abi_decoder_operand_live owner_st.cs_next_var dyn_ptr` by
    (asm_simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     rpt strip_tac >> decide_tac) >>
  `abi_encoder_cursor T dyn_ptr st.cs_next_id slot first lo owner_st
    (LENGTH avs*abi_member_head_size ty) ready` by
    (asm_simp_tac (srw_ss()) [abi_encoder_cursor_def] >> decide_tac) >>
  `abi_decode_footprint_frame [(slot,32)] initial ready` by
    (irule abi_decoder_frame_in_footprint >> qexistsl_tac [`slot`, `32`] >> simp[]) >>
  `abi_footprint_disjoint d output_size [(slot,32)]` by
    (simp_tac (srw_ss()) [abi_footprint_disjoint_def] >> decide_tac) >>
  `abi_encoder_array_memory ei asz msz T ty avs st src dst sb source_cap d output_size b cap 0 ready` by
    (mp_tac (Q.INST [`dyn` |-> `T`, `j` |-> `0:num`, `fp` |-> `[(slot,32)]`,
      `lo` |-> `st.cs_next_id`, `actual` |-> `ready:venom_state`] abi_encoder_array_memory_scratch) >>
     impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss []) >>
  `st.cs_next_var <= owner_st.cs_next_var` by decide_tac >>
  drule_all abi_encoder_array_memory_mono >> strip_tac >>
  qexistsl_tac [`ready`, `slot`] >> asm_simp_tac bool_ss []
QED
