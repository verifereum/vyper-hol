Theory abiEncoderArrayCount
Ancestors
  abiEncoderWrites abiEncoderReentryLeaves abiEncoderMemory abiEncoderBytesPrefix
  abiBuiltinPrefix abiDecoderArrayHeader abiDecoderDynamicLoopSetup abiDecoderReentry
  abiDecoderContract abiDecoderGuards emitHelperProps exprLoweringProps compileEnv emitHelper
  valueEncoding valueEncodingProps venomState venomExecSemantics words list arithmetic
  abiEncoderSequence abiDecoderArrayLoopInit abiDecoderLoop fragExec instIdxIndep
  abiEncoderArrayMemory abiEncoderArrayPrefix abiEncoderArrayLayout abiEncoderInput
  abiEncoderChildInputs abiEncoderBufferFrame abiDecoderCorrectWord abiDecoderEffect
  abiDecoderFrameCompose contractABI

(* ===== Copy ===== *)

(* The parent array prefix copies its count under the enclosing freshness bound. *)

Theorem abi_encoder_array_count_copy_sequence:
  abi_decode_array_header dst src MLOAD st = (cnt,st') /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w db) /\
  abi_decoder_operand_live st.cs_next_var dst /\
  sb < dimword (:256) /\ db < dimword (:256) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. run_inst_seq (emitted_insts st st') s = OK actual /\ inst_extends st st' /\
    eval_operand cnt actual = SOME (mload sb s) /\ mem_word_at db actual.vs_memory = mload sb s /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame db 32 s actual /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    actual.vs_halted = s.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  simp_tac bool_ss [abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, LET_THM] >> pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op MLOAD [src] st = (cnt,loaded_st)` >>
  rename1 `emit_void MSTORE [dst;cnt] loaded_st = ((),ready)` >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  `loaded_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_builtin_emit_load >> strip_tac >>
  rename1 `abi_builtin_prefix st loaded_st limit_st s loaded` >>
  `eval_operand cnt loaded = SOME (mload sb s)` by fs[w2n_n2w] >>
  `eval_operand dst loaded = SOME (n2w db)` by
    (mp_tac (Q.INST [`st'` |-> `loaded_st`, `t` |-> `loaded:venom_state`,
      `op` |-> `dst`, `w` |-> `n2w db:bytes32`] abi_encoder_prefix_eval) >> asm_simp_tac bool_ss []) >>
  qpat_assum `abi_builtin_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  mp_tac (Q.INST [`ptr_op` |-> `dst`, `value_op` |-> `cnt`, `p` |-> `db`,
    `w` |-> `mload sb s`, `st` |-> `loaded_st`, `st'` |-> `ready`, `s` |-> `loaded:venom_state`]
    abi_encoder_emit_store) >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qabbrev_tac `actual = mstore db (mload sb s) loaded` >>
  `run_inst_seq (emitted_insts st ready) s = OK actual /\ inst_extends st ready` by
    (mp_tac (Q.INST [`st1` |-> `loaded_st`, `st2` |-> `ready`, `s1` |-> `loaded:venom_state`,
      `s2` |-> `actual:venom_state`] abi_decode_sequence_chain) >> asm_simp_tac bool_ss [Abbr`actual`]) >>
  `actual.vs_memory = (mstore db (mload sb s) s).vs_memory` by
    (simp_tac bool_ss [Abbr`actual`] >> irule abi_encoder_store_memory >> asm_simp_tac bool_ss []) >>
  `abi_decode_frame db 32 s actual` by
    (mp_tac (Q.INST [`t` |-> `mstore db (mload sb s) s`, `u` |-> `actual:venom_state`, `sz` |-> `32`]
      abi_encoder_frame_memory) >> asm_simp_tac (srw_ss()) [abi_decode_mstore_frame, Abbr`actual`]) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss())
    [Abbr`actual`, mstore_mem_word_at_same, eval_operand_mstore] >>
  rpt strip_tac >> first_x_assum irule >> asm_simp_tac bool_ss []
QED

(* ===== Reach ===== *)

(* The real array count copy reaches its CFG endpoint under enclosing freshness. *)

Theorem abi_encoder_array_count_live:
  abi_decode_array_header dst src opc st = (cnt,st') ==>
  abi_decoder_operand_live st'.cs_next_var cnt
Proof
  simp_tac bool_ss [abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, LET_THM] >> pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  imp_res_tac abi_decoder_operand_live_emit >> imp_res_tac emitted_insts_emit_void >> gvs[]
QED

Theorem abi_encoder_array_count_reach:
  abi_decode_array_header dst src MLOAD st = (cnt,st') /\ fn_has_code st st' func /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w db) /\
  abi_decoder_operand_live st.cs_next_var dst /\ sb < dimword (:256) /\ db < dimword (:256) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand cnt actual = SOME (mload sb initial) /\
    mem_word_at db actual.vs_memory = mload sb initial /\ fresh_vars_wrt limit_st actual /\
    abi_decode_frame db 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`opc` |-> `MLOAD`] abi_decode_array_header_shape) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_decode_source_opcode_def] >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st st')`
    by fs[EVERY_CONJ] >>
  drule_all abi_encoder_array_count_copy_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') initial = OK encoded` >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  gvs[abi_decode_frame_def, fresh_vars_wrt_def, eval_op_inst_idx] >> first_assum ACCEPT_TAC
QED

(* ===== Prepare ===== *)

(* Actual count copying establishes the empty processed-array prefix. *)

Theorem abi_encoder_array_buffer_facts:
  abi_encoder_buffer_pre (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size b cap s /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size ==>
  has_type (Array NONE ty) (ListV avs) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var dst /\ mload sb s = n2w (LENGTH avs) /\
  sb < dimword (:256) /\ d < dimword (:256) /\ 32 <= output_size /\
  (d+output_size <= b \/ b+cap <= d)
Proof
  simp_tac bool_ss [abi_encoder_buffer_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_input_typed >> strip_tac >>
  drule abi_encoder_array_encoding_bound >> strip_tac >>
  qpat_assum `abi_encoder_input _ _ _ _ _ _`
    (qx_choose_then `ct` (qx_choose_then `values` (MAP_EVERY assume_tac o CONJUNCTS)) o
      REWRITE_RULE [abi_encoder_array_input_iff]) >>
  gvs[mem_word_at_eq_mload, Excl "enc_def"] >> decide_tac
QED

Theorem abi_encoder_array_count_prepare:
  abi_decode_array_header dst src MLOAD st = (cnt,st') /\ fn_has_code st st' func /\
  abi_encoder_buffer_pre (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size b cap initial /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size /\
  abi_decoder_budget first last b cap initial /\ st'.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_encoder_array_memory ei asz msz active ty avs st' src dst sb source_cap d output_size b cap 0 actual /\
    abi_decoder_operand_live st'.cs_next_var cnt /\ eval_operand cnt actual = SOME (n2w (LENGTH avs)) /\
    abi_decoder_effect first last lo hi st.cs_next_var limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_array_buffer_facts >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_array_count_live >> strip_tac >>
  mp_tac (Q.INST [`opc` |-> `MLOAD`] abi_decode_array_header_shape) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_decode_source_opcode_def] >> strip_tac >>
  mp_tac (Q.INST [`db` |-> `d:num`] abi_encoder_array_count_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_decode_frame d output_size initial actual` by
    (irule abi_decode_frame_widen >> qexistsl_tac [`d`, `32`] >> asm_simp_tac (srw_ss()) []) >>
  `abi_decoder_effect first last lo hi st.cs_next_var limit_st d output_size b cap initial actual` by
    (irule abi_decoder_scratch_free_effect >> asm_simp_tac (srw_ss()) []) >>
  `abi_encoder_buffer_pre (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size b cap actual` by
    (drule_all abi_encoder_buffer_pre_effect >> asm_simp_tac bool_ss []) >>
  `st.cs_next_var <= st'.cs_next_var` by decide_tac >>
  `abi_encoder_buffer_pre (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    st' src dst sb source_cap d output_size b cap actual` by
    (drule_all abi_encoder_buffer_pre_mono >> asm_simp_tac bool_ss []) >>
  `abi_encoder_array_prefix ty avs 0 d actual.vs_memory` by
    (irule abi_encoder_array_prefix_empty >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [abi_encoder_array_memory_def]
QED
