Theory abiEncoderArrayParent
Ancestors
  abiEncoderArrayPhases abiEncoderComplexCode abiDecoderIndexInit abiDecoderArrayHeader
  compileEnv emitHelper words list abiEncoderArrayContext abiEncoderCursorStoreLoad
  abiEncoderBytesPrefix abiBuiltinPrefix abiDecoderDynamicLoopSetup abiDecoderReentry
  abiDecoderFrameCompose abiDecoderContract abiDecoderGuards emitHelperProps exprLoweringProps
  venomState venomExecSemantics arithmetic abiEncoderSequence abiDecoderLoop fragExec
  instIdxIndep abiEncoderWrites abiEncoderReentryLeaves abiEncoderMemory valueEncoding
  valueEncodingProps abiDecoderArrayLoopInit abiEncoderArrayMemory abiEncoderArrayPrefix
  abiEncoderArrayBodyCode abiEncoderInput abiEncoderChildInputs abiEncoderBufferFrame
  abiDecoderCorrectLeaves abiDecoderEffect contractABI abiEncoderChildEffect
  abiDecoderAllocation abiDecoderProtectedScratch abiDecoderArrayInitExec
  abiDecoderPrimitiveLoopFrames abiDecoderFrame finite_map pred_set abiEncoderZeroCursorPrepare
  abiEncoderComplexPrefix abiEncoderArrayHeaderMemory abiEncoderMembersDefs rich_list
Libs
  monadsyntax

(* Reuse the proved real zero-cursor allocation when establishing array entry. *)
Theorem abi_decode_index_init_complex_prefix:
  abi_decode_index_init = abi_encode_complex_prefix []
Proof
  simp[abi_decode_index_init_def, abi_encode_complex_prefix_def]
QED

Theorem abi_encode_array_prefix_split:
  abi_encode_array_prefix src dst =
    do parent_ptr <- abi_encode_complex_prefix [];
       cnt <- abi_decode_array_header dst src MLOAD;
       return (parent_ptr,cnt)
    od
Proof
  simp_tac bool_ss [FUN_EQ_THM, abi_encode_array_prefix_def,
    GSYM abi_decode_index_init_complex_prefix, abi_decode_array_header_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_encode_array_prefix_trace:
  abi_encode_array_prefix src dst st = (ops,loop_st) ==>
  ?parent_ptr allocated cnt.
    abi_encode_complex_prefix [] st = (parent_ptr,allocated) /\
    abi_decode_array_header dst src MLOAD allocated = (cnt,loop_st) /\
    ops = (parent_ptr,cnt)
Proof
  simp_tac bool_ss [abi_encode_array_prefix_split, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `abi_encode_complex_prefix [] st = (parent_ptr,allocated)` >>
  rename1 `abi_decode_array_header dst src MLOAD allocated = (cnt,ready)` >>
  qexistsl_tac [`parent_ptr`, `allocated`, `cnt`] >> asm_simp_tac bool_ss []
QED

(* ===== Sequence ===== *)

(* Execute the real parent cursor MLOAD/ADD/MSTORE/MLOAD bookkeeping. *)

Theorem abi_encode_array_finish_trace:
  abi_encode_array_finish parent_ptr size_op st = (out,final) ==>
  ?old c1 next c2 c3.
    emit_op MLOAD [parent_ptr] st = (old,c1) /\
    emit_op ADD [old;size_op] c1 = (next,c2) /\
    emit_void MSTORE [parent_ptr;next] c2 = ((),c3) /\
    emit_op MLOAD [parent_ptr] c3 = (out,final)
Proof
  simp_tac bool_ss [abi_encode_array_finish_def, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op MLOAD [parent_ptr] st = (old,c1)` >>
  rename1 `emit_op ADD [old;size_op] c1 = (next,c2)` >>
  rename1 `emit_void MSTORE [parent_ptr;next] c2 = ((),c3)` >>
  qexistsl_tac [`old`, `c1`, `next`, `c2`, `c3`] >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_cursor_sum:
  emit_op MLOAD [cursor_op] st = (old,c1) /\ emit_op ADD [old;size_op] c1 = (next,c2) /\
  eval_operand cursor_op s = SOME (n2w slot) /\ mload slot s = old_word /\
  eval_operand size_op s = SOME size_word /\ abi_decoder_operand_live st.cs_next_var size_op /\
  slot < dimword (:256) /\ c2.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?prepared. eval_operand next prepared = SOME (old_word+size_word) /\
    abi_builtin_prefix st c2 limit_st s prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> imp_res_tac emitted_insts_emit_op >>
  `c1.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= c1.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`src` |-> `cursor_op`, `out` |-> `old`, `p` |-> `n2w slot:bytes32`,
    `st'` |-> `c1`] abi_builtin_emit_load) >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_builtin_prefix st c1 limit_st s loaded` >>
  `eval_operand old loaded = SOME old_word /\ fresh_vars_wrt limit_st loaded` by
    fs[abi_builtin_prefix_def, w2n_n2w] >>
  `eval_operand size_op loaded = SOME size_word` by
    (mp_tac (Q.INST [`op` |-> `size_op`, `w` |-> `size_word:bytes32`,
      `st'` |-> `c1`, `t` |-> `loaded:venom_state`] abi_encoder_prefix_eval) >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`lhs` |-> `old`, `rhs` |-> `size_op`, `out` |-> `next`,
    `a` |-> `old_word:bytes32`, `b` |-> `size_word:bytes32`,
    `st` |-> `c1`, `st'` |-> `c2`, `s` |-> `loaded:venom_state`] abi_builtin_emit_add) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_builtin_prefix c1 c2 limit_st loaded prepared` >>
  qexists_tac `prepared` >> asm_simp_tac bool_ss [] >>
  irule abi_builtin_prefix_chain >> qexistsl_tac [`c1`, `loaded`] >> asm_simp_tac bool_ss []
QED

Theorem abi_encode_array_finish_sequence:
  abi_encode_array_finish parent_ptr size_op st = (out,final) /\
  eval_operand parent_ptr initial = SOME (n2w slot) /\ mload slot initial = old_word /\
  eval_operand size_op initial = SOME size_word /\
  abi_decoder_operand_live st.cs_next_var parent_ptr /\ abi_decoder_operand_live st.cs_next_var size_op /\
  slot < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st final) initial = OK actual /\ inst_extends st final /\
    eval_operand out actual = SOME (old_word+size_word) /\ mload slot actual = old_word+size_word /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame slot 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> drule abi_encode_array_finish_trace >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  `c2.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= c2.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`cursor_op` |-> `parent_ptr`, `s` |-> `initial:venom_state`] abi_encoder_cursor_sum) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `eval_operand parent_ptr prepared = SOME (n2w slot)` by
    (mp_tac (Q.INST [`op` |-> `parent_ptr`, `w` |-> `n2w slot:bytes32`, `st'` |-> `c2`,
      `s` |-> `initial:venom_state`, `t` |-> `prepared:venom_state`] abi_encoder_prefix_eval) >>
     asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live c2.cs_next_var parent_ptr` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss []) >>
  qpat_assum `abi_builtin_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
  mp_tac (Q.INST [`cursor_op` |-> `parent_ptr`, `value_op` |-> `next`, `st` |-> `c2`, `stored_st` |-> `c3`,
    `w` |-> `(old_word:bytes32)+size_word`, `s` |-> `prepared:venom_state`] abi_encoder_cursor_store_load) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `run_inst_seq (emitted_insts st final) initial = OK actual /\ inst_extends st final` by
    (mp_tac (Q.INST [`st1` |-> `c2`, `st2` |-> `final`, `s` |-> `initial:venom_state`,
      `s1` |-> `prepared:venom_state`, `s2` |-> `actual:venom_state`] abi_decode_sequence_chain) >>
     asm_simp_tac bool_ss []) >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  `abi_decode_frame slot 32 initial actual` by
    (irule abi_decode_frame_trans >> qexists_tac `prepared` >>
     asm_simp_tac bool_ss [abi_decode_frame_def]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >> rpt strip_tac >>
  `eval_operand op prepared = SOME w` by (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  qpat_x_assum `!op w. abi_decoder_operand_live c2.cs_next_var op /\ _ ==> _` irule >>
  asm_simp_tac bool_ss [] >> irule abi_decoder_operand_live_mono >>
  qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss [] >> decide_tac
QED

(* ===== Reach ===== *)

(* Parent cursor bookkeeping reaches its real containing-function endpoint. *)

Theorem abi_encode_array_finish_reach:
  abi_encode_array_finish parent_ptr size_op st = (out,final) /\ fn_has_code st final func /\
  eval_operand parent_ptr initial = SOME (n2w slot) /\ mload slot initial = old_word /\
  eval_operand size_op initial = SOME size_word /\
  abi_decoder_operand_live st.cs_next_var parent_ptr /\ abi_decoder_operand_live st.cs_next_var size_op /\
  slot < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (old_word+size_word) /\ mload slot actual = old_word+size_word /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame slot 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encode_array_finish_shape >> strip_tac >>
  drule_all abi_encode_array_finish_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st final) initial = OK encoded` >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH final.cs_current_insts` >>
  gvs[abi_decode_frame_def, fresh_vars_wrt_def, eval_op_inst_idx, mload_def] >>
  first_assum ACCEPT_TAC
QED

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

(* ===== Finish ===== *)

(* Updating the registered parent cursor preserves the completed ABI output and other scratch. *)

Theorem abi_encoder_array_parent_finish:
  abi_encode_array_finish parent_ptr size_op st = (out,final) /\ fn_has_code st final func /\
  eval_operand parent_ptr initial = SOME (n2w slot) /\ mload slot initial = 0w /\
  eval_operand size_op initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var parent_ptr /\ abi_decoder_operand_live st.cs_next_var size_op /\
  mem_bytes_at d len initial.vs_memory = bytes /\ len <= output_size /\
  (d+output_size <= b \/ b+cap <= d) /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < last /\
  lo <= site /\ site < hi /\ FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at d len actual.vs_memory = bytes /\
    eval_operand out actual = SOME (n2w len) /\ mload slot actual = n2w len /\
    FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
    abi_decode_footprint_frame [(slot,32)] initial actual /\
    abi_decoder_effect first last lo hi st.cs_next_var limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `site IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  qpat_assum `abi_decoder_budget _ _ _ _ _`
    (assume_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_decoder_budget_def]) >>
  `slot < dimword (:256)` by decide_tac >>
  mp_tac (Q.INST [`old_word` |-> `0w:bytes32`, `size_word` |-> `n2w len:bytes32`]
    abi_encode_array_finish_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_decode_footprint_frame [(slot,32)] initial actual /\
   abi_decode_footprint_frame [(d,output_size);(slot,32)] initial actual` by
    (conj_tac >> irule abi_decoder_frame_in_footprint >> qexistsl_tac [`slot`, `32`] >> simp[]) >>
  `abi_decoder_scratch_frame first last lo hi initial actual` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`,
      `sz` |-> `output_size:num`] abi_encoder_owned_scratch_frame) >> asm_simp_tac bool_ss []) >>
  `abi_decoder_budget first last b cap actual` by
    (drule_all abi_decoder_budget_transport >> asm_simp_tac bool_ss []) >>
  `abi_decode_frame b cap initial actual` by
    (irule abi_decode_frame_widen >> qexistsl_tac [`slot`, `32`] >> asm_simp_tac bool_ss []) >>
  `abi_decode_footprint_frame [(d,output_size);(b,cap)] initial actual` by
    (irule abi_decoder_frame_in_footprint >> qexistsl_tac [`b`, `cap`] >> simp[]) >>
  `mem_bytes_at d len actual.vs_memory = bytes` by
    (qpat_assum `abi_decode_frame slot 32 initial actual`
       (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
     `d+len <= slot \/ slot+32 <= d` by decide_tac >>
     qpat_x_assum `!p n. _` (qspecl_then [`d`, `len`] mp_tac) >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [abi_decoder_effect_def]
QED

(* ===== Prepare ===== *)

(* Execute the actual parent allocation and count copy before either array loop. *)

Theorem abi_encode_array_prefix_context:
  abi_encode_array_prefix src dst st = (ops,loop_st) /\ fn_has_code st loop_st func ==>
  ?parent_ptr allocated cnt.
    abi_encode_complex_prefix ([]:(abi_enc_info # num # num # bool) list) st = (parent_ptr,allocated) /\
    abi_decode_array_header dst src MLOAD allocated = (cnt,loop_st) /\ ops = (parent_ptr,cnt) /\
    fn_has_code st allocated func /\ fn_has_code allocated loop_st func /\
    allocated.cs_next_var = st.cs_next_var+1 /\ allocated.cs_next_id = st.cs_next_id+2 /\
    loop_st.cs_next_var = st.cs_next_var+2 /\ loop_st.cs_next_id = st.cs_next_id+4
Proof
  strip_tac >> drule abi_encode_array_prefix_trace >> strip_tac >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  mp_tac (Q.INST [`opc` |-> `MLOAD`, `st` |-> `allocated`, `st'` |-> `loop_st`]
    abi_decode_array_header_shape) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_decode_source_opcode_def] >> strip_tac >>
  `cs_extends st allocated /\ cs_extends allocated loop_st` by
    (conj_tac >> irule cs_extends_same_block >> fs[inst_extends_def, IS_PREFIX_APPEND]) >>
  mp_tac (Q.SPECL [`st`, `allocated`, `loop_st`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM abi_decode_index_init_complex_prefix]) >>
  pure_rewrite_tac [GSYM abi_decode_index_init_complex_prefix] >>
  qexistsl_tac [`parent_ptr`, `allocated`, `cnt`] >> asm_simp_tac arith_ss []
QED

Theorem abi_encoder_array_parent_prepare:
  abi_encode_array_prefix src dst st = (ops,loop_st) /\ fn_has_code st loop_st func /\
  abi_encoder_buffer_pre (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size b cap initial /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  loop_st.cs_next_id <= hi /\ hi <= last /\ loop_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual slot.
    abi_encoder_array_memory ei asz msz active ty avs loop_st src dst sb source_cap d output_size b cap 0 actual /\
    abi_encoder_cursor T (FST ops) st.cs_next_id slot first st.cs_next_id loop_st 0 actual /\
    abi_decoder_operand_live loop_st.cs_next_var (SND ops) /\
    eval_operand (SND ops) actual = SOME (n2w (LENGTH avs)) /\
    abi_decoder_effect first last st.cs_next_id hi st.cs_next_var limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = loop_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_prefix_context >> strip_tac >>
  `allocated.cs_next_var <= limit_st.cs_next_var /\ allocated.cs_next_id <= hi /\
   st.cs_next_id < last /\ st.cs_next_id < allocated.cs_next_id /\
   st.cs_next_var <= allocated.cs_next_var /\ allocated.cs_next_var <= loop_st.cs_next_var /\
   allocated.cs_next_id <= loop_st.cs_next_id` by decide_tac >>
  mp_tac (Q.INST [`ei` |-> `AbiDynArray ei asz msz active`, `at` |-> `Array NONE ty`,
    `av` |-> `ListV avs`, `cursor_op` |-> `parent_ptr`, `prepared` |-> `allocated`]
    abi_encoder_zero_cursor_prepare) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial allocated_state` >>
  `fresh_vars_wrt limit_st allocated_state /\ abi_decoder_budget first last b cap allocated_state` by
    fs[abi_decoder_effect_def] >>
  mp_tac (Q.INST [`st` |-> `allocated`, `st'` |-> `loop_st`,
    `initial` |-> `allocated_state:venom_state`, `lo` |-> `allocated.cs_next_id`]
    abi_encoder_array_count_prepare) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_encoder_cursor T parent_ptr st.cs_next_id slot first st.cs_next_id allocated 0 actual` by
    (mp_tac (Q.INST [`active` |-> `T`, `cursor_op` |-> `parent_ptr`, `site` |-> `st.cs_next_id`,
      `lo` |-> `st.cs_next_id`, `st` |-> `allocated`, `off` |-> `0:num`,
      `owned_lo` |-> `allocated.cs_next_id`, `owned_hi` |-> `hi:num`, `next` |-> `allocated.cs_next_var`,
      `initial` |-> `allocated_state:venom_state`, `sz` |-> `output_size:num`]
      abi_encoder_cursor_effect_protected) >> impl_tac >- asm_simp_tac (srw_ss()) [] >> simp[]) >>
  `abi_encoder_cursor T parent_ptr st.cs_next_id slot first st.cs_next_id loop_st 0 actual` by
    (drule_all abi_encoder_cursor_mono >> asm_simp_tac bool_ss []) >>
  `abi_decoder_effect first last st.cs_next_id hi st.cs_next_var limit_st d output_size b cap allocated_state actual` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`d`, `hi`, `allocated.cs_next_id`, `allocated.cs_next_var`, `output_size`] >>
     asm_simp_tac (srw_ss()) [] >> decide_tac) >>
  `abi_decoder_effect first last st.cs_next_id hi st.cs_next_var limit_st d output_size b cap initial actual` by
    (irule abi_decoder_effect_trans >> qexists_tac `allocated_state` >> asm_simp_tac bool_ss []) >>
  qpat_assum `loop_st.cs_next_var = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  qexistsl_tac [`actual`, `slot`] >> asm_simp_tac (srw_ss()) [Excl "enc_def"] >>
  irule abi_decode_sim_trans >> qexists_tac `allocated_state` >> asm_simp_tac bool_ss []
QED
