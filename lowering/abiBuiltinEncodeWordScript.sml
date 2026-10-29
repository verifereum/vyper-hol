Theory abiBuiltinEncodeWord
Ancestors
  abiBuiltinAllocation abiDecoderReentry exprLowering context compileEnv emitHelper
  emitHelperProps exprLoweringProps venomInst words list rich_list arithmetic
  abiBuiltinEncodeAppend fragExec abiBuiltinEncodeFinish abiEncoderWrites abiDecoderContract
  abiDecoderGuards abiDecoderFrameCompose venomState venomExecSemantics finite_map
  abiEncoderSequence abiEncoderMemory abiEncoderInput abiDecoderLoop instIdxIndep
  valueEncodingProps abiBuiltinEncodeResources abiBuiltinEncodeInput byte
  abiBuiltinEncodeDispatch abiBuiltinEncodeSource abiBuiltinEncodeStagedEffect builtinAbi
  valueEncoding vyperABI vyperContext vyperAST vyperTypeSystem contractABI

(* ===== Stage Code ===== *)

(* The actual primitive AbiEncode staging is one ALLOCA and one MSTORE. *)

Theorem abi_builtin_encode_word_info:
  is_word_type ty ==>
  type_memory_bytes ce ty = 32 /\ type_to_abi_enc_info sf ce ty = AbiCopy 32
Proof
  Cases_on `ty` >>
  FIRST [rename1 `BaseT bt` >> Cases_on `bt` >>
    FIRST [rename1 `BytesT bound` >> Cases_on `bound`, all_tac] >>
    simp[is_word_type_def, type_memory_bytes_def, Once type_to_abi_enc_info_def],
    simp[is_word_type_def, type_memory_bytes_def, Once type_to_abi_enc_info_def]]
QED

Theorem abi_builtin_encode_word_stage_shape:
  compile_alloc_buffer 32 st = (buf,allocated) /\
  emit_void MSTORE [buf.buf_operand;value_op] allocated = ((),staged) ==>
  staged.cs_next_id = st.cs_next_id+2 /\ staged.cs_next_var = st.cs_next_var+1 /\
  staged.cs_blocks = st.cs_blocks /\ staged.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts staged.cs_current_insts /\ inst_extends st staged /\
  abi_decoder_operand_live staged.cs_next_var buf.buf_operand /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st staged)
Proof
  simp[compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def, abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, IS_PREFIX_APPEND, is_terminator_def, mk_inst_def]
QED

(* ===== Context ===== *)

(* Split the actual word dispatcher fragment at its constructed source. *)

Theorem abi_builtin_encode_word_context:
  compile_alloc_buffer 32 st = (buf,allocated) /\
  emit_void MSTORE [buf.buf_operand;value_op] allocated = ((),staged) /\
  lower_abi_encode ensure method_id_opt buf.buf_operand info maxlen staged = (out,final) /\
  fn_has_code st final func ==>
  fn_has_code st staged func /\ fn_has_code staged final func /\
  staged.cs_next_var <= final.cs_next_var /\ staged.cs_next_id <= final.cs_next_id /\
  staged.cs_blocks = st.cs_blocks /\ staged.cs_next_var = st.cs_next_var+1 /\
  staged.cs_next_id = st.cs_next_id+2
Proof
  strip_tac >> drule_all abi_builtin_encode_word_stage_shape >> strip_tac >>
  drule lower_abi_encode_extends >> strip_tac >>
  `cs_extends st staged` by
    (irule cs_extends_same_block >> asm_simp_tac bool_ss []) >>
  drule_all fn_has_code_split >> strip_tac >> asm_simp_tac bool_ss []
QED

(* ===== Stage Sequence ===== *)

(* Execute the actual word temporary's allocation and MSTORE, including reuse. *)

Theorem abi_builtin_encode_word_stage_sequence:
  compile_alloc_buffer 32 st = (buf,allocated) /\
  emit_void MSTORE [buf.buf_operand;value_op] allocated = ((),staged) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ sb = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (sb,32)) /\
  eval_operand value_op initial = SOME w /\ abi_decoder_operand_live st.cs_next_var value_op /\
  sb < dimword (:256) /\ staged.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st staged) initial = OK actual /\ inst_extends st staged /\
    eval_operand buf.buf_operand actual = SOME (n2w sb) /\ mload sb actual = w /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame sb 32 initial actual /\
    actual.vs_allocas = (abi_builtin_allocate_state st.cs_next_id 32 initial).vs_allocas /\
    actual.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id 32 initial).vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  `allocated.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `p` |-> `sb:num`,
    `outsz` |-> `32:num`, `st'` |-> `allocated`] abi_builtin_alloc_buffer_frame) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> strip_tac >>
  rename1 `abi_builtin_allocation_frame st.cs_next_var st.cs_next_id 32 initial addressed` >>
  qpat_assum `abi_builtin_allocation_frame _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_allocation_frame_def]) >>
  `eval_operand value_op addressed = SOME w` by
    (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  drule_all abi_builtin_store_sequence >> strip_tac >>
  `run_inst_seq (emitted_insts st staged) initial = OK (mstore sb w addressed) /\
   inst_extends st staged` by
    (mp_tac (Q.INST [`st1` |-> `allocated`, `st2` |-> `staged`, `s` |-> `initial:venom_state`,
      `s1` |-> `addressed:venom_state`, `s2` |-> `mstore sb w addressed`]
      abi_decode_sequence_chain) >> asm_simp_tac bool_ss []) >>
  `abi_decode_frame sb 32 initial (mstore sb w addressed)` by
    (irule abi_decode_frame_trans >> qexists_tac `addressed` >> asm_simp_tac bool_ss [abi_decode_frame_def]) >>
  qexists_tac `mstore sb w addressed` >> asm_simp_tac bool_ss [] >>
  rpt strip_tac >> first_x_assum irule >> asm_simp_tac bool_ss []
QED

(* ===== Stage Reach ===== *)

(* Reach the actual encoder entry after constructing its primitive source. *)

Theorem abi_builtin_encode_word_stage_reach:
  compile_alloc_buffer 32 st = (buf,allocated) /\
  emit_void MSTORE [buf.buf_operand;value_op] allocated = ((),staged) /\ fn_has_code st staged func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ sb = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (sb,32)) /\
  eval_operand value_op initial = SOME w /\ abi_decoder_operand_live st.cs_next_var value_op /\
  sb < dimword (:256) /\ staged.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand buf.buf_operand actual = SOME (n2w sb) /\ mload sb actual = w /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame sb 32 initial actual /\
    actual.vs_allocas = (abi_builtin_allocate_state st.cs_next_id 32 initial).vs_allocas /\
    actual.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id 32 initial).vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = staged.cs_current_bb /\ actual.vs_inst_idx = LENGTH staged.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_encode_word_stage_shape >> strip_tac >>
  drule_all abi_builtin_encode_word_stage_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st staged) initial = OK encoded` >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH staged.cs_current_insts` >>
  gvs[abi_decode_frame_def, fresh_vars_wrt_def, eval_op_inst_idx, mload_def] >> first_assum ACCEPT_TAC
QED

Theorem abi_builtin_encode_staged_word_input:
  is_word_type ty /\ has_type at av /\ ~is_dynamic at /\ static_length at = 32 /\
  word_to_bytes w T = enc at av /\ mload sb s = w ==>
  abi_encoder_input (type_to_abi_enc_info sf ce ty) at av sb 32 s.vs_memory
Proof
  strip_tac >> drule abi_builtin_encode_word_info >> strip_tac >>
  asm_simp_tac (srw_ss()) [abi_encoder_input_copy_iff, abi_encoder_word_window, mem_word_at_eq_mload]
QED

(* ===== Prepare ===== *)

(* Word staging establishes full encoder input; future resources depend only
   on numeric bounds and the pure metadata update of its one allocation. *)

Theorem abi_builtin_encode_word_prepare:
  compile_alloc_buffer 32 st = (buf,allocated) /\
  emit_void MSTORE [buf.buf_operand;value_op] allocated = ((),staged) /\ fn_has_code st staged func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ sb = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (sb,32)) /\
  eval_operand value_op initial = SOME w /\ abi_decoder_operand_live st.cs_next_var value_op /\
  is_word_type ty /\ has_type at av /\ ~is_dynamic at /\ static_length at = 32 /\
  word_to_bytes w T = enc at av /\ LENGTH (enc at av) <= maxlen /\
  abi_builtin_encode_resources (st with cs_next_id := st.cs_next_id+2)
    method_id_opt sb 32 p maxlen first last b cap (abi_builtin_allocate_state st.cs_next_id 32 initial) /\
  staged.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_builtin_encode_pre (type_to_abi_enc_info sf ce ty) at av staged method_id_opt
      buf.buf_operand sb 32 p maxlen first last b cap actual /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame sb 32 initial actual /\
    actual.vs_allocas = (abi_builtin_allocate_state st.cs_next_id 32 initial).vs_allocas /\
    actual.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id 32 initial).vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = staged.cs_current_bb /\ actual.vs_inst_idx = LENGTH staged.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_encode_word_stage_shape >> strip_tac >>
  qpat_assum `abi_builtin_encode_resources _ _ _ _ _ _ _ _ _ _ _`
    (assume_tac o CONJUNCT1 o SIMP_RULE (srw_ss()) [abi_builtin_encode_resources_def, LET_THM]) >>
  `sb < dimword (:256)` by decide_tac >>
  drule_all abi_builtin_encode_word_stage_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `abi_encoder_input (type_to_abi_enc_info sf ce ty) at av sb 32 actual.vs_memory` by
    (drule_all abi_builtin_encode_staged_word_input >> simp[]) >>
  `abi_builtin_encode_resources staged method_id_opt sb 32 p maxlen first last b cap actual` by
    (mp_tac (Q.INST [`st` |-> `st with cs_next_id := st.cs_next_id+2`, `ready` |-> `staged`,
      `source_cap` |-> `32:num`, `s` |-> `abi_builtin_allocate_state st.cs_next_id 32 initial`,
      `t` |-> `actual:venom_state`] abi_builtin_encode_resources_transport) >>
     impl_tac >- asm_simp_tac (srw_ss()) [] >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [abi_builtin_encode_pre_resources] >>
  first_assum ACCEPT_TAC
QED

(* ===== Correct ===== *)

(* Source semantics of the actual singleton word AbiEncode dispatcher path.
   Its source memory is established by executing allocation and MSTORE. *)

Theorem compile_abi_encode_word_source:
  let src_ty = expr_type e in
  let maxlen = abi_size_bound ce.ce_struct_fields src_ty in
  let at = vyper_to_abi_type (get_tenv cx) src_ty in
  let bytes = abi_encode_method_id_bytes method_id ++ enc at av in
  is_word_type src_ty /\ lower_value cfn ce src_ty e origin = (value_op,arg_st) /\
  compile_type_builtin_dispatch_body cfn ce vv_ty ty (AbiEncode F method_id) ret_ty [e] origin =
    (vv,final) /\ fn_has_code arg_st final func /\
  (arg_st.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  well_typed_type_builtin_args (AbiEncode F method_id) (TupleT [src_ty]) [src_ty] /\
  vyper_to_abi (get_tenv cx) src_ty v = SOME av /\
  has_type at av /\ ~is_dynamic at /\ static_length at = 32 /\
  word_to_bytes w T = enc at av /\ LENGTH (enc at av) <= maxlen /\
  eval_operand value_op prepared = SOME w /\ abi_decoder_operand_live arg_st.cs_next_var value_op /\
  ((FLOOKUP prepared.vs_allocas arg_st.cs_next_id = NONE /\ sb = prepared.vs_alloca_next) \/
    FLOOKUP prepared.vs_allocas arg_st.cs_next_id = SOME (sb,32)) /\
  abi_builtin_encode_resources (arg_st with cs_next_id := arg_st.cs_next_id+2)
    (OPTION_MAP bytes_method_id_word method_id) sb 32 p maxlen first last b cap
    (abi_builtin_allocate_state arg_st.cs_next_id 32 prepared) /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st prepared /\ ~prepared.vs_halted /\
  prepared.vs_current_bb = arg_st.cs_current_bb /\ prepared.vs_inst_idx = LENGTH arg_st.cs_current_insts /\
  abi_decode_sim ctx func initial prepared ==>
  ?actual. evaluate_type_builtin cx (AbiEncode F method_id) (TupleT [src_ty]) arg_tys [v] = INL (BytesV bytes) /\
    vv_location vv = SOME LocMemory /\ eval_operand (vv_operand vv) actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH bytes) /\ mem_bytes_at (p+32) (LENGTH bytes) actual.vs_memory = bytes /\
    val_in_memory (BaseTV (BytesT (Dynamic (maxlen+LENGTH (abi_encode_method_id_bytes method_id)))))
      (BytesV bytes) p actual.vs_memory /\
    abi_builtin_encode_staged_effect first last arg_st final limit_st sb 32 p
      (maxlen+32+LENGTH (abi_encode_method_id_bytes method_id))
      (case method_id of NONE => 0 | SOME _ => 32) b cap prepared actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all compile_abi_encode_word_trace >> strip_tac >>
  drule_all abi_builtin_encode_word_context >> strip_tac >>
  `staged.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `arg_st`, `initial` |-> `prepared:venom_state`,
    `ty` |-> `expr_type e`, `at` |-> `vyper_to_abi_type (get_tenv cx) (expr_type e)`,
    `method_id_opt` |-> `OPTION_MAP bytes_method_id_word method_id`,
    `maxlen` |-> `abi_size_bound ce.ce_struct_fields (expr_type e)`]
    (Q.ISPEC `ce.ce_struct_fields` (Q.GEN `sf` abi_builtin_encode_word_prepare))) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func prepared staged_state` >>
  mp_tac (SIMP_RULE (srw_ss()) [LET_THM, abi_builtin_encode_type_def, abi_builtin_encode_value_def]
    (Q.INST [`ensure` |-> `F`, `tys` |-> `[expr_type e]`, `vs` |-> `[v]`,
      `src` |-> `buf.buf_operand`, `start` |-> `staged`, `initial` |-> `staged_state:venom_state`,
      `source_cap` |-> `32:num`,
      `maxlen` |-> `abi_size_bound ce.ce_struct_fields (expr_type e)`, `ctx` |-> `ctx`]
      lower_abi_encode_source)) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func staged_state actual` >>
  `abi_builtin_encode_staged_effect first last arg_st final limit_st sb 32 p
    (abi_size_bound ce.ce_struct_fields (expr_type e)+32+LENGTH (abi_encode_method_id_bytes method_id))
    (case method_id of NONE => 0 | SOME _ => 32) b cap prepared actual` by
    (irule abi_builtin_encode_producer_compose >>
     qexistsl_tac [`staged_state`, `staged`] >> asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_decode_sim ctx func prepared actual` by
    (irule abi_decode_sim_trans >> qexists_tac `staged_state` >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [vv_location_def, vv_operand_def, mk_ptr_def] >>
  irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED
