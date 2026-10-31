Theory abiBuiltinEncodeAllocate
Ancestors
  abiBuiltinEncodeCode abiBuiltinAllocation abiDecoderReentry abiDecoderContract context
  compileEnv emitHelper emitHelperProps exprLoweringProps venomInst words list rich_list
  arithmetic abiBuiltinSetupFrames abiBuiltinPrefix abiEncoderBytesPrefix abiEncoderSequence
  abiDecoderDynamicLoopSetup abiDecoderGuards abiDecoderLoop fragExec instIdxIndep venomState
  venomExecSemantics finite_map

(* ===== Code ===== *)

(* The allocation/address prefix shared by both method-ID choices. *)

Definition abi_builtin_encode_allocate_def:
  abi_builtin_encode_allocate outsz data_offset =
    do buf <- compile_alloc_buffer outsz;
       data_ptr <- emit_op ADD [buf.buf_operand;Lit (n2w data_offset)];
       return (buf.buf_operand,data_ptr)
    od
End

Theorem abi_builtin_encode_setup_allocate:
  abi_builtin_encode_setup method_id_opt maxlen =
    do ops <- abi_builtin_encode_allocate
         (maxlen+32+(case method_id_opt of NONE => 0 | SOME _ => 4))
         (32+(case method_id_opt of NONE => 0 | SOME _ => 4));
       abi_builtin_encode_method_id method_id_opt (FST ops);
       return ops
    od
Proof
  simp_tac bool_ss [FUN_EQ_THM, abi_builtin_encode_setup_def, abi_builtin_encode_allocate_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_builtin_encode_allocate_trace:
  abi_builtin_encode_allocate outsz data_offset st = (ops,address_st) ==>
  ?buf allocated data_ptr.
    compile_alloc_buffer outsz st = (buf,allocated) /\
    emit_op ADD [buf.buf_operand;Lit (n2w data_offset)] allocated = (data_ptr,address_st) /\
    ops = (buf.buf_operand,data_ptr)
Proof
  simp_tac bool_ss [abi_builtin_encode_allocate_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `compile_alloc_buffer outsz st = (buf,allocated)` >>
  rename1 `emit_op ADD _ allocated = (data_ptr,address_st)` >>
  qexistsl_tac [`buf`, `allocated`, `data_ptr`] >> simp[]
QED

Theorem abi_builtin_encode_setup_allocate_trace:
  abi_builtin_encode_setup method_id_opt maxlen st = (ops,ready) ==>
  ?address_st.
    abi_builtin_encode_allocate
      (maxlen+32+(case method_id_opt of NONE => 0 | SOME _ => 4))
      (32+(case method_id_opt of NONE => 0 | SOME _ => 4)) st = (ops,address_st) /\
    abi_builtin_encode_method_id method_id_opt (FST ops) address_st = ((),ready)
Proof
  simp_tac bool_ss [abi_builtin_encode_setup_allocate, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, LET_THM] >> pairarg_tac >> strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `abi_builtin_encode_allocate _ _ st = (ops,address_st)` >>
  qexists_tac `address_st` >> simp[]
QED

Theorem abi_builtin_encode_allocate_shape:
  abi_builtin_encode_allocate outsz data_offset st = (ops,address_st) ==>
  address_st.cs_next_id = st.cs_next_id+2 /\ address_st.cs_next_var = st.cs_next_var+2 /\
  address_st.cs_blocks = st.cs_blocks /\ address_st.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts address_st.cs_current_insts /\ inst_extends st address_st /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st address_st)
Proof
  simp[abi_builtin_encode_allocate_def, compile_alloc_buffer_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, IS_PREFIX_APPEND, is_terminator_def, mk_inst_def]
QED

Theorem abi_builtin_encode_allocate_live:
  abi_builtin_encode_allocate outsz data_offset st = (ops,address_st) ==>
  abi_decoder_operand_live address_st.cs_next_var (FST ops) /\
  abi_decoder_operand_live address_st.cs_next_var (SND ops)
Proof
  strip_tac >> drule abi_builtin_encode_allocate_trace >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac abi_decoder_operand_live_emit >>
  `abi_decoder_operand_live address_st.cs_next_var buf.buf_operand` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `allocated.cs_next_var` >> simp[]) >>
  qpat_x_assum `ops = _` (fn th => PURE_REWRITE_TAC [th, pairTheory.FST, pairTheory.SND]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* ===== Builtin Encode Allocate ===== *)

(* Execute output allocation and its first data-pointer ADD for either prefix. *)

Theorem abi_builtin_encode_allocate_sequence:
  abi_builtin_encode_allocate outsz data_offset st = (ops,address_st) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ address_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st address_st) initial = OK actual /\
    eval_operand (FST ops) actual = SOME (n2w p) /\
    eval_operand (SND ops) actual = SOME (n2w (p+data_offset)) /\
    fresh_vars_wrt limit_st actual /\
    abi_builtin_allocation_frame st.cs_next_var st.cs_next_id outsz initial actual /\
    inst_extends st address_st
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_allocate_trace >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac abi_decoder_operand_live_emit >>
  `allocated.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= allocated.cs_next_var`
    by decide_tac >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `st'` |-> `allocated`]
    abi_builtin_alloc_buffer_frame) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_builtin_allocation_frame st.cs_next_var st.cs_next_id outsz initial allocated_s` >>
  mp_tac (Q.INST [`lhs` |-> `buf.buf_operand`, `rhs` |-> `Lit (n2w data_offset)`, `out` |-> `data_ptr`,
    `a` |-> `n2w p:bytes32`, `b` |-> `n2w data_offset:bytes32`, `st` |-> `allocated`,
    `st'` |-> `address_st`, `s` |-> `allocated_s:venom_state`] abi_builtin_emit_add) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  rename1 `abi_builtin_prefix allocated address_st limit_st allocated_s actual` >>
  `eval_operand buf.buf_operand actual = SOME (n2w p)` by
    (drule_all abi_encoder_prefix_eval >> simp[]) >>
  qpat_assum `abi_builtin_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
  `abi_builtin_allocation_frame st.cs_next_var st.cs_next_id outsz initial actual` by
    (irule abi_builtin_allocation_frame_suffix >>
     qexistsl_tac [`allocated_s`, `allocated.cs_next_var`] >> asm_simp_tac bool_ss []) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `actual` >> gvs[word_add_n2w]
QED

Theorem abi_builtin_encode_allocate_reach:
  abi_builtin_encode_allocate outsz data_offset st = (ops,address_st) /\ fn_has_code st address_st func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ address_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand (FST ops) actual = SOME (n2w p) /\
    eval_operand (SND ops) actual = SOME (n2w (p+data_offset)) /\ fresh_vars_wrt limit_st actual /\
    abi_builtin_allocation_frame st.cs_next_var st.cs_next_id outsz initial actual /\
    actual.vs_current_bb = address_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH address_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_allocate_shape >> strip_tac >>
  drule_all abi_builtin_encode_allocate_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st address_st) initial = OK encoded` >>
  `~encoded.vs_halted` by fs[abi_builtin_allocation_frame_def] >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH address_st.cs_current_insts` >>
  gvs[abi_builtin_allocation_frame_def, fresh_vars_wrt_def, eval_op_inst_idx]
QED
