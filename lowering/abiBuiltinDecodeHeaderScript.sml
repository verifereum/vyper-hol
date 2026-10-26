(* The actual ABI builtin's length load, data pointer and length validation.
   TOP-LEVEL: abi_builtin_decode_header, lower_abi_decode_phases,
     lower_abi_decode_trace. *)
Theory abiBuiltinDecodeHeader
Ancestors
  abiBuiltinLengthGuard abiBuiltinBoundTests abiBuiltinPrefix abiDecoderDynamicLoopSetup
  abiDecoderReentry abiDecoderContract builtinAbi context compileEnv emitHelper
  emitHelperProps exprLoweringProps venomExecSemantics venomState venomInst words list rich_list arithmetic

Definition abi_builtin_decode_header_def:
  abi_builtin_decode_header data min_size max_size =
    do len <- emit_op MLOAD [data];
       src <- emit_op ADD [data; Lit 32w];
       abi_builtin_length_guard len min_size max_size;
       return (len,src)
    od
End

Theorem lower_abi_decode_phases:
  lower_abi_decode data info min_size max_size output_size =
    do inputs <- abi_builtin_decode_header data min_size max_size;
       buf <- compile_alloc_buffer output_size;
       hi <- emit_op ADD [SND inputs; FST inputs];
       compile_abi_decode_to_buf buf.buf_operand (SND inputs) MLOAD hi info;
       return buf.buf_operand
    od
Proof
  Cases_on `min_size = max_size` >>
  asm_simp_tac bool_ss [FUN_EQ_THM, lower_abi_decode_def, abi_builtin_decode_header_def,
    abi_builtin_length_guard_def, abi_builtin_interval_guard_def,
    abi_builtin_bound_test_def, abi_builtin_eq_guard_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem lower_abi_decode_trace:
  lower_abi_decode data info min_size max_size output_size st = (out,final) ==>
  ?inputs header_st buf allocation_st hi ready.
    abi_builtin_decode_header data min_size max_size st = (inputs,header_st) /\
    compile_alloc_buffer output_size header_st = (buf,allocation_st) /\
    emit_op ADD [SND inputs; FST inputs] allocation_st = (hi,ready) /\
    compile_abi_decode_to_buf buf.buf_operand (SND inputs) MLOAD hi info ready = ((),final) /\
    out = buf.buf_operand
Proof
  simp_tac bool_ss [lower_abi_decode_phases, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `abi_builtin_decode_header data min_size max_size st = (inputs,header_st)` >>
  rename1 `compile_alloc_buffer output_size header_st = (buf,allocation_st)` >>
  rename1 `emit_op ADD [SND inputs; FST inputs] allocation_st = (hi,ready)` >>
  qexistsl_tac [`inputs`, `header_st`, `buf`, `allocation_st`, `hi`, `ready`] >> simp[]
QED

Theorem abi_builtin_decode_header_shape:
  abi_builtin_decode_header data min_size max_size st = (inputs,st') ==>
  st'.cs_next_var = st.cs_next_var + 2 + (if min_size = max_size then 1 else 5) /\
  st'.cs_next_id = st.cs_next_id + 2 + (if min_size = max_size then 2 else 6) /\
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\ inst_extends st st' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st')
Proof
  Cases_on `min_size = max_size` >>
  simp[abi_builtin_decode_header_def, abi_builtin_length_guard_def,
    abi_builtin_interval_guard_def, abi_builtin_eq_guard_def, abi_builtin_bound_test_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, IS_PREFIX_APPEND,
    is_terminator_def, is_alloca_op_def, mk_inst_def]
QED

Theorem abi_builtin_decode_header:
  abi_builtin_decode_header data min_size max_size st = (inputs,st') /\
  eval_operand data s = SOME p /\ mload (w2n p) s = n2w cnt /\
  min_size <= cnt /\ cnt <= max_size /\ max_size < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var data /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. eval_operand (FST inputs) t = SOME (n2w cnt) /\
    eval_operand (SND inputs) t = SOME (p + 32w) /\ abi_builtin_prefix st st' limit_st s t
Proof
  simp_tac bool_ss [abi_builtin_decode_header_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op MLOAD [data] st = (len,c1)` >>
  rename1 `emit_op ADD [data; Lit 32w] c1 = (src,c2)` >>
  rename1 `abi_builtin_length_guard len min_size max_size c2 = ((),end_st)` >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac abi_decoder_operand_live_emit >>
  drule abi_builtin_length_guard_shape >> strip_tac >>
  `c1.cs_next_var <= limit_st.cs_next_var /\ c2.cs_next_var <= limit_st.cs_next_var /\
   st.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var` by decide_tac >>
  drule_all abi_builtin_emit_load >> strip_tac >>
  rename1 `abi_builtin_prefix st c1 limit_st s s1` >>
  `eval_operand data s1 = SOME p /\ fresh_vars_wrt limit_st s1` by
    fs[abi_builtin_prefix_def, abi_decoder_address_frame_def] >>
  mp_tac (Q.INST [`lhs` |-> `data`, `rhs` |-> `Lit 32w`, `out` |-> `src`,
    `a` |-> `p:bytes32`, `b` |-> `32w:bytes32`,
    `st` |-> `c1`, `st'` |-> `c2`, `s` |-> `s1:venom_state`] abi_builtin_emit_add) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  rename1 `abi_builtin_prefix c1 c2 limit_st s1 s2` >>
  `abi_builtin_prefix st c2 limit_st s s2` by
    (irule abi_builtin_prefix_chain >> qexistsl_tac [`c1`, `s1`] >> simp[]) >>
  `abi_decoder_operand_live c2.cs_next_var len` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `c1.cs_next_var` >> simp[]) >>
  `eval_operand len s2 = SOME (n2w cnt) /\ fresh_vars_wrt limit_st s2` by
    fs[abi_builtin_prefix_def, abi_decoder_address_frame_def] >>
  mp_tac (Q.INST [`st` |-> `c2`, `st'` |-> `end_st`, `s` |-> `s2:venom_state`]
    abi_builtin_length_guard) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_builtin_prefix c2 end_st limit_st s2 t` >>
  `abi_builtin_prefix st end_st limit_st s t` by
    (irule abi_builtin_prefix_chain >> qexistsl_tac [`c2`, `s2`] >> simp[] >> decide_tac) >>
  qexists_tac `t` >> fs[abi_builtin_prefix_def, abi_decoder_address_frame_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_DECODE_HEADER_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin decode header not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinDecodeHeader");
