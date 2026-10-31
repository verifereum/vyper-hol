(* The complete straight-line setup preceding recursive ABI builtin decoding.
   TOP-LEVEL: abi_builtin_decode_setup, lower_abi_decode_setup,
     abi_builtin_decode_setup_trace, abi_builtin_decode_setup_shape.
   Helper: the output allocation instruction site. *)
Theory abiBuiltinDecodeSetup
Ancestors
  abiBuiltinDecodeHeader abiBuiltinLengthGuard abiBuiltinBoundTests abiBuiltinAllocation
  abiDecoderContract builtinAbi context compileEnv emitHelper emitHelperProps exprLoweringProps
  venomExecSemantics venomState venomInst words list rich_list arithmetic

Definition abi_builtin_decode_output_site_def:
  abi_builtin_decode_output_site st (min_size:num) (max_size:num) =
    st.cs_next_id + 2 + (if min_size = max_size then 2 else 6)
End

Definition abi_builtin_decode_setup_def:
  abi_builtin_decode_setup data min_size max_size outsz =
    do inputs <- abi_builtin_decode_header data min_size max_size;
       buf <- compile_alloc_buffer outsz;
       hi <- emit_op ADD [SND inputs; FST inputs];
       return (buf.buf_operand,SND inputs,hi)
    od
End

Theorem lower_abi_decode_setup:
  lower_abi_decode data info min_size max_size outsz =
    do ops <- abi_builtin_decode_setup data min_size max_size outsz;
       compile_abi_decode_to_buf (FST ops) (FST (SND ops)) MLOAD (SND (SND ops)) info;
       return (FST ops)
    od
Proof
  simp_tac bool_ss [FUN_EQ_THM, lower_abi_decode_phases, abi_builtin_decode_setup_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_builtin_decode_setup_trace:
  abi_builtin_decode_setup data min_size max_size outsz st = (ops,ready) ==>
  ?inputs header_st buf allocation_st hi.
    abi_builtin_decode_header data min_size max_size st = (inputs,header_st) /\
    compile_alloc_buffer outsz header_st = (buf,allocation_st) /\
    emit_op ADD [SND inputs; FST inputs] allocation_st = (hi,ready) /\
    ops = (buf.buf_operand,SND inputs,hi)
Proof
  simp_tac bool_ss [abi_builtin_decode_setup_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `abi_builtin_decode_header data min_size max_size st = (inputs,header_st)` >>
  rename1 `compile_alloc_buffer outsz header_st = (buf,allocation_st)` >>
  rename1 `emit_op ADD [SND inputs; FST inputs] allocation_st = (hi,_)` >>
  qexistsl_tac [`inputs`, `header_st`, `buf`, `allocation_st`, `hi`] >> simp[]
QED

Theorem abi_builtin_decode_setup_shape:
  abi_builtin_decode_setup data min_size max_size outsz st = (ops,ready) ==>
  ready.cs_next_id = abi_builtin_decode_output_site st min_size max_size + 2 /\
  ready.cs_next_var = st.cs_next_var + 4 + (if min_size = max_size then 1 else 5) /\
  ready.cs_blocks = st.cs_blocks /\ ready.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts ready.cs_current_insts /\ inst_extends st ready /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st ready)
Proof
  Cases_on `min_size = max_size` >>
  simp[abi_builtin_decode_setup_def, abi_builtin_decode_output_site_def,
    abi_builtin_decode_header_def, abi_builtin_length_guard_def,
    abi_builtin_interval_guard_def, abi_builtin_eq_guard_def, abi_builtin_bound_test_def,
    compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, IS_PREFIX_APPEND, is_terminator_def, mk_inst_def]
QED

Theorem abi_builtin_decode_header_outputs:
  abi_builtin_decode_header data min_size max_size st = (inputs,header_st) ==>
  FST inputs = Var (STRING #"%" (toString st.cs_next_var)) /\
  SND inputs = Var (STRING #"%" (toString (st.cs_next_var + 1)))
Proof
  simp[abi_builtin_decode_header_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac emitted_insts_emit_op >> simp[]
QED
