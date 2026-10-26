(* Exact counters and output operands for actual straight-line array phases. *)
Theory abiEncoderArrayScalarCode
Ancestors
  abiEncoderArrayPhases abiEncoderArrayCode abiDecoderIndexInit abiDecoderContract
  abiEncoder context fragExec compileEnv emitHelperProps exprLoweringProps emitHelper venomInst words list rich_list arithmetic

Theorem abi_encode_array_dynamic_init_shape:
  abi_encode_array_dynamic_init count_op asz st = (ptrs,owner_st) ==>
  ptrs = (Var (STRING #"%" (toString st.cs_next_var)),
    Var (STRING #"%" (toString (st.cs_next_var+1)))) /\
  owner_st.cs_next_var = st.cs_next_var+3 /\ owner_st.cs_next_id = st.cs_next_id+5 /\
  owner_st.cs_blocks = st.cs_blocks /\ owner_st.cs_current_bb = st.cs_current_bb /\
  inst_extends st owner_st /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st owner_st)
Proof
  simp[abi_encode_array_dynamic_init_def, abi_decode_index_init_def, compile_alloc_buffer_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]
QED

Theorem abi_encode_array_prefix_shape:
  abi_encode_array_prefix src dst st = (ops,loop_st) ==>
  ops = (Var (STRING #"%" (toString st.cs_next_var)),
    Var (STRING #"%" (toString (st.cs_next_var+1)))) /\
  loop_st.cs_next_var = st.cs_next_var+2 /\ loop_st.cs_next_id = st.cs_next_id+4 /\
  loop_st.cs_blocks = st.cs_blocks /\ loop_st.cs_current_bb = st.cs_current_bb /\
  inst_extends st loop_st /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st loop_st)
Proof
  simp[abi_encode_array_prefix_def, abi_decode_index_init_def, compile_alloc_buffer_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]
QED

Theorem abi_encode_array_finish_shape:
  abi_encode_array_finish parent_ptr size_op st = (out,final) ==>
  out = Var (STRING #"%" (toString (st.cs_next_var+2))) /\
  final.cs_next_var = st.cs_next_var+3 /\ final.cs_next_id = st.cs_next_id+4 /\
  final.cs_blocks = st.cs_blocks /\ final.cs_current_bb = st.cs_current_bb /\
  inst_extends st final /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st final)
Proof
  simp[abi_encode_array_finish_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]
QED

Theorem abi_encode_array_exit_shape:
  (abi_encode_array_static_exit src asz st = (out,final) ==>
    out = Var (STRING #"%" (toString (st.cs_next_var+2))) /\
    final.cs_next_var = st.cs_next_var+3 /\ final.cs_next_id = st.cs_next_id+3 /\
    final.cs_blocks = st.cs_blocks /\ final.cs_current_bb = st.cs_current_bb /\ inst_extends st final /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st final)) /\
  (abi_encode_array_dynamic_exit src dyn_ptr st = (out,final) ==>
    out = Var (STRING #"%" (toString (st.cs_next_var+2))) /\
    final.cs_next_var = st.cs_next_var+3 /\ final.cs_next_id = st.cs_next_id+3 /\
    final.cs_blocks = st.cs_blocks /\ final.cs_current_bb = st.cs_current_bb /\ inst_extends st final /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st final))
Proof
  conj_tac >> simp[abi_encode_array_static_exit_def, abi_encode_array_dynamic_exit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_SCALAR_CODE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder scalar array phase not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayScalarCode");
