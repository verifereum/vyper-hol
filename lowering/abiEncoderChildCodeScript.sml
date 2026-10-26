(* Exact head/offset setup and bookkeeping around a recursive child encoder. *)
Theory abiEncoderChildCode
Ancestors
  abiEncoder abiDecoderContract emitHelperProps exprLoweringProps
  compileEnv emitHelper venomInst list rich_list words arithmetic
Libs monadsyntax

Definition abi_encode_child_prefix_def:
  abi_encode_child_prefix dst head_offset dyn_ptr =
    do head <- emit_op ADD [dst;Lit (n2w head_offset)];
       offset <- emit_op MLOAD [dyn_ptr];
       child_dst <- emit_op ADD [dst;offset];
       return (head,offset,child_dst)
    od
End

Definition abi_encode_child_suffix_def:
  abi_encode_child_suffix head dyn_ptr offset child_len =
    do emit_void MSTORE [head;offset];
       next_offset <- emit_op ADD [offset;child_len];
       emit_void MSTORE [dyn_ptr;next_offset];
       return child_len
    od
End

Theorem abi_encode_dynamic_child_phases:
  compile_abi_encode_child dst src ei T head_offset dyn_ptr =
    do ops <- abi_encode_child_prefix dst head_offset dyn_ptr;
       child_len <- compile_abi_encode_to_buf (SND (SND ops)) src ei;
       abi_encode_child_suffix (FST ops) dyn_ptr (FST (SND ops)) child_len
    od
Proof
  simp_tac bool_ss [FUN_EQ_THM, Once compile_abi_encode_child_def,
    abi_encode_child_prefix_def, abi_encode_child_suffix_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_encode_static_child_trace:
  compile_abi_encode_child dst src ei F head_offset dyn_ptr st = (out,st') ==>
  ?head prepared. emit_op ADD [dst;Lit (n2w head_offset)] st = (head,prepared) /\
    compile_abi_encode_to_buf head src ei prepared = (out,st')
Proof
  simp_tac bool_ss [Once compile_abi_encode_child_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD _ st = (head,prepared)` >> qexistsl_tac [`head`, `prepared`] >> simp[]
QED

Theorem abi_encode_dynamic_child_trace:
  compile_abi_encode_child dst src ei T head_offset dyn_ptr st = (out,st') ==>
  ?ops prepared child_len child_end.
    abi_encode_child_prefix dst head_offset dyn_ptr st = (ops,prepared) /\
    compile_abi_encode_to_buf (SND (SND ops)) src ei prepared = (child_len,child_end) /\
    abi_encode_child_suffix (FST ops) dyn_ptr (FST (SND ops)) child_len child_end = (out,st')
Proof
  simp_tac bool_ss [abi_encode_dynamic_child_phases, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `abi_encode_child_prefix _ _ _ st = (ops,prepared)` >>
  rename1 `compile_abi_encode_to_buf _ src ei prepared = (child_len,child_end)` >>
  qexistsl_tac [`ops`, `prepared`, `child_len`, `child_end`] >> simp[]
QED

Theorem abi_encode_child_prefix_shape:
  abi_encode_child_prefix dst head_offset dyn_ptr st = (ops,st') ==>
  st'.cs_next_var = st.cs_next_var+3 /\ st'.cs_next_id = st.cs_next_id+3 /\
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\ inst_extends st st' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st')
Proof
  simp[abi_encode_child_prefix_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, is_alloca_op_def]
QED

Theorem abi_encode_child_suffix_shape:
  abi_encode_child_suffix head dyn_ptr offset child_len st = (out,st') ==>
  out = child_len /\ st'.cs_next_var = st.cs_next_var+1 /\ st'.cs_next_id = st.cs_next_id+3 /\
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\ inst_extends st st' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st')
Proof
  simp[abi_encode_child_suffix_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, is_alloca_op_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_CHILD_CODE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder child code not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderChildCode");
