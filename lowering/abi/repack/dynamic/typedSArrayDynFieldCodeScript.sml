(* TOP-LEVEL: actual array Log-field dispatch and generated-name lifetimes for
   the explicit address ADD followed by a recursively compiled copy.
   Helper: emit_op preserves the parent's label counter. *)
Theory typedSArrayDynFieldCode
Ancestors
  typedArrayLoopNames fieldAddressProps abiBytestringCode abiStaticLoopCode memoryLayoutDefs
  logBytesStoreProps memoryValueDefs valueEncoding context compileEnv emitHelper venomState list words arithmetic

Theorem compile_store_memory_array_dispatch:
  !cenv dst src dst_elem src_elem dst_bound src_bound.
    ArrayT dst_elem dst_bound <> ArrayT src_elem src_bound ==>
    compile_store_memory cenv src dst (ArrayT dst_elem dst_bound) (ArrayT src_elem src_bound) =
    compile_store_memory_typed cenv dst (ArrayT dst_elem dst_bound) src (ArrayT src_elem src_bound)
Proof
  rpt gen_tac >> DISCH_TAC >>
  simp[compile_store_memory_def, is_word_type_def, is_bytestring_type_def, tuple_memory_layout_eq_def]
QED

Theorem emit_op_next_label:
  !opc ops cs dst mid.
    emit_op opc ops cs = (dst,mid) ==> mid.cs_next_label = cs.cs_next_label
Proof
  simp[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >> rpt strip_tac >> gvs[]
QED

Theorem emit_field_address_copy_names:
  !buf offset cs dst mid src copy_names.
    emit_op ADD [buf; Lit (n2w offset)] cs = (dst,mid) /\
    EVERY (\name. src <> Var name) (compiler_var_names cs.cs_next_var (SUC copy_names)) ==>
    src <> dst /\
    EVERY (\name. dst <> Var name /\ src <> Var name) (compiler_var_names mid.cs_next_var copy_names)
Proof
  rpt gen_tac >> strip_tac >> drule emit_field_address_code >> strip_tac >>
  `dst = Var (compiler_var_name cs.cs_next_var 0)` by simp[compiler_var_name_def] >> conj_tac
  >- (mp_tac (Q.SPECL [`src`, `cs.cs_next_var`, `SUC copy_names`, `0`] compiler_var_names_avoid_index) >> simp[]) >>
  asm_simp_tac bool_ss [EVERY_CONJ] >> conj_tac
  >- (mp_tac (Q.SPECL [`cs.cs_next_var`, `1`, `copy_names`, `0`] compiler_var_names_before) >>
      simp[]) >>
  mp_tac (Q.SPECL [`src`, `cs.cs_next_var`, `SUC copy_names`, `1`, `copy_names`] compiler_var_names_avoid_segment) >> simp[]
QED

Theorem emit_field_copy_operand_frame:
  !buf offset cs dst mid before addressed after copy_names.
    emit_op ADD [buf; Lit (n2w offset)] cs = (dst,mid) /\
    (!arg_op. arg_op <> dst ==> eval_operand arg_op addressed = eval_operand arg_op before) /\
    (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names mid.cs_next_var copy_names) ==>
      eval_operand arg_op after = eval_operand arg_op addressed) ==>
    !arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names cs.cs_next_var (SUC copy_names)) ==>
      eval_operand arg_op after = eval_operand arg_op before
Proof
  rpt gen_tac >> strip_tac >> qx_gen_tac `arg_op` >> DISCH_TAC >>
  mp_tac (Q.SPECL [`buf`, `offset`, `cs`, `dst`, `mid`, `arg_op`, `copy_names`] emit_field_address_copy_names) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  `EVERY (\name. arg_op <> Var name) (compiler_var_names mid.cs_next_var copy_names)` by fs[EVERY_CONJ] >>
  qpat_x_assum `!arg_op. EVERY _ _ ==> _` (qspec_then `arg_op` mp_tac) >>
  qpat_x_assum `!arg_op. _ <> dst ==> _` (qspec_then `arg_op` mp_tac) >> simp[]
QED

Theorem field_address_typed_memory_frame:
  !tv before addressed after (buf_addr:bytes32) field_offset.
    addressed.vs_memory = before.vs_memory /\ w2n buf_addr + field_offset < dimword(:256) /\
    (!other_tv other_v offset.
      memory_value_rel other_tv other_v offset addressed.vs_memory /\ val_wf other_tv other_v /\
      (offset + type_memory_size other_tv <= w2n (buf_addr + n2w field_offset) \/
        w2n (buf_addr + n2w field_offset) + type_memory_size tv <= offset) ==>
      memory_value_rel other_tv other_v offset after.vs_memory) ==>
    !other_tv other_v offset.
      memory_value_rel other_tv other_v offset before.vs_memory /\ val_wf other_tv other_v /\
      (offset + type_memory_size other_tv <= w2n buf_addr + field_offset \/
        w2n buf_addr + field_offset + type_memory_size tv <= offset) ==>
      memory_value_rel other_tv other_v offset after.vs_memory
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  qpat_x_assum `!other_tv other_v offset. _`
    (qspecl_then [`other_tv`, `other_v`, `offset`] mp_tac) >>
  impl_tac >- (asm_simp_tac bool_ss [log_field_address] >> decide_tac) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed fixed/dynamic Log field code theorem: " ^ name)
  end) (DB.thms "typedSArrayDynFieldCode")
