(* TOP-LEVEL: one bytes/string Log data field emits the explicit field
   address ADD followed by the actual runtime-length store. *)
Theory logBytesStoreCode
Ancestors
  bytesCopyCode bytesCopyExec bytesSnapshotCode abiBytestringCode
  eventTopicValueProps stmtLowering context compileEnv exprLoweringProps
  emitHelper emitHelperProps ssaOperandFrame venomState venomExecSemantics venomInst
  list rich_list words arithmetic

Theorem compile_log_bytes_field_code:
  !cenv src aty fty buf offset cs ret cs'.
    is_bytestring_type fty /\
    compile_log_store_data cenv [(src,aty)] [fty] buf offset cs = (ret,cs') ==>
    ret = () /\
    emitted_insts cs cs' =
      mk_inst cs.cs_next_id ADD [buf; Lit (n2w offset)]
        [STRING #"%" (toString cs.cs_next_var)] ::
      bytes_copy_insts (cs.cs_next_id + 1) (compiler_var_names (cs.cs_next_var + 1) 5)
        (Var (STRING #"%" (toString cs.cs_next_var))) src /\
    same_blocks cs cs' /\
    cs'.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs cs' /\
    cs'.cs_next_var = cs.cs_next_var + 6
Proof
  rpt gen_tac >> strip_tac >>
  `~is_word_type fty` by (drule_all bytestring_type_not_word >> simp[]) >>
  gvs[compile_log_store_data_def, compile_store_memory_def,
    compile_store_bytestring_def, compile_bytestring_copy_len_def,
    emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emitted_insts_def,
    bytes_copy_insts_def, compiler_var_names_EL, same_blocks_def,
    DROP_APPEND1, DROP_LENGTH_NIL]
QED

Definition log_bytes_store_result_def:
  log_bytes_store_result var_base (buf_addr:bytes32) offset src_addr ss =
    bytes_copy_result (var_base + 1) (buf_addr + n2w offset) src_addr
      (update_var (STRING #"%" (toString var_base)) (buf_addr + n2w offset) ss)
End

val log_field_add_step = List.find (fn th =>
  aconv (rhs (#1 (dest_imp (#2 (strip_forall (concl th)))))) ``ADD``)
  (CONJUNCTS step_inst_base_opcode_eqs);

Theorem log_bytes_store_execution:
  !id var_base buf src offset ss buf_addr src_addr.
    eval_operand buf ss = SOME buf_addr /\ eval_operand src ss = SOME src_addr /\
    EVERY (\name. src <> Var name) (compiler_var_names var_base 6) ==>
    run_inst_seq
      (mk_inst id ADD [buf; Lit (n2w offset)] [STRING #"%" (toString var_base)] ::
       bytes_copy_insts (id + 1) (compiler_var_names (var_base + 1) 5)
         (Var (STRING #"%" (toString var_base))) src) ss =
      OK (log_bytes_store_result var_base buf_addr offset src_addr ss)
Proof
  rpt gen_tac >> strip_tac >> fs[compiler_var_names_six] >>
  `run_inst_seq
    (bytes_copy_insts (id + 1) (compiler_var_names (var_base + 1) 5)
      (Var (STRING #"%" (toString var_base))) src)
    (update_var (STRING #"%" (toString var_base)) (buf_addr + n2w offset) ss) =
    OK (log_bytes_store_result var_base buf_addr offset src_addr ss)` by
    (PURE_REWRITE_TAC [log_bytes_store_result_def] >> irule bytes_copy_execution >>
     simp[eval_operand_update_var, eval_operand_update_var_avoids, compiler_var_names_five]) >>
  asm_simp_tac (srw_ss())
    [valOf log_field_add_step, run_inst_seq_def, mk_inst_def, exec_pure2_def, eval_operand_lit]
QED

Theorem log_bytes_store_operand_frame:
  !var_base buf_addr offset src_addr ss arg_op.
    EVERY (\name. arg_op <> Var name) (compiler_var_names var_base 6) ==>
    eval_operand arg_op (log_bytes_store_result var_base buf_addr offset src_addr ss) =
      eval_operand arg_op ss
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\name. arg_op <> Var name) (compiler_var_names (var_base + 1) 5) /\
    arg_op <> Var (STRING #"%" (toString var_base))` by
    fs[compiler_var_names_five, compiler_var_names_six] >>
  simp[log_bytes_store_result_def, bytes_copy_result_operand_frame, eval_operand_update_var_avoids]
QED

Theorem log_bytes_store_field_operand:
  !var_base buf_addr offset src_addr ss.
    eval_operand (Var (STRING #"%" (toString var_base)))
      (log_bytes_store_result var_base buf_addr offset src_addr ss) = SOME (buf_addr + n2w offset)
Proof
  rpt gen_tac >>
  `EVERY (\name. Var (STRING #"%" (toString var_base)) <> Var name)
    (compiler_var_names (var_base + 1) 5)` by simp[compiler_var_names_five] >>
  simp[log_bytes_store_result_def, bytes_copy_result_operand_frame, eval_operand_update_var]
QED

Theorem log_bytes_store_control[simp]:
  !var_base buf_addr offset src_addr ss.
    (log_bytes_store_result var_base buf_addr offset src_addr ss).vs_current_bb = ss.vs_current_bb /\
    (log_bytes_store_result var_base buf_addr offset src_addr ss).vs_inst_idx = ss.vs_inst_idx /\
    (log_bytes_store_result var_base buf_addr offset src_addr ss).vs_halted = ss.vs_halted
Proof
  simp[log_bytes_store_result_def, update_var_def]
QED
