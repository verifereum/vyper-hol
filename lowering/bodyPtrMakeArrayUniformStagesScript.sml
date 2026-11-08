(* Uniform checks for concrete immutable-copy stages, without transporting
   the cursor-sensitive revert-forward exemptions of arbitrary checks. *)
Theory bodyPtrMakeArrayUniformStages
Ancestors
  bodyPtrMakeArrayImmutableOne bodyPtrMakeArrayOffsetFrame
  ghostPcTransportPtr bodyPtrMakeArrayCopyStep bodyPtrMakeArrayEmission
  immutableCopyExecution context compileEnv emitHelper emitHelperProps
  fragGasSeqPtr ptrDiscipline venomState venomExecSemantics venomInst codegenRel
  exprLoweringProps typedCopyPtr

Theorem immutable_runtime_load_checks_uniform:
  compile_imm_load_word F imm op sa = (r,sb) /\
  eval_operand op s = SOME a /\ op_taint tn op = {} /\
  allocas_from 0 s /\ ~ctx_has_dalloca ctx /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf ==>
  !j. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
        (s with vs_inst_idx := j) Gf tnf
Proof
  strip_tac >> gvs[compile_imm_load_word_def] >>
  drule emitted_insts_emit_op >> strip_tac >>
  gvs[inst_seq_ptr_def, Once step_inst_base_def, mk_inst_def, exec_read1_def] >>
  gen_tac >>
  simp[inst_seq_ptr_def, ptr_inst_ok_external_load,
       Once step_inst_base_def, mk_inst_def, exec_read1_def,
       update_var_def, allocas_from_def, step_prov_def, out_prov_def,
       lookup_var_def] >>
  conj_tac
  >- (irule (REWRITE_RULE [mk_inst_def] ptr_inst_ok_external_load) >>
      simp[allocas_from_def]) >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
       written_taint_def, out_taint_def, store_taint_def, imm_taint_def,
       lookup_var_def, source_memory_write_ranges_def,
       sized_source_write_range_def, fixed_source_write_range_def]
QED

Theorem immutable_runtime_store_checks_uniform:
  emit_void MSTORE [Var dst;value] sa = ((),sb) /\
  lookup_var dst s = SOME b /\ eval_operand value s = SOME w /\
  ptr_covers G tn dst s 32 /\ ~ctx_has_dalloca ctx /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf ==>
  !j. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
        (s with vs_inst_idx := j) Gf tnf
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  gvs[inst_seq_ptr_def, Once step_inst_base_def, mk_inst_def,
      exec_write2_def, eval_operand_def] >>
  gen_tac >>
  simp[inst_seq_ptr_def, Once step_inst_base_def, mk_inst_def,
       exec_write2_def, eval_operand_def, lookup_var_def] >>
  conj_tac
  >- (irule (REWRITE_RULE [mk_inst_def] ptr_inst_ok_mstore_raw) >> simp[]) >>
  simp[mstore_def, step_prov_def, out_prov_def,
       step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
       written_taint_def, out_taint_def, store_taint_def, imm_taint_def,
       lookup_var_def, source_memory_write_ranges_def,
       sized_source_write_range_def, fixed_source_write_range_def]
QED

Theorem immutable_offset_checks_uniform:
  compile_lit_byte_offset op off sa = (r,sb) /\
  eval_operand op s = SOME a /\ op_taint tn op = {} /\
  ~ctx_has_dalloca ctx /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf ==>
  !j. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
        (s with vs_inst_idx := j) Gf tnf
Proof
  strip_tac >> Cases_on `off = 0`
  >- gvs[compile_lit_byte_offset_def, comp_return_def,
         emitted_insts_def, inst_seq_ptr_def] >>
  Cases_on `op` >>
  gvs[eval_operand_def, compile_lit_byte_offset_def, comp_return_def]
  >- gvs[emitted_insts_def, inst_seq_ptr_def] >>
  drule emitted_insts_emit_op >> strip_tac >>
  gvs[inst_seq_ptr_def, Once step_inst_base_def, mk_inst_def,
      exec_pure2_def, eval_operand_def] >>
  gen_tac >>
  simp[inst_seq_ptr_def, Once step_inst_base_def, mk_inst_def,
       exec_pure2_def, eval_operand_def, lookup_var_def,
       REWRITE_RULE [mk_inst_def] ptr_inst_ok_copy_len_binop, op_taint_def] >>
  simp[update_var_def, step_prov_def, out_prov_def,
       step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
       written_taint_def, out_taint_def, store_taint_def, imm_taint_def,
       lookup_var_def, source_memory_write_ranges_def,
       sized_source_write_range_def, fixed_source_write_range_def]
QED
