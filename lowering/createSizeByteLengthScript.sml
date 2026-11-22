Theory createSizeByteLength
Ancestors
  exprLowering exprLoweringProps loweringPosts emitHelper emitHelperProps compileEnv context
  valueEncodingDefs valueEncodingProps vyperTyping vyperValue
  venomExecSemantics venomMemProps venomState venomInst
  arithmetic finite_map list rich_list words bufferAllocationExecution
  stmtReasonMemory freshWrites loweringStateRelDefs ssaOperandFrame

(* Loading a dynamic-bytes header does not require any assertion about the
   bytes beyond it.  This also applies to a zero-length bytestring. *)
Theorem create_snapshot_memory_length_word:
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) =
    SOME (BaseTV (BytesT (Dynamic k))) /\
  expr_val_rel cx (BaseT (BytesT (Dynamic k))) (BytesV bytes) (vv_operand vv) s /\
  LENGTH bytes + 32 < dimword (:256) /\
  compile_create_snapshot ce vv ty sa = (snap,sb) /\
  emit_op MLOAD [snap] sb = (len,sc) /\
  run_inst_seq (emitted_insts sa sc) s = OK t ==>
  eval_operand len t = SOME (n2w (LENGTH bytes))
Proof
  strip_tac >>
  `?p. eval_operand (vv_operand vv) s = SOME p /\
       mload (w2n p) s = n2w (LENGTH bytes)` by
    fs[expr_val_rel_def, is_word_type_def, evaluate_type_def,
       val_in_memory_def, mem_word_at_eq_mload] >>
  qpat_x_assum `compile_create_snapshot _ _ _ _ = _` mp_tac >>
  simp[compile_create_snapshot_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> pairarg_tac >> simp[] >>
  simp[compile_copy_memory_dynamic_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >>
  qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  drule compile_alloc_buffer_execution >> disch_then (qspec_then `s` strip_assume_tac) >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  qpat_x_assum `run_inst_seq (emitted_insts _ _) _ = _` mp_tac >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[] >>
  qmatch_asmsub_abbrev_tac `OK u` >>
  `u.vs_memory = s.vs_memory /\ u.vs_labels = s.vs_labels /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    lookup_var (STRING #"%" (toString sa.cs_next_var)) u =
      SOME (n2w (buffer_allocation_base s sa.cs_next_id))` by
    (Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >>
     simp[Abbr `u`, lookup_var_update_var, lookup_var_def, update_var_def,
          not_fresh_at_def, buffer_allocation_fields_def]) >>
  qmatch_goalsub_abbrev_tac `mk_inst _ MLOAD [src] _` >>
  `eval_operand src s = SOME p /\ (!x. src = Var x ==> not_fresh_at sa x)` by
    simp[Abbr `src`] >>
  qpat_x_assum `Abbrev (src = _)` kall_tac >>
  qpat_x_assum `Abbrev (u = _)` kall_tac >>
  qpat_x_assum `run_inst_seq [_] _ = OK _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [run_inst_seq_def, AllCaseEqs()]) >>
  simp[Once run_inst_seq_def] >>
  `32 <= w2n ((n2w (LENGTH bytes) : bytes32) + 32w)` by
    simp[word_add_n2w, w2n_n2w] >>
  `mload (w2n p) u = n2w (LENGTH bytes)` by
    fs[mload_def, read_memory_def] >>
  `eval_operand src u = SOME p` by (Cases_on `src` >> gvs[eval_operand_def]) >>
  `src <> Var (STRING #"%" (toString (sa.cs_next_var + 1))) /\
   src <> Var (STRING #"%" (toString (sa.cs_next_var + 2)))` by
    (rpt strip_tac >> fs[not_fresh_at_def]) >>
  simp[run_inst_seq_def, step_mload_eq, step_add_eq, step_mcopy_eq,
       eval_operand_update_var_avoids, eval_operand_mcopy_eq,
       eval_operand_def, lookup_var_update_var, fresh_var_distinct,
       mload_mcopy_same, mload_update_var] >>
  fs[lookup_var_def, mcopy_vars, update_var_def, FLOOKUP_UPDATE,
     fresh_var_distinct, mload_mcopy_same] >>
  strip_tac >> gvs[mload_def, read_memory_def, FLOOKUP_UPDATE]
QED

(* The last two instructions of the raw blueprint preparation read a typed
   bytestring and turn its pointer into a data pointer. The ADD cannot
   overwrite the length result, even when the input is a borrowed pointer. *)
Theorem create_blueprint_raw_arg_length_word:
  cfn ce (expr_type e) e ca = (vv,cm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce later) vv cm = (saved,cs) /\
  unwrap_value ce saved cs = (raw_op,cu) /\
  compile_create_blueprint_args cfn ce T later [e] ca = ((data,len),cb) /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) =
    SOME (BaseTV (BytesT (Dynamic k))) /\
  expr_val_rel cx (BaseT (BytesT (Dynamic k))) (BytesV bytes) raw_op u /\
  run_inst_seq (emitted_insts cu cb) u = OK t ==>
  eval_operand len t = SOME (n2w (LENGTH bytes))
Proof
  strip_tac >>
  `?p. eval_operand raw_op u = SOME p /\ mload (w2n p) u = n2w (LENGTH bytes)` by
    fs[expr_val_rel_def, is_word_type_def, evaluate_type_def,
       val_in_memory_def, mem_word_at_eq_mload] >>
  qpat_x_assum `compile_create_blueprint_args _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_create_blueprint_args_def, comp_bind_def, comp_return_def] >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >> fs[emitted_insts_def] >>
  qpat_x_assum `run_inst_seq _ u = _` mp_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[] >> strip_tac >>
  gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
      exec_read1_def, exec_pure2_def, bind_outputs_def, eval_operand_def,
      lookup_var_update_var, fresh_var_distinct, AllCaseEqs()]
QED
