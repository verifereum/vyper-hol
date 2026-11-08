(* TOP-LEVEL: actual Log field lowering stores a compatible bytes/string
   argument at the declared buffer offset, including capacity widening. *)
Theory logBytesStoreProps
Ancestors
  vyperEventArgCompat
  logBytesStoreCode bytesCopyCode bytesCopyExec bytesCopyMemory bytesCopyProps
  bytesSnapshotMemory memoryValueDefs valueLoadProps eventTopicValueProps
  vyperEventCompatibility vyperTypeSystem vyperValue vyperTyping
  compileEnv exprLoweringProps emitHelper fragBlockPath fragExec instIdxIndep
  venomState venomInst list words arithmetic

Theorem log_field_address:
  !addr offset.
    w2n (addr:bytes32) + offset < dimword(:256) ==>
    w2n (addr + n2w offset) = w2n addr + offset
Proof
  rpt gen_tac >> Cases_on `addr` >> simp[word_add_n2w] >> strip_tac >> simp[]
QED

Theorem log_bytes_store_widened_layout:
  !tenv fty aty ftv atv v var_base buf_addr offset src_addr ss.
    is_bytestring_type fty /\ is_bytestring_type aty /\
    evaluate_type tenv fty = SOME ftv /\ evaluate_type tenv aty = SOME atv /\
    value_has_type atv v /\ memory_value_rel atv v (w2n src_addr) ss.vs_memory /\
    type_memory_size atv < dimword(:256) ==>
    memory_value_rel ftv v (w2n (buf_addr + n2w offset))
      (log_bytes_store_result var_base buf_addr offset src_addr ss).vs_memory
Proof
  rpt gen_tac >> strip_tac >> PURE_REWRITE_TAC [log_bytes_store_result_def] >>
  mp_tac (Q.SPECL [`tenv`, `fty`, `aty`, `ftv`, `atv`, `v`, `(var_base:num) + 1`,
    `buf_addr + n2w offset`, `src_addr`,
    `update_var (STRING #"%" (toString (var_base:num))) (buf_addr + n2w offset) ss`]
    bytes_copy_result_widened_layout) >> simp[update_var_def]
QED

Theorem log_bytes_store_preserves_field_region:
  !tenv fty aty ftv atv v var_base buf_addr offset src_addr ss other_tv other_v other_offset.
    is_bytestring_type fty /\ is_bytestring_type aty /\
    evaluate_type tenv fty = SOME ftv /\ evaluate_type tenv aty = SOME atv /\
    value_has_type ftv v /\ value_has_type atv v /\
    memory_value_rel atv v (w2n src_addr) ss.vs_memory /\ type_memory_size atv < dimword(:256) /\
    w2n buf_addr + offset < dimword(:256) /\
    memory_value_rel other_tv other_v other_offset ss.vs_memory /\ val_wf other_tv other_v /\
    (other_offset + type_memory_size other_tv <= w2n buf_addr + offset \/
      w2n buf_addr + offset + type_memory_size ftv <= other_offset) ==>
    memory_value_rel other_tv other_v other_offset
      (log_bytes_store_result var_base buf_addr offset src_addr ss).vs_memory
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  PURE_REWRITE_TAC [log_bytes_store_result_def] >>
  mp_tac (Q.SPECL [`tenv`, `fty`, `aty`, `ftv`, `atv`, `v`, `(var_base:num) + 1`,
    `buf_addr + n2w offset`, `src_addr`,
    `update_var (STRING #"%" (toString (var_base:num))) (buf_addr + n2w offset) ss`,
    `other_tv`, `other_v`, `other_offset`] bytes_copy_result_preserves_field_region) >>
  impl_tac >- simp[update_var_def, log_field_address] >> simp[]
QED

Theorem compile_log_bytes_field_path:
  !tenv ctx func cenv fty aty ftv atv v buf src offset cs ret cs' ss buf_addr src_addr.
    is_bytestring_type fty /\ event_arg_compatible fty aty /\
    evaluate_type tenv fty = SOME ftv /\ evaluate_type tenv aty = SOME atv /\
    compile_log_store_data cenv [(src,aty)] [fty] buf offset cs = (ret,cs') /\
    lowered_value_rel aty atv v src ss /\
    eval_operand buf ss = SOME buf_addr /\ eval_operand src ss = SOME src_addr /\
    type_memory_size atv < dimword(:256) /\ w2n buf_addr + offset < dimword(:256) /\
    EVERY (\name. src <> Var name) (compiler_var_names cs.cs_next_var 5) /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ value_has_type ftv v /\
      memory_value_rel ftv v (w2n buf_addr + offset) out.vs_memory /\
      eval_operand (Var (STRING #"%" (toString cs.cs_next_var))) out =
        SOME (buf_addr + n2w offset) /\
      (!other_tv other_v other_offset.
        memory_value_rel other_tv other_v other_offset ss.vs_memory /\ val_wf other_tv other_v /\
        (other_offset + type_memory_size other_tv <= w2n buf_addr + offset \/
          w2n buf_addr + offset + type_memory_size ftv <= other_offset) ==>
        memory_value_rel other_tv other_v other_offset out.vs_memory) /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names cs.cs_next_var 5) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt strip_tac >> drule_all compile_log_bytes_field_code >> strip_tac >>
  `is_bytestring_type aty` by (drule_all event_arg_compatible_bytestring >> simp[]) >>
  `~is_word_type aty` by (drule_all bytestring_type_not_word >> simp[]) >>
  `memory_value_rel atv v (w2n src_addr) ss.vs_memory /\ value_has_type atv v` by
    gvs[lowered_value_rel_def] >>
  `value_has_type ftv v` by
    (drule_all (cj 1 event_arg_compatible_value_has_type) >> simp[]) >>
  `memory_value_rel ftv v (w2n buf_addr + offset)
    (log_bytes_store_result cs.cs_next_var buf_addr offset src_addr ss).vs_memory` by
    (mp_tac (Q.SPECL [`tenv`, `fty`, `aty`, `ftv`, `atv`, `v`, `cs.cs_next_var`,
       `buf_addr`, `offset`, `src_addr`, `ss`] log_bytes_store_widened_layout) >>
     simp[log_field_address]) >>
  `run_inst_seq (emitted_insts cs cs') ss =
    OK (log_bytes_store_result cs.cs_next_var buf_addr offset src_addr ss)` by
    simp[log_bytes_store_execution] >>
  `!other_tv other_v other_offset.
    memory_value_rel other_tv other_v other_offset ss.vs_memory /\ val_wf other_tv other_v /\
    (other_offset + type_memory_size other_tv <= w2n buf_addr + offset \/
      w2n buf_addr + offset + type_memory_size ftv <= other_offset) ==>
    memory_value_rel other_tv other_v other_offset
      (log_bytes_store_result cs.cs_next_var buf_addr offset src_addr ss).vs_memory` by
    (rpt gen_tac >> DISCH_TAC >>
     mp_tac (Q.SPECL [`tenv`, `fty`, `aty`, `ftv`, `atv`, `v`, `cs.cs_next_var`,
       `buf_addr`, `offset`, `src_addr`, `ss`, `other_tv`, `other_v`, `other_offset`]
       log_bytes_store_preserves_field_region) >> simp[]) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs`, `cs'`, `ss`,
    `log_bytes_store_result cs.cs_next_var buf_addr offset src_addr ss`] fragment_path_emitted) >>
  impl_tac >- simp[bytes_copy_straight, mk_inst_def, is_terminator_def] >> strip_tac >>
  qexists_tac `(log_bytes_store_result cs.cs_next_var buf_addr offset src_addr ss) with
    vs_inst_idx := LENGTH cs'.cs_current_insts` >>
  fs[eval_op_inst_idx, log_bytes_store_field_operand, log_bytes_store_operand_frame] >>
  first_assum MATCH_ACCEPT_TAC
QED
