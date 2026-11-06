(* TOP-LEVEL: the recursive typed store's scalar case loads a word through
   its source pointer before storing it. Its real instruction path reuses
   the ABI word-copy proof and permits outputs from earlier iterations. *)
Theory typedWordStoreProps
Ancestors
  typedCopyStateFrame abiEncoder abiEncoderPathProps memoryValueDefs memoryValueFrame valueLoadProps valueEncoding
  valueEncodingProps context compileEnv exprLoweringProps emitHelper emitHelperProps
  fragBlockPath fragExec instIdxIndep ssaOperandFrame dynCopyExec
  vyperValue vyperTyping venomState venomInst list words arithmetic

Theorem compile_typed_word_abi_code:
  !cenv dst ty src src_ty cs ret cs'.
    is_word_type ty /\ compile_store_memory_typed cenv dst ty src src_ty cs = (ret,cs') ==>
    ret = () /\ compile_abi_encode_static dst src cs = (Lit 32w,cs')
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [Once compile_store_memory_typed_def] >>
  simp[compile_abi_encode_static_def, emit_op_def, emit_void_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def] >> rpt strip_tac >> gvs[]
QED

Theorem compile_store_memory_typed_word_path:
  !tenv ctx func cenv ty tv v dst src src_ty cs ret cs' ss dst_addr src_addr.
    is_word_type ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
    memory_value_rel tv v (w2n src_addr) ss.vs_memory /\
    compile_store_memory_typed cenv dst ty src src_ty cs = (ret,cs') /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    dst <> Var (STRING #"%" (toString cs.cs_next_var)) /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ copy_state_frame ss out /\ memory_value_rel tv v (w2n dst_addr) out.vs_memory /\
      (!arg_op. arg_op <> Var (STRING #"%" (toString cs.cs_next_var)) ==>
        eval_operand arg_op out = eval_operand arg_op ss) /\
      (!other_tv other_v offset.
        memory_value_rel other_tv other_v offset ss.vs_memory /\ val_wf other_tv other_v /\
        (offset + type_memory_size other_tv <= w2n dst_addr \/ w2n dst_addr + 32 <= offset) ==>
        memory_value_rel other_tv other_v offset out.vs_memory)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule_all compile_typed_word_abi_code >> strip_tac >>
  drule compile_abi_encode_static_code >> strip_tac >>
  drule_all_then (qspec_then `ctx` ASSUME_TAC) compile_abi_encode_static_path >>
  qabbrev_tac `raw_out = mstore (w2n (dst_addr:bytes32)) (mload (w2n (src_addr:bytes32)) ss)
    (update_var (STRING #"%" (toString cs.cs_next_var)) (mload (w2n src_addr) ss) ss)` >>
  `mload (w2n src_addr) ss = typed_val_to_w256 tv v` by
    (drule_all memory_value_rel_word >> simp[mem_word_at_eq_mload]) >>
  `memory_value_rel tv v (w2n dst_addr) raw_out.vs_memory` by
    (simp_tac bool_ss [Abbr`raw_out`, mstore_update_var] >> simp[update_var_def] >>
     mp_tac (Q.SPECL [`tenv`, `ty`, `tv`, `v`, `w2n (dst_addr:bytes32)`, `ss`]
       mstore_establishes_memory_value_rel_word) >> simp[]) >>
  `raw_out.vs_current_bb = cs'.cs_current_bb /\ raw_out.vs_halted = ss.vs_halted` by
    fs[Abbr`raw_out`, same_blocks_def, update_var_def] >>
  `copy_state_frame ss raw_out` by simp[Abbr`raw_out`] >>
  qexists_tac `raw_out with vs_inst_idx := LENGTH cs'.cs_current_insts` >>
  simp[eval_op_inst_idx] >> conj_tac
  >- simp[Abbr`raw_out`, eval_operand_mstore_eq, eval_operand_update_var_avoids] >>
  rpt gen_tac >> DISCH_TAC >>
  simp_tac bool_ss [Abbr`raw_out`, mstore_update_var] >> simp[update_var_def] >>
  irule mstore_preserves_memory_value_rel >> simp[]
QED
