(* Total operand frame for the finite dynamic element pointer fragment. *)
Theory abiDecodeMemElementFrame
Ancestors
  entryDecoderSetupEndpoint abiDecodeMemElementPointer abiDecoderReentry abiEncoder
  compileEnv emitHelper emitHelperProps exprLoweringProps loweringStateRelDefs
  venomState venomInst list rich_list arithmetic pred_set

Theorem abi_decode_element_outputs[local]:
  compile_abi_decode_dyn_elem_ptr MLOAD bop src data hi sz st = (ptr_op,st') /\
  abi_decoder_older_vars st.cs_next_var x ==>
  EVERY (\i. ~MEM x i.inst_outputs) (emitted_insts st st')
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_decode_dyn_elem_ptr _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `hi = Lit 0w` >> Cases_on `bop = Lit 0w` >>
  simp[compile_abi_decode_dyn_elem_ptr_def, compile_abi_dec_addr_def,
    compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
    emit_def] >> strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp_tac bool_ss [DROP_LENGTH_APPEND, APPEND, EVERY_DEF, mk_inst_def, MEM] >>
  fs[abi_decoder_older_vars_def]
QED

Theorem abi_decode_element_total_frame:
  compile_abi_decode_dyn_elem_ptr MLOAD bop src data hi sz st = (ptr_op,st') /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  !op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s
Proof
  strip_tac >> drule abi_decode_element_shape >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st st')` by fs[EVERY_MEM] >>
  drule_all entry_sequence_nonterminator_labels >> strip_tac >>
  Cases >> simp[abi_decoder_operand_live_def, eval_operand_def] >> strip_tac >>
  irule entry_sequence_nonoutput_lookup >> goal_assum (drule_at Any) >>
  qpat_x_assum `_ IN abi_decoder_older_vars _`
    (assume_tac o REWRITE_RULE [IN_APP]) >>
  drule_all abi_decode_element_outputs >> strip_tac >> fs[EVERY_MEM]
QED
