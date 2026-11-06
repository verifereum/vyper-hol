(* TOP-LEVEL: the explicit Log field-address ADD executes at an open compiler
   cut and preserves typed arguments outside its one written temporary.
   Repeated writes to that temporary are allowed. *)
Theory fieldAddressProps
Ancestors
  typedCopyStateFrame fieldStoreComposition compileEnv exprLoweringProps emitHelper emitHelperProps
  fragExec fragBlockPath instIdxIndep ssaOperandFrame valueLoadProps
  venomState venomExecSemantics venomInst list words

Theorem emit_field_address_code:
  !buf offset cs dst cs'.
    emit_op ADD [buf; Lit (n2w offset)] cs = (dst,cs') ==>
    dst = Var (STRING #"%" (toString cs.cs_next_var)) /\
    same_blocks cs cs' /\ cs'.cs_next_var = cs.cs_next_var + 1 /\
    emitted_insts cs cs' =
      [mk_inst cs.cs_next_id ADD [buf; Lit (n2w offset)]
        [STRING #"%" (toString cs.cs_next_var)]] /\
    cs'.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs cs'
Proof
  rpt gen_tac >> DISCH_TAC >> drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> simp[same_blocks_def]
QED

Theorem emit_field_address_path:
  !ctx func buf offset cs dst cs' ss addr.
    emit_op ADD [buf; Lit (n2w offset)] cs = (dst,cs') /\
    eval_operand buf ss = SOME addr /\ fn_has_code cs cs' func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ out.vs_memory = ss.vs_memory /\ copy_state_frame ss out /\
      eval_operand dst out = SOME (addr + n2w offset) /\
      (!arg_op. arg_op <> dst ==> eval_operand arg_op out = eval_operand arg_op ss) /\
      (!ty tv v arg_op. lowered_value_rel ty tv v arg_op ss /\ arg_op <> dst ==>
        lowered_value_rel ty tv v arg_op out)
Proof
  rpt gen_tac >> strip_tac >> drule emit_field_address_code >> strip_tac >>
  `step_inst_base (mk_inst cs.cs_next_id ADD [buf; Lit (n2w offset)]
      [STRING #"%" (toString cs.cs_next_var)]) ss =
    OK (update_var (STRING #"%" (toString cs.cs_next_var)) (addr + n2w offset) ss)` by
    (irule step_ADD >> simp[eval_operand_lit]) >>
  `run_inst_seq (emitted_insts cs cs') ss =
    OK (update_var (STRING #"%" (toString cs.cs_next_var)) (addr + n2w offset) ss)` by
    simp[run_inst_seq_def] >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs`, `cs'`, `ss`,
    `update_var (STRING #"%" (toString cs.cs_next_var)) (addr + n2w offset) ss`]
    fragment_path_emitted) >>
  impl_tac >- simp[mk_inst_def, is_terminator_def] >> strip_tac >>
  qexists_tac `(update_var (STRING #"%" (toString cs.cs_next_var)) (addr + n2w offset) ss)
    with vs_inst_idx := LENGTH cs'.cs_current_insts` >>
  `!name word. (update_var name word ss).vs_memory = ss.vs_memory /\
    (update_var name word ss).vs_halted = ss.vs_halted` by simp[update_var_def] >>
  simp[eval_op_inst_idx, eval_operand_update_var,
    eval_operand_update_var_avoids] >>
  rpt gen_tac >> strip_tac >> irule lowered_value_rel_frame >>
  qexists_tac `ss` >> simp[] >>
  simp[eval_op_inst_idx, eval_operand_update_var_avoids]
QED
