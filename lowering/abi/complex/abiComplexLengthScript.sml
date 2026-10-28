(* TOP-LEVEL: the aggregate's actual final MLOAD returns its tail-counter
   value and preserves memory and every operand except the returned name. *)
Theory abiComplexLength
Ancestors
  compileEnv exprLoweringProps emitHelperProps ssaOperandFrame instIdxIndep
  fragExec fragBlockPath venomState venomExecSemantics venomInst list words

Theorem emit_abi_complex_length_path:
  !ctx func dyn_ptr cs op cs' ss dyn_addr.
    emit_op MLOAD [dyn_ptr] cs = (op,cs') /\
    fn_has_code cs cs' func /\ eval_operand dyn_ptr ss = SOME dyn_addr /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out.
      fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ out.vs_memory = ss.vs_memory /\
      eval_operand op out = SOME (mload (w2n dyn_addr) ss) /\
      out with vs_vars := ss.vs_vars = ss with vs_inst_idx := LENGTH cs'.cs_current_insts /\
      (!arg_op. arg_op <> op ==> eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  `step_inst_base (mk_inst cs.cs_next_id MLOAD [dyn_ptr]
      [STRING #"%" (toString cs.cs_next_var)]) ss =
    OK (update_var (STRING #"%" (toString cs.cs_next_var)) (mload (w2n dyn_addr) ss) ss)` by
    (irule step_MLOAD >> simp[]) >>
  `run_inst_seq (emitted_insts cs cs') ss =
    OK (update_var (STRING #"%" (toString cs.cs_next_var)) (mload (w2n dyn_addr) ss) ss)` by
    simp[run_inst_seq_def] >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs`, `cs'`, `ss`,
    `update_var (STRING #"%" (toString cs.cs_next_var)) (mload (w2n (dyn_addr:bytes32)) ss) ss`]
    fragment_path_emitted) >>
  impl_tac >- simp[same_blocks_def, mk_inst_def, is_terminator_def] >> DISCH_TAC >>
  qexists_tac `(update_var (STRING #"%" (toString cs.cs_next_var)) (mload (w2n dyn_addr) ss) ss)
    with vs_inst_idx := LENGTH cs'.cs_current_insts` >>
  simp[eval_op_inst_idx, eval_operand_update_var, eval_operand_update_var_avoids,
    update_var_reset_vars] >> simp[update_var_def, venom_state_component_equality] >> fs[same_blocks_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed aggregate ABI returned-length load: " ^ name)
  end) (DB.thms "abiComplexLength")
