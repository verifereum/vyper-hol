Theory entryCreateCheckedSum
Ancestors
  dallocaCreateBlueprint builtinCreate emitHelper emitHelperProps
  exprLoweringProps stmtReasonMemory loweringStateRelDefs
  venomInst venomState venomExecSemantics venomMemProps words arithmetic

(* The assertion tests the signed difference, not the sign of off. The
   framing equality carries that checked word to the actual append ADD. *)
Theorem blueprint_literal_checked_sum:
  compile_create_blueprint_check T target off ca = (code,cb) /\
  run_inst_seq (emitted_insts ca cb) s = OK t /\
  eval_operand code u = eval_operand code t /\
  eval_operand args_len u = SOME aw /\ w2n aw < 2 ** 64 /\
  emit_op ADD [code;args_len] sa = (size_op,sm) /\
  run_inst_seq (emitted_insts sa sm) u = OK pre ==>
  ?cw sz. eval_operand code u = SOME cw /\
          0 < w2n cw /\ w2n cw < 2 ** 255 /\
          eval_operand size_op pre = SOME sz /\
          w2n sz = w2n cw + w2n aw
Proof
  strip_tac >> drule_all create_blueprint_check_prefix >>
  disch_then (qx_choose_then `cw` strip_assume_tac) >>
  `eval_operand code u = SOME cw` by simp[] >>
  drule_then strip_assume_tac emitted_insts_emit_op >>
  `eval_operand size_op pre = SOME (cw + aw)` by
    (qpat_x_assum `run_inst_seq _ u = OK pre` mp_tac >>
     simp[run_inst_seq_def, step_add_eq] >>
     strip_tac >> gvs[eval_operand_def, lookup_var_update_var]) >>
  `2 ** 255 + 2 ** 64 < (2 ** 256 : num)` by EVAL_TAC >>
  `w2n cw + w2n aw < dimword (:256)` by
    (simp[dimword_def] >> (gvs[])) >>
  qexistsl_tac [`cw`, `cw + aw`] >>
  simp[word_add_def, w2n_n2w, LESS_MOD]
QED
