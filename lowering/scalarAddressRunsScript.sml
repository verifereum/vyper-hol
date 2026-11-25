(* Raw instruction-list observations for emitted scalar address arithmetic. *)
Theory scalarAddressRuns
Ancestors
  emitHelperProps exprLoweringProps storageCopyBodyPtr venomExecSemantics
  venomInst venomState words list

Theorem emitted_scalar_binop_code:
  (opc = ADD \/ opc = MUL) /\ emit_op opc [left;right] sa = (Var out,sb) ==>
  emitted_insts sa sb = [mk_inst sa.cs_next_id opc [left;right] [out]] /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  gvs[mk_inst_def, is_terminator_def]
QED

Theorem emitted_scalar_binop_run:
  (opc = ADD /\ w = a + b \/ opc = MUL /\ w = a * b) /\
  emit_op opc [left;right] sa = (Var out,sb) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  t = (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
      t = (u with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule emitted_insts_emit_op >> strip_tac >>
  qexists `update_var out w s` >>
  qpat_x_assum `opc = ADD /\ _ \/ opc = MUL /\ _` strip_assume_tac >>
  gvs[run_inst_seq_def, arithmeticTheory.ADD1] >>
  simp_tac std_ss [Once step_inst_base_def, mk_inst_def,
    instruction_accessors, instruction_accfupds, opcode_case_def] >>
  simp[exec_pure2_def]
QED

Theorem emitted_address_run_append:
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  sc.cs_current_insts = sb.cs_current_insts ++ emitted_insts sb sc /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sb sc) /\
  (?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
       t = (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  (?v. run_inst_seq (emitted_insts sb sc) t = OK v /\
       t' = (v with vs_inst_idx := LENGTH sc.cs_current_insts)) ==>
  ?w. run_inst_seq (emitted_insts sa sc) s = OK w /\
      t' = (w with vs_inst_idx := LENGTH sc.cs_current_insts)
Proof
  strip_tac >>
  `emitted_insts sa sc = emitted_insts sa sb ++ emitted_insts sb sc` by
    metis_tac[emitted_insts_append] >>
  asm_rewrite_tac[] >> irule run_inst_seq_cursor_append >> metis_tac[]
QED
