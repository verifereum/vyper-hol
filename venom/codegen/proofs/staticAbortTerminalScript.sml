(* Static storage and logging endpoints reject arbitrary concrete values. *)
Theory staticAbortTerminal
Ancestors
  staticAbortTrace asmSymSem asmSem asmIR stackOpSim list arithmetic

Theorem static_abort_terminal_dispatch:
  MEM name ["SSTORE"; "TSTORE"; "LOG0"; "LOG1"; "LOG2"; "LOG3"; "LOG4"] /\
  s.as_call_ctx.cc_static /\ asm_op_arity name <= LENGTH s.as_stack ==>
  asm_step lo o2pc (AsmOp name) s = AsmFault (s with as_returndata := [])
Proof
  simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `_ <= LENGTH _` mp_tac >>
  CONV_TAC (LAND_CONV (LAND_CONV EVAL)) >> strip_tac >>
  simp[asm_step_def, asm_step_op_def] >>
  simp[asm_step_arith_def] >> simp[asm_step_compare_def] >>
  simp[asm_step_bitwise_def] >> simp[asm_step_memory_def] >>
  simp[asm_step_control_def] >> simp[asm_step_extcall_def] >>
  simp[asm_step_copy_def] >> simp[asm_step_context_def] >>
  fs[quantHeuristicsTheory.LENGTH_TO_EXISTS_CONS] >>
  simp[dup_table_def, swap_table_def, log_table_def,
       asm_sstore_def, asm_tstore_def, asm_log_def]
QED

Theorem static_abort_terminal_step:
  MEM name ["SSTORE"; "TSTORE"; "LOG0"; "LOG1"; "LOG2"; "LOG3"; "LOG4"] /\
  s.as_call_ctx.cc_static /\ asm_op_arity name <= LENGTH s.as_stack /\
  asm_block_at prog s.as_pc [AsmOp name] ==>
  ?t. static_abort_exception lo o2pc prog 1 s t
Proof
  strip_tac >>
  `s.as_pc < LENGTH prog /\ EL s.as_pc prog = AsmOp name` by
    fs[asm_block_at_cons] >>
  `static_abort_safe_at prog s` by
    (simp[static_abort_safe_at_def] >>
     qpat_x_assum `MEM name _` mp_tac >> simp[] >> strip_tac >> gvs[] >> EVAL_TAC) >>
  `static_abort_trace lo o2pc prog 1 s` by
    simp[static_abort_trace_def, asm_steps_def] >>
  drule_all static_abort_terminal_dispatch >>
  disch_then (qspecl_then [`o2pc`, `lo`] assume_tac) >>
  qexists `s with as_returndata := []` >>
  simp[static_abort_exception_def] >>
  rewrite_tac[numLib.num_CONV ``1:num``] >> simp[asm_steps_def]
QED
