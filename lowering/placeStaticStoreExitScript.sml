Theory placeStaticStoreExit
Ancestors
  stmtSimDefs exprSimDefs fragExec fragGasSeqAbort loweringPosts venomInst venomState
  emitHelperProps loweringHalt
  venomExecSemantics list rich_list

Theorem place_static_store_prefix_exit:
  s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id (if tr then TSTORE else SSTORE) [dst;op] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  eval_operand dst s = SOME slot /\ eval_operand op s = SOME w ==>
  ?r. gas_marked_path F ctx func s 0 r /\ exit_result r /\
      stmt_exit RetQ ee (INR (Error (RuntimeError "write in static context"))) r
Proof
  strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  `step_inst_base (mk_inst id SSTORE [dst;op] []) s =
     Abort ExHalt_abort (halt_state (set_returndata [] s))` by
    metis_tac[step_SSTORE] >>
  `step_inst_base (mk_inst id TSTORE [dst;op] []) s =
     Abort ExHalt_abort (halt_state (set_returndata [] s))` by
    metis_tac[step_TSTORE] >>
  qexists_tac `Abort ExHalt_abort (halt_state (set_returndata [] s))` >>
  simp[stmt_exit_def, expr_exit_def, exit_result_def] >>
  `gas_marked_path F ctx func s
     (if (mk_inst id (if tr then TSTORE else SSTORE) [dst;op] []).inst_opcode = GAS then 1 else 0)
     (Abort ExHalt_abort (halt_state (set_returndata [] s)))` by
    (irule gas_marked_path_abort >>
     Cases_on `tr` >>
     gvs[mk_inst_def, is_terminator_def]) >>
  Cases_on `tr` >> gvs[mk_inst_def]
QED
