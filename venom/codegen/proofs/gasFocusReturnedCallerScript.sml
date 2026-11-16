(* Actual child return and binding at the immutable saved caller state. *)
Theory gasFocusReturnedCaller
Ancestors
  gasFocusTerminalRow dftIndexedExec dftRunRel venomExecSemantics
  venomInst venomState list rich_list arithmetic

Theorem focus_returned_caller_terminal:
  !fuel C fn entry bb sp pre c postinsts last b0 nm ops child args ent ir
   child_out caller_post t r.
    lookup_block entry.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis entry bb.bb_instructions = OK sp /\
    bb.bb_instructions =
      TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++
      pre ++ [c] ++ postinsts ++ [last] /\
    EVERY (\i. ~is_terminator i.inst_opcode) pre /\
    EVERY (\i. ~is_terminator i.inst_opcode) postinsts /\
    FOLDR (dft_exec_cons fuel C) OK pre
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK b0 /\
    c.inst_opcode = INVOKE /\
    decode_invoke c = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME child /\
    eval_operands ops b0 = SOME args /\
    setup_callee child args b0 = SOME ent /\
    run_blocks fuel C child ent = IntRet ir child_out /\
    bind_outputs c.inst_outputs ir.iret_values
      (adopt_return_fmp ir (merge_callee_state b0 child_out)) = SOME caller_post /\
    FOLDR (dft_exec_cons fuel C) OK postinsts
      (caller_post with vs_inst_idx := SUC b0.vs_inst_idx) = OK t /\
    is_terminator last.inst_opcode /\
    step_inst fuel C last t = r /\
    (!u. r <> OK u)
    ==> run_blocks (SUC fuel) C fn entry = r
Proof
  rpt strip_tac >>
  `step_inst fuel C c b0 = OK caller_post` by
    simp[Once step_inst_def] >>
  `FOLDR (dft_exec_cons fuel C) OK (pre ++ [c] ++ postinsts)
     (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK t` by
    (rewrite_tac[FOLDR_APPEND] >>
     simp[Once dft_exec_prefix_continue] >>
     simp[dft_exec_cons_def, is_terminator_def]) >>
  irule focus_terminal_row_result >>
  conj_tac >- simp[] >>
  qexistsl [`bb`, `last`, `sp`, `t`, `pre ++ [c] ++ postinsts`] >>
  simp[EVERY_APPEND, is_terminator_def, APPEND_ASSOC]
QED
