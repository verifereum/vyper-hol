(* Joint finite-horizon simulation of Abs. *)
Theory bodyFullBuiltinWordAbs
Ancestors
  bodyFullPreds bodySimFull bodyFullGhostFrame gasOutcomeFullCompose
  exprSimWordBuiltins exprSimUnopProps fragGasSeqPtr builtinProps
  fragExecMem instMemFrontier memSafeRun
  builtinSimple emitHelper emitHelperProps freshWrites
  exprLoweringProps exprLowering compileEnv venomInst list rich_list

val _ = Parse.hide "body";

Theorem abs_suffix_opcodes:
  !x sa op sb.
    compile_builtin_abs x sa = (op,sb) ==>
    MAP (\i. i.inst_opcode) (emitted_insts sa sb) =
      [SUB; SLT; EQ; AND; ISZERO; ASSERT; XOR; MUL; XOR]
Proof
  rpt gen_tac >>
  simp[compile_builtin_abs_def, compile_select_def, comp_bind_def,
       comp_ignore_bind_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def, mk_inst_def,
       emitted_insts_def] >>
  rpt strip_tac >> gvs[rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem abs_suffix_mem_ok:
  !x sa op sb s.
    compile_builtin_abs x sa = (op,sb) ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt strip_tac >> drule abs_suffix_opcodes >> strip_tac >>
  irule run_inst_seq_mem_ok_every >>
  `EVERY (\opc. MEM opc [SUB; SLT; EQ; AND; ISZERO; ASSERT; XOR; MUL])
     (MAP (\i. i.inst_opcode) (emitted_insts sa sb))` by simp[] >>
  gvs[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[below_frontier_no_ranges, inst_dload_in_section_other]
QED
