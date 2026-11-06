(* Compiler boundary for the branchless, ASSERT-checked Abs suffix. *)
Theory bodyPtrWordBuiltinsAbsSuffix
Ancestors builtinSimple exprLowering exprLoweringProps compileEnv emitHelper
  venomInst list rich_list fragExec

Theorem word_abs_current_block:
  compile_builtin_abs x sa = (op,sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb
Proof
  simp[compile_builtin_abs_def, compile_select_def, comp_bind_def,
       comp_ignore_bind_def, emit_op_def, emit_void_def, fresh_id_def,
       fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[emitted_insts_def] >> simp[DROP_LENGTH_APPEND]
QED

Theorem word_abs_emitted_opcodes:
  compile_builtin_abs x sa = (op,sb) ==>
  MAP (\i. i.inst_opcode) (emitted_insts sa sb) =
    [SUB; SLT; EQ; AND; ISZERO; ASSERT; XOR; MUL; XOR]
Proof
  simp[compile_builtin_abs_def, compile_select_def, comp_bind_def,
       comp_ignore_bind_def, emit_op_def, emit_void_def, fresh_id_def,
       fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem word_abs_code_prefix:
  compile_builtin_abs x sa = (op,sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)
Proof
  strip_tac >> drule word_abs_current_block >> strip_tac >>
  gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]
QED
