(* Actual raw runs, independent of the pointer certificates. *)
Theory bodyPtrEnvBuiltinsBlockHashSource
Ancestors builtinProps varsExt freshWrites exprLoweringProps compileEnv
  venomState venomExecSemantics words list

Theorem blockhash_run_old_operand:
  compile_blockhash arg sa = (op,sb) /\ eval_operand arg s = SOME n /\
  (!x. arg = Var x ==> not_fresh_at sa x) ==>
  if ~(word_lt n (s.vs_block_ctx.bc_number - 256w)) /\
     w2n n < w2n s.vs_block_ctx.bc_number then
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
        eval_operand op t = SOME (s.vs_block_ctx.bc_blockhash (w2n n))
  else ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
Proof
  strip_tac >>
  `eval_operand arg (drop_fresh sa s) = SOME n` by
    metis_tac[eval_operand_drop_fresh] >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  drule_all compile_blockhash_run >> simp[drop_fresh_def] >>
  drule compile_blockhash_shape >> strip_tac >>
  `vars_ext_result (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s))
    (run_inst_seq (emitted_insts sa sb) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >>
     fs[EVERY_MEM]) >>
  IF_CASES_TAC >> simp[] >> strip_tac >>
  gvs[vars_ext_result_def, drop_fresh_def] >>
  gvs[vars_ext_def] >> metis_tac[eval_operand_vars_ext, optionTheory.NOT_NONE_SOME]
QED
