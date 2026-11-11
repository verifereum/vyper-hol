(* Actual raw runs, independent of the pointer certificates. *)
Theory bodyPtrEnvBuiltinsBlockHashSource
Ancestors builtinProps varsExt freshWrites exprLoweringProps compileEnv loweringStateRelDefs
  venomState venomExecSemantics words list arithmeticProps exprSimUnopProps
  exprSimDefs loweringPosts valueEncoding vyperValue vyperValueOperation
  vyperContext vyperState vyperAST vyperInterpreter integer integer_word
  vyperTyping

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

Theorem blockhash_source_raw_outcome:
  0 <= i /\ i < 2 ** 256 /\ stmt_state_rel ctx fn cenv cx ee s /\
  compile_blockhash arg sm = (op,sb) /\
  (!x. arg = Var x ==> not_fresh_at sm x) /\
  eval_operand arg s = SOME (typed_val_to_w256 (BaseTV (UintT 256)) (IntV i)) ==>
  (?u v. run_inst_seq (emitted_insts sm sb) s = OK u /\
     eval_operand op u = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) v) /\
     unop_result cx (BaseT (BytesT (Fixed 32))) BlockHash
       [BaseT (UintT 256)] (IntV i) ee = INL v /\
     expr_val_rel cx (BaseT (BytesT (Fixed 32))) v op u) \/
  (?u. run_inst_seq (emitted_insts sm sb) s = Abort Revert_abort u /\
     expr_exit (unop_result cx (BaseT (BytesT (Fixed 32))) BlockHash
       [BaseT (UintT 256)] (IntV i) ee) (Abort Revert_abort u))
Proof
  strip_tac >>
  `call_ctx_rel cx.txn s.vs_call_ctx s.vs_tx_ctx s.vs_block_ctx` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `?n. i = &n` by metis_tac[integerTheory.NUM_POSINT_EXISTS] >>
  gvs[typed_val_to_w256_def, val_to_w256_def, integer_wordTheory.i2w_pos] >>
  `tx_env_ok cx.txn` by fs[call_ctx_rel_def] >>
  `0 < cx.txn.block_number /\ cx.txn.block_number < 2 ** 255` by
    fs[tx_env_ok_def] >>
  `n < 2 ** 256` by simp[] >>
  drule_all blockhash_signed_window >> strip_tac >>
  `s.vs_block_ctx.bc_number = n2w cx.txn.block_number` by fs[call_ctx_rel_def] >>
  `cx.txn.block_number < 2 ** 256` by fs[] >>
  drule_all blockhash_run_old_operand >>
  `cx.txn.block_number MOD dimword (:256) = cx.txn.block_number` by
    fs[wordsTheory.dimword_def] >>
  simp[wordsTheory.w2n_n2w, GSYM wordsTheory.dimword_def] >>
  simp[unop_result_def, evaluate_builtin_def, tx_env_ok_evaluate_block_hash] >>
  Cases_on `n < cx.txn.block_number /\ cx.txn.block_number <= n + 256` >> simp[]
  >- suspend "success" >> suspend "revert"
QED

Resume blockhash_source_raw_outcome[success]:
  `cx.txn.block_number - 256 <= n` by decide_tac >>
  gvs[] >> strip_tac >>
  `s.vs_block_ctx.bc_blockhash n =
     EL (cx.txn.block_number - (n + 1)) cx.txn.block_hashes` by
    (fs[call_ctx_rel_def] >> drule tx_env_ok_hash_window >>
     disch_then (qspec_then `n` mp_tac) >> gvs[] >> decide_tac) >>
  qexists_tac `t` >>
  simp[expr_val_rel_def, typed_val_to_w256_def, val_to_w256_def,
       evaluate_type_def, is_word_type_def, PAD_RIGHT,
       length_word_to_bytes_be, word_of_bytes_be_to_bytes] >>
  gvs[]
QED
Resume blockhash_source_raw_outcome[revert]:
  `n MOD dimword (:256) = n` by fs[wordsTheory.dimword_def] >>
  `~(cx.txn.block_number - 256 <= n /\ n < cx.txn.block_number)` by decide_tac >>
  gvs[] >> strip_tac >>
  qexists_tac `t` >> simp[expr_exit_def]
QED
Finalise blockhash_source_raw_outcome
