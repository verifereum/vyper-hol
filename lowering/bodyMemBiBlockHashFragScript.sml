Theory bodyMemBiBlockHashFrag
Ancestors
  bodyMemBiBlockHashPath bodyUnopFragMemory exprSimBuiltins
  exprUnopSimDefs exprSimDefs exprSimProps varsExt loweringPosts fragExec
  builtinProps exprLoweringProps compileEnv
  vyperInterpreter vyperValue vyperValueOperation valueEncoding
  vyperContext vyperState vyperAST venomState venomExecSemantics
  exprSimSource exprSimMemorySource allocaHistory
  integer integer_word words list arithmeticProps freshWrites exprSimUnopProps
Libs
  intLib

Theorem compile_blockhash_frag_mem:
  !ctx func cenv cx i es0.
    0 <= i /\ i < 2 ** 256 ==>
    unop_frag_mem ctx func cenv cx compile_blockhash
      (typed_val_to_w256 (BaseTV (UintT 256)) (IntV i))
      (BaseT (BytesT (Fixed 32)))
      (unop_result cx (BaseT (BytesT (Fixed 32))) BlockHash
         [BaseT (UintT 256)] (IntV i) es0) es0
Proof
  rpt strip_tac >> simp[unop_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  `call_ctx_rel cx.txn s0.vs_call_ctx s0.vs_tx_ctx s0.vs_block_ctx` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `?n. i = &n` by metis_tac[integerTheory.NUM_POSINT_EXISTS] >>
  gvs[typed_val_to_w256_def, val_to_w256_def, integer_wordTheory.i2w_pos] >>
  `tx_env_ok cx.txn` by fs[call_ctx_rel_def] >>
  `fresh_vars_wrt sa (drop_fresh sa s0)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand x (drop_fresh sa s0) = SOME (n2w n)` by
    metis_tac[eval_operand_drop_fresh] >>
  `0 < cx.txn.block_number /\ cx.txn.block_number < 2 ** 255` by
    fs[tx_env_ok_def] >>
  `n < 2 ** 256` by simp[] >>
  drule_all blockhash_signed_window >> strip_tac >>
  `s0.vs_block_ctx.bc_number = n2w cx.txn.block_number` by
    fs[call_ctx_rel_def] >>
  `cx.txn.block_number < 2 ** 256` by fs[] >>
  `(drop_fresh sa s0).vs_block_ctx = s0.vs_block_ctx` by simp[drop_fresh_def] >>
  drule_all compile_blockhash_run >>
  `cx.txn.block_number MOD dimword (:256) = cx.txn.block_number` by
    fs[wordsTheory.dimword_def] >>
  simp[wordsTheory.w2n_n2w, GSYM wordsTheory.dimword_def] >>
  simp[unop_result_def, evaluate_builtin_def, tx_env_ok_evaluate_block_hash] >>
  Cases_on `n < cx.txn.block_number /\ cx.txn.block_number <= n + 256` >>
  simp[]
  >- suspend "success" >>
  suspend "revert"
QED

Resume compile_blockhash_frag_mem[success]:
  `cx.txn.block_number - 256 <= n` by decide_tac >>
  gvs[] >> strip_tac >>
  `s0.vs_block_ctx.bc_blockhash n =
     EL (cx.txn.block_number - (n + 1)) cx.txn.block_hashes` by
    (fs[call_ctx_rel_def] >> drule tx_env_ok_hash_window >>
     disch_then (qspec_then `n` mp_tac) >> gvs[] >> decide_tac) >>
  drule_all blockhash_clean_success_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all blockhash_run_post >> strip_tac >>
  `alloca_inv s0` by fs[stmt_state_rel_def] >>
  drule_all blockhash_run_history >> strip_tac >>
  qexists_tac `OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)` >>
  simp[] >>
  simp[expr_val_rel_def, typed_val_to_w256_def,
       vyperValueTheory.evaluate_type_def, is_word_type_def,
       PAD_RIGHT, length_word_to_bytes_be, word_of_bytes_be_to_bytes]
QED

Resume compile_blockhash_frag_mem[revert]:
  `n MOD dimword (:256) = n` by fs[wordsTheory.dimword_def] >>
  `~(cx.txn.block_number - 256 <= n /\ n < cx.txn.block_number)` by decide_tac >>
  gvs[] >> strip_tac >>
  drule_all blockhash_clean_abort_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `Abort Revert_abort (t with vs_inst_idx := j)` >>
  simp[exit_result_def, expr_exit_def]
QED

Finalise compile_blockhash_frag_mem
