Theory targetPureWalkRuntimeWitness
Ancestors
  targetPureWalkWitness exprLoweringProps

(* The concrete transaction has a valid one-block hash window. *)
Theorem w_tx_env_ok:
  tx_env_ok w_cx.txn
Proof
  EVAL_TAC
QED

(* All call, transaction and block fields match, including BLOCKHASH. *)
Theorem w_call_ctx_rel:
  call_ctx_rel w_cx.txn w_s0.vs_call_ctx w_s0.vs_tx_ctx w_s0.vs_block_ctx
Proof
  simp[loweringStateRelDefsTheory.call_ctx_rel_def, w_tx_env_ok,
       w_cx_def, w_s0_def,
       vyperContextTheory.empty_evaluation_context_def,
       vyperContextTheory.empty_call_txn_def,
       venomStateTheory.init_venom_state_def,
       venomStateTheory.empty_call_context_def,
       venomStateTheory.empty_tx_context_def,
       venomStateTheory.empty_block_context_def] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[] >> gvs[]
QED

Theorem w_state_rel[local]:
  state_rel w_func w_cenv w_cx w_es w_s0
Proof
  rewrite_tac[loweringStateRelDefsTheory.state_rel_def] >>
  rpt conj_tac >> EVAL_TAC >>
  simp[wordsTheory.dimword_def, venomLayoutTheory.dimindex_256,
       valueEncodingTheory.type_memory_size_def,
       valueEncodingDefsTheory.val_wf_def,
       memoryValueDefsTheory.memory_value_rel_def] >>
  CONV_TAC (wordsLib.WORD_EVAL_CONV) >> EVAL_TAC >>
  simp[wordsTheory.dimword_def, venomLayoutTheory.dimindex_256]
QED

Theorem w_alloca_inv[local]:
  alloca_inv w_s0
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, venomLayoutTheory.dimindex_256]
QED

Theorem w_immutable_sep[local]:
  immutable_alloca_sep w_func w_cenv w_cx w_es w_s0 /\
  immutable_base_zero w_cenv w_s0
Proof
  EVAL_TAC >> simp[]
QED

Theorem w_no_direct_calls[local]:
  !g. ~fn_directly_calls w_ctx "walk" g
Proof
  gen_tac >> rewrite_tac[fcgDefsTheory.fn_directly_calls_def] >>
  EVAL_TAC >> simp[venomInstTheory.fn_insts_blocks_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem w_no_calls[local]:
  !g. ~TC (fn_directly_calls w_ctx) "walk" g
Proof
  simp[Once relationTheory.TC_CASES1, w_no_direct_calls]
QED

Theorem w_alloca_room[local]:
  alloca_room w_ctx w_func w_s0
Proof
  rewrite_tac[alloca_room_def] >>
  `w_func.fn_name = "walk"` by EVAL_TAC >>
  simp[w_no_calls] >> EVAL_TAC >>
  simp[wordsTheory.dimword_def, venomLayoutTheory.dimindex_256]
QED

Theorem w_fmp_room[local]:
  fmp_room w_ctx w_func w_s0
Proof
  rewrite_tac[fmp_room_def] >>
  `w_func.fn_name = "walk"` by EVAL_TAC >>
  simp[w_no_calls] >> EVAL_TAC >>
  simp[venomInstTheory.fn_insts_blocks_def]
QED

Theorem raw_log_witness_entry:
  stmt_state_rel w_ctx w_func w_cenv w_cx w_es w_s0
Proof
  simp[stmt_state_rel_def, w_state_rel, w_alloca_inv, w_alloca_room,
       w_fmp_room, w_immutable_sep, w_entry_fields]
QED
