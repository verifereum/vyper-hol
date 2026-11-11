Theory externalReturnSuffixResult
Ancestors
  externalReturnSuffixRun vyperLoweringCorrect loweringHalt exprLoweringProps
  e2eDefs vyperInterpreter vyperState

Theorem return_output_alloc_encoder_result_rel:
  compile_alloc_buffer msz st = (buf,mid) /\
  compile_abi_encode_to_buf buf.buf_operand src ei mid = (out,en) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\
  fn_inst_ids_distinct func /\ stmt_state_rel ctx func cenv cx es s /\
  local_ptrs_reserved cenv st /\ msz < dimword (:256) /\
  LENGTH (enc at av) <= msz /\ abi_encoder_admissible ei /\
  abi_encoder_window_input ei at av sb cap s.vs_memory /\
  eval_operand src s = SOME (n2w sb) /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  (0 < cap ==>
    (?aid b len. aid < st.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (b,len) /\
      b <= sb /\ sb + cap <= b + len) \/
    (?name b len. local_region cenv es.scopes s name b len /\
      b <= sb /\ sb + cap <= b + len)) /\
  emit_inst RETURN [buf.buf_operand;out] [] en = (x,sf) /\
  fn_has_code en sf func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  cx.sources = srcs /\ cx.layouts = layouts /\ cx.txn.target = tx.target /\
  ~lookup_raw_return_or_F (NONE:num option) tx.function_name External tops /\
  return_bytes tops ret v (enc at av) ==>
  ?fuel. external_call_result_rel tops ret tx
    (INL v, finalize_pending_deletions
       (abstract_machine_from_state srcs exps layouts es), es.requests)
    (run_from fuel ctx func s)
Proof
  strip_tac >> drule_all return_output_alloc_encoder_halt >> strip_tac >>
  qexists_tac `fuel` >> simp[external_call_result_rel_def, tx_return_bytes_def] >>
  fs[stmt_state_rel_def] >>
  drule_all external_halt_success >>
  disch_then (qspecl_then [`tops`, `exps`] mp_tac) >>
  simp[abstract_machine_from_state_def, finalize_pending_deletions_def]
QED
