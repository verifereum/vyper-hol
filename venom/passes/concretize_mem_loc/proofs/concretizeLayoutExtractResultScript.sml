Theory concretizeLayoutExtractResult
Ancestors venomExecSemantics venomState list

Theorem concretize_extract_exists:
  extract_venom_result s output ro rs result = SOME (w,post) ==>
  ?tpost. extract_venom_result t output roT rs result = SOME (w,tpost)
Proof
  simp[extract_venom_result_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> pairarg_tac >> gvs[] >>
  Cases_on `result'` >> gvs[] >> Cases_on `y` >> gvs[]
QED

Theorem concretize_extract_observables:
  extract_venom_result s output ro rs result = SOME (w,post) /\
  extract_venom_result t output roT rs result = SOME (z,tpost) /\
  s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient /\
  s.vs_logs = t.vs_logs /\ s.vs_pending_deletions = t.vs_pending_deletions ==>
  w = z /\ post.vs_returndata = tpost.vs_returndata /\
  post.vs_accounts = tpost.vs_accounts /\
  post.vs_transient = tpost.vs_transient /\
  post.vs_logs = tpost.vs_logs /\
  post.vs_pending_deletions = tpost.vs_pending_deletions
Proof
  simp[extract_venom_result_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> Cases_on `result'` >> gvs[] >> Cases_on `y` >> gvs[]
QED

(* The complete unchanged-state envelope, without a memory equation:
   the existing extract_venom_result_memory owns that equation. *)
Theorem concretize_extract_unchanged:
  extract_venom_result s output ro rs result = SOME (w,post) ==>
  post.vs_call_ctx = s.vs_call_ctx /\
  post.vs_tx_ctx = s.vs_tx_ctx /\ post.vs_block_ctx = s.vs_block_ctx /\
  post.vs_prev_hashes = s.vs_prev_hashes /\
  post.vs_requests = s.vs_requests /\ post.vs_outcomes = s.vs_outcomes /\
  post.vs_vars = s.vs_vars /\ post.vs_allocas = s.vs_allocas /\
  post.vs_fmp = s.vs_fmp /\ post.vs_initial_fmp = s.vs_initial_fmp /\
  post.vs_labels = s.vs_labels /\ post.vs_gas_readings = s.vs_gas_readings /\
  post.vs_immutables = s.vs_immutables /\ post.vs_halted = s.vs_halted /\
  post.vs_code = s.vs_code /\ post.vs_data_section = s.vs_data_section /\
  post.vs_inst_idx = s.vs_inst_idx /\ post.vs_current_bb = s.vs_current_bb /\
  post.vs_prev_bb = s.vs_prev_bb
Proof
  simp[extract_venom_result_def, AllCaseEqs()] >> rpt strip_tac >>
  pairarg_tac >> gvs[]
QED
