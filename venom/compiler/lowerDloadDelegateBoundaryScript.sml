Theory lowerDloadDelegateBoundary
Ancestors
  lowerDloadSharedState venomExecSemantics

Theorem ld_delegatecall_state_exact:
  s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient /\
  s.vs_call_ctx = t.vs_call_ctx /\ s.vs_tx_ctx = t.vs_tx_ctx /\
  s.vs_block_ctx = t.vs_block_ctx /\ s.vs_prev_hashes = t.vs_prev_hashes ==>
  make_venom_delegatecall_state s target gas calldata code is_static =
  make_venom_delegatecall_state t target gas calldata code is_static
Proof
  simp[make_venom_delegatecall_state_def, venom_to_tx_params_def]
QED

Theorem ld_delegatecall_state_shared:
  ld_shared_state tn un s t /\ tn.t_stor = {} /\ tn.t_trans = {} ==>
  make_venom_delegatecall_state s target gas calldata code is_static =
  make_venom_delegatecall_state t target gas calldata code is_static
Proof
  strip_tac >> drule_all ld_shared_state_empty_exact >> strip_tac >>
  drule ld_shared_state_environment >> strip_tac >>
  irule ld_delegatecall_state_exact >> simp[]
QED

(* The actual concrete evaluation inputs used by exec_delegatecall. *)
Theorem ld_delegatecall_run_shared:
  ld_shared_state tn un s t /\ tn.t_stor = {} /\ tn.t_trans = {} /\
  read_memory ao az s = read_memory bo bz t ==>
  vfmExecution$run (make_venom_delegatecall_state s target gas
    (read_memory ao az s) (lookup_account target s.vs_accounts).code
    s.vs_call_ctx.cc_static) =
  vfmExecution$run (make_venom_delegatecall_state t target gas
    (read_memory bo bz t) (lookup_account target t.vs_accounts).code
    t.vs_call_ctx.cc_static)
Proof
  strip_tac >> drule_all ld_shared_state_empty_exact >> strip_tac >>
  drule ld_shared_state_environment >> strip_tac >>
  AP_TERM_TAC >> asm_rewrite_tac[] >>
  irule ld_delegatecall_state_exact >> simp[]
QED

(* Memory outputs may have unrelated offsets: this boundary covers only
   shared state.  The relocation consumer owns the memory-write relation. *)
Theorem ld_extract_result_shared:
  ld_shared_state tn un s t ==>
  OPTREL (\(v,s') (w,t'). v = w /\ ld_shared_state tn un s' t')
    (extract_venom_result s output ro rs result)
    (extract_venom_result t output to ts result)
Proof
  strip_tac >> Cases_on `result`
  >- simp[extract_venom_result_def] >>
  rename1 `SOME p` >> PairCases_on `p` >>
  simp[extract_venom_result_def] >>
  Cases_on `p1.contexts` >- simp[] >>
  rename1 `p1.contexts = h::rest` >>
  Cases_on `rest` >> simp[] >> PairCases_on `h` >>
  Cases_on `p0` >> simp[] >>
  gvs[lowerDloadSharedStateTheory.ld_shared_state_def] >>
  Cases_on `y` >>
  gvs[lowerDloadSharedStateTheory.ld_shared_state_def,
       ptrDisciplineTheory.storage_agree_except_def,
       ptrDisciplineTheory.word_agree_except_def]
QED
