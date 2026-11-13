Theory lowerDloadSharedState
Ancestors
  ptrDiscipline venomState finite_map pred_set

(* Shared observable inputs, excluding histories, control, and relocated memory.
   Source taint masks govern agreement; target masks may only shrink. *)
Definition ld_shared_state_def:
  ld_shared_state tn un s t <=>
    s.vs_call_ctx = t.vs_call_ctx /\
    s.vs_tx_ctx = t.vs_tx_ctx /\ s.vs_block_ctx = t.vs_block_ctx /\
    s.vs_prev_hashes = t.vs_prev_hashes /\
    s.vs_code = t.vs_code /\ s.vs_data_section = t.vs_data_section /\
    s.vs_outcomes = t.vs_outcomes /\ s.vs_returndata = t.vs_returndata /\
    s.vs_fmp = t.vs_fmp /\ s.vs_call_entry_fmp = t.vs_call_entry_fmp /\
    s.vs_initial_fmp = t.vs_initial_fmp /\
    (!a. (s.vs_accounts a with storage := (t.vs_accounts a).storage) =
          t.vs_accounts a) /\
    (!a. storage_agree_except tn.t_stor
          (s.vs_accounts a).storage (t.vs_accounts a).storage) /\
    (!a. storage_agree_except tn.t_trans (s.vs_transient a) (t.vs_transient a)) /\
    FDOM s.vs_immutables = FDOM t.vs_immutables /\
    (!q. q IN FDOM s.vs_immutables ==>
      word_agree_except {b | (q,b) IN tn.t_imm}
        (s.vs_immutables ' q) (t.vs_immutables ' q)) /\
    un.t_stor SUBSET tn.t_stor /\ un.t_trans SUBSET tn.t_trans /\
    un.t_imm SUBSET tn.t_imm
End

Theorem ld_shared_state_identity:
  ld_shared_state tn tn s s
Proof
  simp[ld_shared_state_def, storage_agree_except_def, word_agree_except_def]
QED

Theorem ld_shared_state_masks:
  ld_shared_state tn un s t ==>
  un.t_stor SUBSET tn.t_stor /\ un.t_trans SUBSET tn.t_trans /\
  un.t_imm SUBSET tn.t_imm
Proof
  simp[ld_shared_state_def]
QED

Theorem ld_shared_state_storage:
  ld_shared_state tn un s t ==>
  !a. storage_agree_except tn.t_stor
    (s.vs_accounts a).storage (t.vs_accounts a).storage
Proof
  simp[ld_shared_state_def]
QED

Theorem ld_shared_state_transient:
  ld_shared_state tn un s t ==>
  !a. storage_agree_except tn.t_trans (s.vs_transient a) (t.vs_transient a)
Proof
  simp[ld_shared_state_def]
QED

Theorem ld_shared_state_empty_exact:
  ld_shared_state tn un s t /\ tn.t_stor = {} /\ tn.t_trans = {} ==>
  s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient /\
  un.t_stor = {} /\ un.t_trans = {}
Proof
  `dimindex (:256) = 256` by CONV_TAC fcpLib.INDEX_CONV >>
  strip_tac >> gvs[ld_shared_state_def] >>
  `!a. (s.vs_accounts a).storage = (t.vs_accounts a).storage` by
    (gvs[storage_agree_except_def, key_taint_def, word_agree_except_bits,
         FUN_EQ_THM, fcpTheory.CART_EQ, wordsTheory.dimword_def] >>
     metis_tac[]) >>
  conj_tac
  >- (simp[FUN_EQ_THM] >> qx_gen_tac `a` >>
      qpat_x_assum `!a. _ with storage := _ = _`
        (qspec_then `a` mp_tac) >>
      simp[vfmStateTheory.account_state_component_equality] ) >>
  gvs[storage_agree_except_def, key_taint_def, word_agree_except_bits,
      FUN_EQ_THM, fcpTheory.CART_EQ] >> metis_tac[]
QED

Theorem ld_shared_state_environment:
  ld_shared_state tn un s t ==>
  s.vs_call_ctx = t.vs_call_ctx /\
  s.vs_tx_ctx = t.vs_tx_ctx /\ s.vs_block_ctx = t.vs_block_ctx /\
  s.vs_prev_hashes = t.vs_prev_hashes /\
  s.vs_code = t.vs_code /\ s.vs_data_section = t.vs_data_section /\
  s.vs_outcomes = t.vs_outcomes /\ s.vs_returndata = t.vs_returndata /\
  s.vs_fmp = t.vs_fmp /\ s.vs_call_entry_fmp = t.vs_call_entry_fmp /\
  s.vs_initial_fmp = t.vs_initial_fmp
Proof
  simp[ld_shared_state_def]
QED

Theorem ld_shared_state_nonstorage:
  ld_shared_state tn un s t ==>
  !a. (s.vs_accounts a with storage := (t.vs_accounts a).storage) = t.vs_accounts a
Proof
  simp[ld_shared_state_def]
QED

Theorem ld_shared_state_immutables:
  ld_shared_state tn un s t ==>
  FDOM s.vs_immutables = FDOM t.vs_immutables /\
  (!q. q IN FDOM s.vs_immutables ==>
    word_agree_except {b | (q,b) IN tn.t_imm}
      (s.vs_immutables ' q) (t.vs_immutables ' q))
Proof
  simp[ld_shared_state_def]
QED
