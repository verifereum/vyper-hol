Theory concretizeLayoutHaltExit
Ancestors concretizeLayoutSupplement ptrDiscipline pred_set

Theorem concretize_supplement_halt_exit:
  tn.t_stor SUBSET
    D.d_stor s.vs_call_ctx.cc_address
      (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET
    D.d_trans s.vs_call_ctx.cc_address
      (s.vs_transient s.vs_call_ctx.cc_address) /\
  tn.t_imm SUBSET D.d_imm s.vs_immutables /\ R SUBSET D.d_ret s.vs_returndata /\
  concretize_supplement D tn s t /\
  s.vs_halted = t.vs_halted /\ s.vs_logs = t.vs_logs /\
  s.vs_pending_deletions = t.vs_pending_deletions /\
  LENGTH s.vs_returndata = LENGTH t.vs_returndata /\
  (!i. i < LENGTH s.vs_returndata /\ i NOTIN R ==>
       EL i s.vs_returndata = EL i t.vs_returndata) ==>
  dead_result_rel D (Halt s) (Halt t)
Proof
  strip_tac >>
  gvs[concretize_supplement_def, dead_result_rel_def] >>
  rpt conj_tac
  >- (gvs[accounts_agree_except_def] >> gen_tac >>
      first_x_assum (qspec_then `a` strip_assume_tac) >> simp[] >>
      gvs[storage_agree_except_def, word_agree_except_def, key_taint_def,
          SUBSET_DEF] >>
      Cases_on `a = s.vs_call_ctx.cc_address` >> gvs[] >> metis_tac[])
  >- (gvs[transient_agree_except_def, storage_agree_except_def,
          word_agree_except_def, key_taint_def, SUBSET_DEF] >>
      gen_tac >> Cases_on `a = s.vs_call_ctx.cc_address` >> gvs[] >> metis_tac[])
  >- (gvs[imms_agree_except_def, word_agree_except_def, SUBSET_DEF] >>
      metis_tac[])
  >> gvs[SUBSET_DEF] >> metis_tac[]
QED
