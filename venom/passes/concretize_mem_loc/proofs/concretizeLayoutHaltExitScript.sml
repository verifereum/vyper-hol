Theory concretizeLayoutHaltExit
Ancestors concretizeLayoutSupplement ptrDiscipline pred_set

Theorem concretize_supplement_halt_exit:
  taint_within D C vs0 /\ final_taint vs0 C s tn R /\
  concretize_supplement D tn s t /\
  s.vs_halted = t.vs_halted /\ s.vs_logs = t.vs_logs /\
  s.vs_pending_deletions = t.vs_pending_deletions /\
  LENGTH s.vs_returndata = LENGTH t.vs_returndata /\
  (!i. i < LENGTH s.vs_returndata /\ i NOTIN R ==>
       EL i s.vs_returndata = EL i t.vs_returndata) ==>
  dead_result_rel D (Halt s) (Halt t)
Proof
  strip_tac >>
  qpat_x_assum `taint_within _ _ _` mp_tac >>
  pure_rewrite_tac[taint_within_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
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
