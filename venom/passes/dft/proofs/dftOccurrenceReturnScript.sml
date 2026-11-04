(* Caller restoration is independent of the duration of a callee run. *)
Theory dftOccurrenceReturn
Ancestors
  dftOccurrenceReceipt dftOccurrenceResidual dftCommutation
  venomExecSemantics venomState list option

Definition dft_restore_def:
  dft_restore outs ret cs s = bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s cs))
End

Theorem dft_restore_update:
  ~MEM v outs ==>
  dft_restore outs ret cs (update_var v x s) =
  OPTION_MAP (update_var v x) (dft_restore outs ret cs s)
Proof
  strip_tac >>
  `adopt_return_fmp ret (merge_callee_state (update_var v x s) cs) =
   update_var v x (adopt_return_fmp ret (merge_callee_state s cs))` by
    (Cases_on `ret.iret_adopt_fmp` >>
     simp[adopt_return_fmp_def, merge_callee_state_def, update_var_def]) >>
  simp[dft_restore_def, bind_outputs_update_var]
QED

Theorem dft_restore_pending:
  !us s. EVERY (\p. ~MEM (FST p) outs) us ==>
  dft_restore outs ret cs (dft_pending_apply us s) =
  OPTION_MAP (dft_pending_apply us) (dft_restore outs ret cs s)
Proof
  Induct
  >- (gen_tac >> Cases_on `dft_restore outs ret cs s` >>
      simp[dft_pending_apply_def]) >>
  simp[dft_pending_apply_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `update_var (FST h) (SND h) s` mp_tac) >>
  simp[dft_pending_apply_def, dft_restore_update] >>
  Cases_on `dft_restore outs ret cs s` >> simp[dft_pending_apply_def]
QED

Theorem dft_restore_cut_data:
  dft_restore outs ret cs (dft_cut_data s) =
  OPTION_MAP dft_cut_data (dft_restore outs ret cs s)
Proof
  `adopt_return_fmp ret (merge_callee_state (dft_cut_data s) cs) =
   dft_cut_data (adopt_return_fmp ret (merge_callee_state s cs))` by
    (Cases_on `ret.iret_adopt_fmp` >>
     simp[adopt_return_fmp_def, merge_callee_state_def, dft_cut_data_def]) >>
  simp[dft_restore_def, bind_outputs_def] >>
  IF_CASES_TAC >> simp[] >>
  ` (\u (v,x). update_var v x u) =
    (\u p. update_var (FST p) (SND p) u)` by
    (simp[FUN_EQ_THM, pairTheory.FORALL_PROD]) >>
  asm_rewrite_tac[] >>
  rewrite_tac[GSYM dft_pending_apply_def, dft_cut_data_pending]
QED

Theorem dft_restore_failure:
  dft_restore outs ret cs s = NONE <=> LENGTH outs <> LENGTH ret.iret_values
Proof
  simp[dft_restore_def, bind_outputs_def] >> IF_CASES_TAC >> simp[]
QED

Theorem dft_restore_pair_failure:
  (dft_restore outs ret cs s = NONE) = (dft_restore outs ret cs t = NONE)
Proof
  simp[dft_restore_failure]
QED

Theorem dft_restore_cut_pair:
  dft_cut_pair us vs s t /\
  EVERY (\p. ~MEM (FST p) outs) us /\
  EVERY (\p. ~MEM (FST p) outs) vs /\
  dft_restore outs ret cs s = SOME s' /\
  dft_restore outs ret cs t = SOME t' ==>
  dft_cut_pair us vs s' t'
Proof
  strip_tac >> fs[dft_cut_pair_def] >>
  qpat_x_assum `dft_cut_data s = dft_pending_apply us _`
    (mp_tac) >>
  qmatch_goalsub_rename_tac `dft_pending_apply us b0` >> strip_tac >>
  `dft_restore outs ret cs (dft_cut_data s) = SOME (dft_cut_data s')` by
    simp[dft_restore_cut_data] >>
  `dft_restore outs ret cs (dft_cut_data t) = SOME (dft_cut_data t')` by
    simp[dft_restore_cut_data] >>
  `OPTION_MAP (dft_pending_apply us) (dft_restore outs ret cs b0) =
     SOME (dft_cut_data s')` by metis_tac[dft_restore_pending] >>
  `OPTION_MAP (dft_pending_apply vs) (dft_restore outs ret cs b0) =
     SOME (dft_cut_data t')` by metis_tac[dft_restore_pending] >>
  Cases_on `dft_restore outs ret cs b0` >> gvs[] >>
  metis_tac[]
QED

Definition dft_saved_call_def:
  dft_saved_call w lctx lc0 lh lrs rctx rc0 rh rrs outs s t <=>
    dft_receipt_list w lctx lc0 lh lrs /\
    dft_receipt_list w rctx rc0 rh rrs /\
    dft_cut_pair (dft_receipt_payload lrs) (dft_receipt_payload rrs) s t /\
    EVERY (\p. ~MEM (FST p) outs) (dft_receipt_payload lrs) /\
    EVERY (\p. ~MEM (FST p) outs) (dft_receipt_payload rrs)
End

Theorem dft_saved_call_restore:
  dft_saved_call w lctx lc0 lh lrs rctx rc0 rh rrs outs s t /\
  dft_restore outs ret cs s = SOME s' /\
  dft_restore outs ret cs t = SOME t' ==>
  dft_saved_call w lctx lc0 lh lrs rctx rc0 rh rrs outs s' t'
Proof
  simp[dft_saved_call_def] >> rpt strip_tac >>
  drule_all dft_restore_cut_pair >> simp[]
QED
