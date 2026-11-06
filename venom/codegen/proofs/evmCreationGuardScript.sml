(* Fixed-address creation-status boundaries for EVM execution. *)
Theory evmCreationGuard
Ancestors
  vfmAccountDeletion vfmExecution vfmExecutionProp vfmState vfmContext
  vfmTypes vfmPreserves list combin

Theorem step_inst_creation_original_empty:
  s.contexts <> [] /\
  (account_empty (lookup_account a s.originalAccounts) \/
   account_already_created (lookup_account a s.rollback.accounts)) /\
  step_inst op s = (r,t) ==>
  (account_empty (lookup_account a t.originalAccounts) =
   account_empty (lookup_account a s.originalAccounts))
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  Cases_on `op = Create \/ op = Create2`
  >- (gvs[step_inst_def] >>
      drule_all step_create_deletion_projections >> strip_tac >> gvs[] >>
      Cases_on `a = b` >>
      gvs[lookup_account_def, update_account_def, combinTheory.APPLY_UPDATE_THM,
          account_empty_def, account_already_created_def, empty_account_state_def]) >>
  Cases_on `op = Call \/ op = CallCode \/ op = DelegateCall \/ op = StaticCall`
  >- (gvs[step_inst_def] >>
      drule_all (SRULE [preserves_when_def] step_call_deletion_call) >>
      simp[]) >>
  Cases_on `op = SelfDestruct`
  >- (gvs[step_inst_def] >>
      drule_all step_self_destruct_deletion_provenance >> simp[]) >>
  gvs[] >>
  mp_tac step_inst_deletion_exact >>
  simp[preserves_when_def] >>
  disch_then (qspecl_then [`s`, `r`, `t`] mp_tac) >> simp[]
QED
