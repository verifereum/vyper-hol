(* Join the two source-read modes before the delayed unwrap.  The
   deployment branch uses the checker artifact, rather than a read-only
   syntactic claim about nested callees. *)
Theory bodyAssignLocalSavedSupplierMods
Ancestors
  bodyAssignLocalSavedMods bodyCopyReachedRhsMods bodySavedTargetSourceMods
  bodySavedTargetDeployReadMods bodySavedTargetVvPostMods bodySavedTargetPtrMods
  bodySavedRhsSlotLiveMods bodyWriteTargetStageMods
  bodyFullPostsMods exprLoweringProps loweringPosts compileEnv
  vyperInterpreter vyperState vyperAST context words arithmetic

Theorem assign_local_saved_read_mods:
  ((contract_inv mods exps ctx cenv cx /\ ~cx.in_deploy /\
    check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
    EVERY (source_body_call_supported cx) (int_calls_target bt) /\
    EVERY (\k. MEM k (linked_live_functions mods exps)) (int_calls_target bt) /\
    ~expr_can_mutate cenv (target_to_expr bt)) \/
   (contract_inv mods exps ctx cenv cx /\ cx.in_deploy /\
    exports_ok cx.layouts cx.txn.target mods exps /\
    IS_SOME (check_contract F cx.layouts cx.txn.target mods) /\
    check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
    EVERY (source_body_call_supported cx) (int_calls_target bt) /\
    EVERY (\k. MEM k (linked_live_functions mods exps)) (int_calls_target bt) /\
    ~expr_can_mutate cenv (target_to_expr bt))) /\
  (!tail. eval_target_place cx bt (mid with gas_obs := target_gas ++ tail) =
    (INL p,ee with gas_obs := tail)) /\
  read_result cx raw mid = (INL v,mid) ==>
  read_result cx raw ee = (INL v,ee)
Proof
  strip_tac >> Cases_on `cx.in_deploy` >> gvs[]
  >- (mp_tac saved_target_source_update_mods >>
      (impl_tac >- simp[]) >>
      disch_then (strip_assume_tac) >> first_assum ACCEPT_TAC)
  >- (mp_tac saved_target_read_deploy_mods >>
      (impl_tac >- simp[]) >>
      disch_then ACCEPT_TAC)
QED
