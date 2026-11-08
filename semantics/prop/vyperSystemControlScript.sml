(* Raw revert data and terminal control. *)
Theory vyperSystemControl
Ancestors
  vyperInterpreter vyperSmallStep[ignore_grammar] vyperState vyperAST
  vyperMisc vyperTypeSystem vyperValue vyperValueOperation
Libs BasicProvers

Theorem raw_revert_no_success:
  eval_expr cx (Call ty RawRevert es drv) st <> (INL value,st')
Proof
  simp[Once evaluate_def, vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def, vyperStateTheory.raise_def] >>
  rpt (PURE_TOP_CASE_TAC >>
       simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def, vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
            vyperStateTheory.lift_option_type_def, vyperStateTheory.return_def, vyperStateTheory.raise_def])
QED

Theorem selfdestruct_no_success:
  eval_expr cx (Call ty SelfDestructTarget es drv) st <> (INL value,st')
Proof
  simp[Once evaluate_def, vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def, vyperStateTheory.raise_def] >>
  rpt (PURE_TOP_CASE_TAC >>
       simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def, vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
            vyperStateTheory.lift_option_type_def, vyperStateTheory.get_accounts_def, vyperStateTheory.update_accounts_def,
            vyperStateTheory.update_pending_deletions_def, vyperStateTheory.return_def, vyperStateTheory.raise_def])
QED

Theorem expr_no_fallthrough_no_success:
  expr_no_fallthrough e ==> eval_expr cx e st <> (INL value,st')
Proof
  Cases_on `e` >> simp[expr_no_fallthrough_def] >>
  rename1 `Call ty target es drv` >> Cases_on `target` >>
  simp[expr_no_fallthrough_def] >>
  simp[raw_revert_no_success, selfdestruct_no_success]
QED

(* Revert data is the original byte vector, with no ABI envelope. *)
Theorem raw_revert_bytes:
  eval_exprs cx es st = (INL [BytesV data], st') ==>
  eval_expr cx (Call ty RawRevert es extra) st =
    (INR (Error (RevertData data)), st')
Proof
  strip_tac >> simp[Once evaluate_def, vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
    vyperStateTheory.type_check_def, vyperStateTheory.assert_def, vyperStateTheory.return_def, vyperStateTheory.raise_def,
    vyperStateTheory.lift_option_type_def, dest_BytesV_def]
QED

Theorem raw_revert_argument_error:
  eval_exprs cx es st = (INR ex, st') ==>
  eval_expr cx (Call ty RawRevert es extra) st = (INR ex, st')
Proof
  strip_tac >> simp[Once evaluate_def, vyperStateTheory.bind_def]
QED

Theorem raw_revert_cps_bytes:
  vyperSmallStep$apply_vals cx [BytesV data] st (vyperSmallStep$RawRevertK k) =
    vyperSmallStep$AK cx (vyperSmallStep$ApplyExc (Error (RevertData data))) st k
Proof
  simp[Once vyperSmallStepTheory.apply_vals_def, vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
    vyperStateTheory.type_check_def, vyperStateTheory.assert_def, vyperStateTheory.return_def, vyperStateTheory.raise_def,
    vyperStateTheory.lift_option_type_def, dest_BytesV_def]
QED
