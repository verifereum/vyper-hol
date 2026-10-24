(* TOP-LEVEL: raw_revert_no_success, selfdestruct_no_success. *)
Theory vyperSystemControl
Ancestors vyperInterpreter vyperState vyperAST vyperMisc vyperTypeSystem
Libs BasicProvers

Theorem raw_revert_no_success:
  eval_expr cx (Call ty RawRevert es drv) st <> (INL value,st')
Proof
  simp[Once evaluate_def, bind_def, ignore_bind_def, raise_def] >>
  rpt (PURE_TOP_CASE_TAC >>
       simp[bind_def, ignore_bind_def, type_check_def, assert_def,
            lift_option_type_def, return_def, raise_def])
QED

Theorem selfdestruct_no_success:
  eval_expr cx (Call ty SelfDestructTarget es drv) st <> (INL value,st')
Proof
  simp[Once evaluate_def, bind_def, ignore_bind_def, raise_def] >>
  rpt (PURE_TOP_CASE_TAC >>
       simp[bind_def, ignore_bind_def, type_check_def, assert_def,
            lift_option_type_def, get_accounts_def, update_accounts_def,
            update_pending_deletions_def, return_def, raise_def])
QED

Theorem expr_no_fallthrough_no_success:
  expr_no_fallthrough e ==> eval_expr cx e st <> (INL value,st')
Proof
  Cases_on `e` >> simp[expr_no_fallthrough_def] >>
  rename1 `Call ty target es drv` >> Cases_on `target` >>
  simp[expr_no_fallthrough_def] >>
  simp[raw_revert_no_success, selfdestruct_no_success]
QED
