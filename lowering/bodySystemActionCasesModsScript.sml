(* Linked expression rules for the three system actions. *)
Theory bodySystemActionCasesMods
Ancestors
  bodyFullPredsMods bodyRawLogCaseMods bodyRawRevertCaseMods
  bodySelfDestructCaseMods

Theorem body_raw_log_case_full_mods:
  !mods exps cx ann args dflt.
    body_exprs_full_ok_mods mods exps cx args ==>
    body_expr_full_ok_mods mods exps cx (Call ann RawLog args dflt)
Proof
  rpt gen_tac >> MATCH_ACCEPT_TAC bodyRawLogCaseModsTheory.body_raw_log_case_full_mods
QED

Theorem body_raw_revert_case_full_mods:
  !mods exps cx ann args dflt.
    body_exprs_full_ok_mods mods exps cx args ==>
    body_expr_full_ok_mods mods exps cx (Call ann RawRevert args dflt)
Proof
  ACCEPT_TAC bodyRawRevertCaseModsTheory.body_raw_revert_case_full_mods
QED

Theorem body_selfdestruct_case_full_mods:
  !mods exps cx ann args dflt.
    body_exprs_full_ok_mods mods exps cx args ==>
    body_expr_full_ok_mods mods exps cx (Call ann SelfDestructTarget args dflt)
Proof
  ACCEPT_TAC bodySelfDestructCaseModsTheory.body_selfdestruct_case_full_mods
QED
