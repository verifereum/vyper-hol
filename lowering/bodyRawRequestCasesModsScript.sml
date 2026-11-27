(* Publish the linked cases for Send and the two raw-call input routes. *)
Theory bodyRawRequestCasesMods
Ancestors
  bodyFullPredsMods bodyRawRequestInputsMods bodyRawRequestWordsMods
  bodySendComposeMods bodySendTailOutcomeMods bodyRawContinuationMods
  bodyRawBytesRequestMods bodyRawCalldataRequestMods bodyRawResultReadMods
  vyperAST vyperState

Theorem body_send_case_full_mods:
  !mods exps cx ann has_gas args dflt.
    (!s x t. type_check (LENGTH args = (if has_gas then 3 else 2)) "Send args" s =
       (INL x,t) ==> body_exprs_full_ok_mods mods exps cx args) ==>
    body_expr_full_ok_mods mods exps cx (Call ann (Send has_gas) args dflt)
Proof
  rpt gen_tac >> disch_tac >> match_mp_tac send_case_from_parts_mods >>
  conj_tac >- ACCEPT_TAC (GEN_ALL send_pre_types_mods) >>
  conj_tac >- ACCEPT_TAC (GEN_ALL request_operand_pre_mods) >>
  conj_tac >- ACCEPT_TAC (GEN_ALL request_word_prefix_mods) >>
  conj_tac
  >- ACCEPT_TAC (GEN_ALL (CONV_RULE (DEPTH_CONV ETA_CONV) send_tail_outcome_full_mods)) >>
  first_assum ACCEPT_TAC
QED

Theorem raw_call_expr_full_ok_mods:
  !mods exps cx ann flags args dflt.
    body_exprs_full_ok_mods mods exps cx args ==>
    body_expr_full_ok_mods mods exps cx (Call ann (RawCallTarget flags) args dflt)
Proof
  rpt gen_tac >> disch_tac >> simp[Once body_expr_full_ok_mods_def] >>
  rpt gen_tac >> disch_then strip_assume_tac >> reverse conj_asm2_tac
  >- (irule raw_call_vv_from_parts_mods >>
      qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
      qpat_assum `body_const_cells_agree_mods _ _ _ _` (irule_at Any) >>
      qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
      rpt conj_tac >>
      (first_assum ACCEPT_TAC ORELSE
       (rpt gen_tac >> MATCH_ACCEPT_TAC raw_call_continuation_full_mods))) >>
  irule raw_request_value_of_vv_mods >>
  qpat_assum `expr_body_pre_mods _ _ _ _ _ _` (irule_at Any) >> simp[]
QED

Theorem raw_call_calldata_expr_full_ok_mods:
  !mods exps cx ann flags args dflt.
    body_exprs_full_ok_mods mods exps cx args ==>
    body_expr_full_ok_mods mods exps cx (Call ann (RawCallCalldataTarget flags) args dflt)
Proof
  rpt gen_tac >> disch_tac >> simp[Once body_expr_full_ok_mods_def] >>
  rpt gen_tac >> disch_then strip_assume_tac >> reverse conj_asm2_tac
  >- (irule raw_calldata_vv_from_parts_mods >>
      qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
      qpat_assum `body_const_cells_agree_mods _ _ _ _` (irule_at Any) >>
      qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
      rpt conj_tac >>
      (first_assum ACCEPT_TAC ORELSE
       (rpt gen_tac >> MATCH_ACCEPT_TAC raw_call_continuation_full_mods))) >>
  irule raw_request_value_of_vv_mods >>
  qpat_assum `expr_body_pre_mods _ _ _ _ _ _` (irule_at Any) >> simp[]
QED
