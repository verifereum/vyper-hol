(* Source frames for expressions without Call or Pop. Gas readings and
   precompile outcomes are the only source fields these expressions consume. *)
Theory bodyIntCallJointPureSource
Ancestors
  supportedExprTraverse vyperAST vyperInterpreter vyperState vyperStatePreservation
  vyperPlaceFrames vyperContext vyperMisc list pair sum exprCallBounds exprCallbackContracts

Theorem eval_exprs_normalized_frame[local]:
  (!e. MEM e es ==> !st res st'. eval_expr cx e st = (res,st') ==>
    (st' with <|gas_obs := []; outcomes := NONE|>) =
    (st with <|gas_obs := []; outcomes := NONE|>)) ==>
  !st res st'. eval_exprs cx es st = (res,st') ==>
    (st' with <|gas_obs := []; outcomes := NONE|>) =
    (st with <|gas_obs := []; outcomes := NONE|>)
Proof
  Induct_on `es` >> simp[Once evaluate_def, return_def] >>
  rpt gen_tac >> strip_tac >>
  `!st res st'. eval_expr cx h st = (res,st') ==>
    (st' with <|gas_obs := []; outcomes := NONE|>) =
    (st with <|gas_obs := []; outcomes := NONE|>)` by
      (first_x_assum (qspec_then `h` mp_tac) >> simp[]) >>
  `!st res st'. eval_exprs cx es st = (res,st') ==>
    (st' with <|gas_obs := []; outcomes := NONE|>) =
    (st with <|gas_obs := []; outcomes := NONE|>)` by
      (gvs[] >> qpat_x_assum `_ ==> !st res st'. eval_exprs _ _ _ = _ ==> _` match_mp_tac >> rpt strip_tac >>
       qpat_x_assum `!e. _` (qspec_then `e` mp_tac) >> simp[]) >>
  qpat_x_assum `!e. e = h \/ MEM e es ==> _` kall_tac >>
  qpat_x_assum `_ ==> !st res st'. eval_exprs _ _ _ = _ ==> _` kall_tac >>
  rpt strip_tac >> gvs[bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac read_result_state >> gvs[] >> metis_tac[]
QED

Theorem effect_free_eval_expr_frame:
  !e cx st res st'. ~expr_has_effect e /\
    eval_expr cx e st = (res,st') ==>
    (st' with <|gas_obs := []; outcomes := NONE|>) =
    (st with <|gas_obs := []; outcomes := NONE|>)
Proof
  measureInduct_on `expr_size e` >> Cases_on `e` >>
  simp[expr_has_effect_def, supported_expr_exists_def, expr_effect_root_def] >>
  rpt gen_tac
  >~ [`eval_expr cx (Name ty nm) st`]
  >- (simp[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
           type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[])
  >~ [`eval_expr cx (Literal ty lit) st`]
  >- simp[Once evaluate_def, return_def]
  >~ [`eval_expr cx (TopLevelName ty nsid) st`]
  >- (PairCases_on `nsid` >> simp[Once evaluate_def] >> strip_tac >>
      drule lookup_global_state >> simp[])
  >~ [`eval_expr cx (FlagMember ty nsid mid) st`]
  >- (simp[Once evaluate_def] >> strip_tac >>
      drule lookup_flag_mem_state >> simp[])
  >~ [`eval_expr cx (IfExp ty c a b) st`]
  >- (strip_tac >>
      first_assum (qspec_then `c` mp_tac) >>
      simp[expr_size_def, expr_has_effect_def] >> strip_tac >>
      first_assum (qspec_then `a` mp_tac) >>
      simp[expr_size_def, expr_has_effect_def] >> strip_tac >>
      qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >>
      simp[expr_size_def, expr_has_effect_def] >> strip_tac >>
      suspend "ifexp")
  >~ [`StructLit _ _ _`]
  >- suspend "structlit"
  >~ [`Attribute _ _ _`]
  >- (rename1 `Attribute at ae af` >> strip_tac >> qpat_x_assum `!y. _` (qspec_then `ae` mp_tac) >>
      simp[expr_size_def, expr_has_effect_def] >> strip_tac >>
      suspend "attribute")
  >~ [`Subscript _ _ _`]
  >- (rename1 `eval_expr cx (Subscript ty ae idx) st` >>
      strip_tac >> first_assum (qspec_then `ae` mp_tac) >>
      simp[expr_size_def, expr_has_effect_def] >> strip_tac >>
      qpat_x_assum `!y. _` (qspec_then `idx` mp_tac) >>
      simp[expr_size_def, expr_has_effect_def] >> strip_tac >>
      suspend "subscript")
  >~ [`Builtin _ _ _`]
  >- suspend "builtin"
  >~ [`TypeBuiltin _ _ _ _`]
  >- suspend "typebuiltin"
QED

Resume effect_free_eval_expr_frame[ifexp]:
  gvs[Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs(),
      return_def, raise_def] >>
  imp_res_tac read_result_state >>
  imp_res_tac conditional_result_state >> gvs[] >>
  gvs[COND_RATOR, AllCaseEqs(), raise_def] >> metis_tac[]
QED
Resume effect_free_eval_expr_frame[attribute]:
  gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
  imp_res_tac select_result_state >> gvs[] >> metis_tac[]
QED
Resume effect_free_eval_expr_frame[subscript]:
  gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >>
  gvs[] >> metis_tac[]
QED
Resume effect_free_eval_expr_frame[structlit]:
  rename1 `StructLit aty sid fields` >> strip_tac >>
  `!e. MEM e (MAP SND fields) ==> !st res st'.
    eval_expr cx e st = (res,st') ==>
    (st' with <|gas_obs := []; outcomes := NONE|>) =
    (st with <|gas_obs := []; outcomes := NONE|>)` by
    (rpt strip_tac >>
     `expr_size e < expr_size (StructLit aty sid fields)` by
       (irule struct_callback_child_bound >> simp[]) >>
     qpat_x_assum `!y. _` (qspec_then `e` mp_tac) >>
     simp[] >> disch_then irule >>
     gvs[expr_has_effect_def, supported_fields_exists_every,
         EVERY_MEM, EXISTS_MEM, MEM_MAP, FORALL_PROD] >>
     PairCases_on `y` >> gvs[] >> metis_tac[]) >>
  drule eval_exprs_normalized_frame >> strip_tac >>
  PairCases_on `sid` >>
  gvs[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
  metis_tac[]
QED
Resume effect_free_eval_expr_frame[typebuiltin]:
  rename1 `TypeBuiltin aty tb typ args` >> strip_tac >>
  `!e. MEM e args ==> !st res st'. eval_expr cx e st = (res,st') ==>
    (st' with <|gas_obs := []; outcomes := NONE|>) =
    (st with <|gas_obs := []; outcomes := NONE|>)` by
    (rpt strip_tac >>
     `expr_size e < list_size expr_size args` by
       (irule expr_list_member_bound >> simp[]) >>
     qpat_x_assum `!y. _` (qspec_then `e` mp_tac) >>
     simp[expr_size_def] >> disch_then irule >>
     gvs[expr_has_effect_def, supported_exprs_exists_every, EXISTS_MEM] >>
     metis_tac[]) >>
  drule eval_exprs_normalized_frame >> strip_tac >>
  qpat_x_assum `!y. expr_size y < _ ==> _` kall_tac >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
      assert_def, return_def, raise_def, lift_sum_def, AllCaseEqs()] >>
  gvs[sum_CASE_rator, AllCaseEqs(), return_def, raise_def, ETA_THM] >>
  metis_tac[]
QED
Resume effect_free_eval_expr_frame[builtin]:
  rename1 `Builtin aty bt args` >> strip_tac >>
  `!e. MEM e args ==> !st res st'. eval_expr cx e st = (res,st') ==>
    (st' with <|gas_obs := []; outcomes := NONE|>) =
    (st with <|gas_obs := []; outcomes := NONE|>)` by
    (rpt strip_tac >>
     `expr_size e < list_size expr_size args` by
       (irule expr_list_member_bound >> simp[]) >>
     qpat_x_assum `!y. _` (qspec_then `e` mp_tac) >>
     simp[expr_size_def] >> disch_then irule >>
     gvs[expr_has_effect_def, supported_exprs_exists_every, EXISTS_MEM] >>
     metis_tac[]) >>  drule eval_exprs_normalized_frame >> strip_tac >>
  qpat_x_assum `!y. expr_size y < _ ==> _` kall_tac >>
  Cases_on `bt = Len`
  >- (gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
          assert_def, return_def, raise_def, AllCaseEqs()] >>
      imp_res_tac result_array_length_state >> gvs[] >>
      `MEM (HD args) args` by
        (Cases_on `args` >> gvs[builtin_args_length_ok_def]) >>
      qpat_x_assum `!e. MEM e args ==> _` (qspec_then `HD args` mp_tac) >>
      simp[] >> metis_tac[]) >>
  Cases_on `bt = Env MsgGas`
  >- (gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
          assert_def, return_def, raise_def, AllCaseEqs()] >>
      imp_res_tac next_gas_reading_state >> gvs[]) >>
  Cases_on `bt = Bop In \/ bt = Bop NotIn`
  >- (gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
          assert_def, return_def, raise_def, lift_sum_def, AllCaseEqs()] >>
      gvs[sum_CASE_rator, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac lift_option_type_state >> gvs[] >>
      qpat_x_assum `!e. MEM e args ==> _` kall_tac >> metis_tac[]) >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
      assert_def, return_def, raise_def, get_accounts_def, lift_sum_def,
      AllCaseEqs()] >>
  gvs[sum_CASE_rator, AllCaseEqs(), return_def, raise_def, ETA_THM] >>
  imp_res_tac precompile_call_success_state >> gvs[] >>
  qpat_x_assum `!e. MEM e args ==> _` kall_tac >> metis_tac[]
QED
Finalise effect_free_eval_expr_frame

Theorem effect_free_eval_exprs_frame:
  !es cx st res st'. EVERY (\e. ~expr_has_effect e) es /\
    eval_exprs cx es st = (res,st') ==>
    (st' with <|gas_obs := []; outcomes := NONE|>) =
    (st with <|gas_obs := []; outcomes := NONE|>)
Proof
  rpt gen_tac >> strip_tac >>
  irule eval_exprs_normalized_frame >>
  qexistsl [`cx`, `es`, `res`] >> simp[] >>
  rpt strip_tac >>
  `~expr_has_effect e` by gvs[EVERY_MEM] >>
  drule_all effect_free_eval_expr_frame >> simp[]
QED
