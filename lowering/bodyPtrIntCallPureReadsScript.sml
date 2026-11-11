Theory bodyPtrIntCallPureReads
Ancestors
  list rich_list finite_map vyperMisc vyperState vyperLookup vyperInterpreter
  vyperStatePreservation supportedExprs supportedExprTraverse
  vyperPlaceFrames vyperStorageBackend supportedExprForms stmtSimForArrayFrame

(* The observations consumed by delayed reads exclude gas and oracle cursors. *)
Theorem intcall_pure_read_observations_mutual:
  (!tops e. supported_pure_expr tops e ==>
    !cx es res ee. eval_expr cx e es = (res,ee) ==>
      ee.scopes = es.scopes /\ ee.accounts = es.accounts /\ ee.tStorage = es.tStorage /\
      ee.immutables = es.immutables) /\
  (!tops args. supported_pure_exprs tops args ==>
    !cx es res ee. eval_exprs cx args es = (res,ee) ==>
      ee.scopes = es.scopes /\ ee.accounts = es.accounts /\ ee.tStorage = es.tStorage /\
      ee.immutables = es.immutables) /\
  (!tops fields. supported_pure_fields tops fields ==>
    !cx es res ee. eval_exprs cx (MAP SND fields) es = (res,ee) ==>
      ee.scopes = es.scopes /\ ee.accounts = es.accounts /\ ee.tStorage = es.tStorage /\
      ee.immutables = es.immutables) /\
  (!tops e. supported_place_expr tops e ==>
    !cx es res ee. eval_expr cx e es = (res,ee) ==>
      ee.scopes = es.scopes /\ ee.accounts = es.accounts /\ ee.tStorage = es.tStorage /\
      ee.immutables = es.immutables)
Proof
  ho_match_mp_tac supported_pure_expr_ind >> rpt conj_tac >>
  simp[supported_pure_expr_def] >>
  rpt (gen_tac ORELSE disch_then strip_assume_tac)
  >>~- ([`eval_expr _ (Name _ _) _ = _`],
      gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
          type_check_def, assert_def, lift_option_type_def,
          return_def, raise_def, AllCaseEqs()])
  >>~- ([`eval_expr _ (Literal _ _) _ = _`],
      gvs[Once evaluate_def, return_def])
  >>~- ([`eval_expr _ (TopLevelName _ _) _ = _`],
      rename1 `eval_expr cx (TopLevelName ty nsid) es = _` >>
      PairCases_on `nsid` >> gvs[Once evaluate_def] >>
      imp_res_tac lookup_global_state >> gvs[])
  >>~- ([`eval_expr _ (IfExp _ _ _ _) _ = _`], suspend "ifexp")
  >>~- ([`eval_expr _ (StructLit _ _ _) _ = _`], suspend "struct")
  >~ [`eval_expr _ (Subscript _ _ _) _ = _`] >- suspend "subscript1"
  >>~- ([`eval_expr _ (Subscript _ _ _) _ = _`], suspend "subscript2")
  >~ [`eval_expr _ (Attribute _ _ _) _ = _`] >- suspend "attribute1"
  >>~- ([`eval_expr _ (Attribute _ _ _) _ = _`], suspend "attribute2")
  >>~- ([`eval_expr _ (Builtin _ _ _) _ = _`], suspend "builtin")
  >>~- ([`eval_expr _ (TypeBuiltin _ _ _ _) _ = _`], suspend "typebuiltin")
  >> gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def]
  >> imp_res_tac read_result_state >> gvs[] >> metis_tac[]
QED

Resume intcall_pure_read_observations_mutual[ifexp]:
  gvs[Once evaluate_def, bind_def, ignore_bind_def, switch_BoolV_def,
      AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac conditional_result_state >> gvs[] >>
  gvs[COND_RATOR, AllCaseEqs(), raise_def] >> metis_tac[]
QED

Resume intcall_pure_read_observations_mutual[struct]:
  rename1 `eval_expr cx (StructLit ty nsid fields) es = _` >>
  PairCases_on `nsid` >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  metis_tac[]
QED

Resume intcall_pure_read_observations_mutual[subscript1]:
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >>
  gvs[] >> metis_tac[]
QED

Resume intcall_pure_read_observations_mutual[subscript2]:
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >>
  gvs[] >> metis_tac[]
QED

Resume intcall_pure_read_observations_mutual[attribute1]:
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac select_result_state >> gvs[] >> metis_tac[]
QED

Resume intcall_pure_read_observations_mutual[attribute2]:
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac select_result_state >> gvs[] >> metis_tac[]
QED

Resume intcall_pure_read_observations_mutual[builtin]:
  `blt <> Len` by
    (Cases_on `blt = Len` >> gvs[supported_builtin_form_def, AllCaseEqs()]) >>
  Cases_on `blt = Env MsgGas` >>
  gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
      ignore_bind_def, return_def, raise_def, AllCaseEqs(), get_accounts_def] >>
  imp_res_tac next_gas_reading_state >>
  imp_res_tac lift_sum_state >>
  imp_res_tac precompile_call_success_state >> gvs[] >> metis_tac[]
QED

Resume intcall_pure_read_observations_mutual[typebuiltin]:
  gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
      ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac lift_sum_state >> gvs[] >> metis_tac[]
QED

Finalise intcall_pure_read_observations_mutual

Theorem intcall_effect_free_eval_observations:
  supported_expr tops e /\ ~expr_has_effect e /\
  eval_expr cx e es = (res,ee) ==>
  ee.scopes = es.scopes /\ ee.accounts = es.accounts /\
  ee.tStorage = es.tStorage /\ ee.immutables = es.immutables
Proof
  strip_tac >>
  `supported_pure_expr tops e` by
    metis_tac[supported_expr_def, supported_effect_expr_has_effect] >>
  metis_tac[intcall_pure_read_observations_mutual]
QED

Theorem intcall_effect_free_results_observations:
  !args tops cx es res ee.
  EVERY (supported_expr tops) args /\ EVERY (\e. ~expr_has_effect e) args /\
  eval_expr_results cx args es = (res,ee) ==>
  ee.scopes = es.scopes /\ ee.accounts = es.accounts /\
  ee.tStorage = es.tStorage /\ ee.immutables = es.immutables
Proof
  Induct_on `args` >> simp[Once evaluate_def, return_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac intcall_effect_free_eval_observations >> gvs[] >> metis_tac[]
QED

Theorem intcall_read_result_observations:
  es.scopes = ee.scopes /\ es.accounts = ee.accounts /\
  es.tStorage = ee.tStorage /\ es.immutables = ee.immutables /\
  read_result cx raw es = (INL v,es) ==>
  read_result cx raw ee = (INL v,ee)
Proof
  Cases_on `raw` >> simp[read_result_def, return_def, raise_def] >>
  rename1 `read_place cx p es = _` >> Cases_on `p` >>
  simp[read_place_def, read_storage_slot_eq, get_storage_def,
       get_accounts_def, get_transient_storage_def, get_scopes_def,
       get_immutables_def, get_address_immutables_def, bind_def,
       lift_option_type_def, lift_option_def, lift_sum_def,
       return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[option_CASE_rator, sum_CASE_rator, return_def, raise_def,
                      AllCaseEqs()]
  >~ [`get_storage _ _ b`] >- (Cases_on `b` >> gvs[get_storage_def])
QED

Theorem intcall_read_results_observations:
  !raws cx es ee vs.
  es.scopes = ee.scopes /\ es.accounts = ee.accounts /\
  es.tStorage = ee.tStorage /\ es.immutables = ee.immutables /\
  read_results cx raws es = (INL vs,es) ==>
  read_results cx raws ee = (INL vs,ee)
Proof
  Induct_on `raws` >> simp[read_results_def, return_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[read_results_def, bind_def, return_def, AllCaseEqs()] >>
  drule read_result_state >> disch_then SUBST_ALL_TAC >>
  drule_all intcall_read_result_observations >> strip_tac >>
  qexists_tac `ee` >> simp[] >> first_x_assum irule >>
  qexists_tac `es` >> simp[]
QED

Theorem intcall_effect_free_results_delayed_read:
  EVERY (supported_expr tops) args /\ EVERY (\e. ~expr_has_effect e) args /\
  eval_expr_results cx args es = (res,ee) /\
  read_result cx raw es = (INL v,es) ==>
  read_result cx raw ee = (INL v,ee)
Proof
  metis_tac[intcall_effect_free_results_observations,
            intcall_read_result_observations]
QED

Theorem intcall_effect_free_results_delayed_reads:
  EVERY (supported_expr tops) args /\ EVERY (\e. ~expr_has_effect e) args /\
  eval_expr_results cx args es = (res,ee) /\
  read_results cx raws es = (INL vs,es) ==>
  read_results cx raws ee = (INL vs,ee)
Proof
  metis_tac[intcall_effect_free_results_observations,
            intcall_read_results_observations]
QED
