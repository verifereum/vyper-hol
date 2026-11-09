(* Source-state boundary for deferred pure call operands. *)
Theory bodyIntCallJointCallSource
Ancestors
  supportedExprs vyperInterpreter vyperState vyperContext vyperMisc
  vyperStatePreservation vyperPlaceFrames vyperCallFrame
  vyperImmutablesPreservation pair sum

Theorem intcall_pure_immutables_mutual:
  (!tops e. supported_pure_expr tops e ==>
    !cx s r t. eval_expr cx e s = (r,t) ==> t.immutables = s.immutables) /\
  (!tops es. supported_pure_exprs tops es ==>
    (!cx s r t. eval_exprs cx es s = (r,t) ==> t.immutables = s.immutables) /\
    (!e. MEM e es ==> !cx s r t.
      eval_expr cx e s = (r,t) ==> t.immutables = s.immutables)) /\
  (!tops fs. supported_pure_fields tops fs ==>
    !cx s r t. eval_exprs cx (MAP SND fs) s = (r,t) ==>
      t.immutables = s.immutables) /\
  (!tops e. supported_place_expr tops e ==>
    !cx s r t. eval_expr cx e s = (r,t) ==> t.immutables = s.immutables)
Proof
  ho_match_mp_tac supported_pure_expr_ind >>
  rpt conj_tac >> rpt gen_tac >> simp[supported_pure_expr_def]
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
          type_check_def, assert_def, return_def, raise_def, AllCaseEqs()])
  >- simp[Once evaluate_def, return_def]
  >- (PairCases_on `id` >> rpt strip_tac >>
      gvs[Once evaluate_def] >> metis_tac[lookup_global_immutables])
  >- suspend "ifexp"
  >- suspend "structlit"
  >- suspend "subscript"
  >- suspend "attribute"
  >- suspend "builtin"
  >- suspend "typebuiltin"
  >- suspend "nil"
  >- suspend "cons"
  >- suspend "fields_nil"
  >- suspend "fields_cons"
  >- suspend "place_name"
  >- suspend "place_global"
  >- suspend "place_subscript"
  >> suspend "place_rest"
QED

Resume intcall_pure_immutables_mutual[ifexp]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs(),
      return_def, raise_def] >>
  imp_res_tac read_result_state >>
  imp_res_tac conditional_result_state >> gvs[] >>
  gvs[COND_RATOR, AllCaseEqs(), raise_def] >> metis_tac[]
QED
Resume intcall_pure_immutables_mutual[structlit]:
  PairCases_on `id` >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >> metis_tac[]
QED
Resume intcall_pure_immutables_mutual[subscript]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >>
  gvs[] >> metis_tac[]
QED
Resume intcall_pure_immutables_mutual[attribute]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac select_result_state >> gvs[] >> metis_tac[]
QED
Resume intcall_pure_immutables_mutual[builtin]:
  rpt strip_tac >>
  Cases_on `blt = Len` >> Cases_on `blt = Env MsgGas` >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
      assert_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac result_array_length_state >>
  imp_res_tac next_gas_reading_state >>
  imp_res_tac lift_sum_state >> imp_res_tac get_accounts_state >>
  imp_res_tac precompile_call_success_state >> gvs[] >>
  gvs[builtin_args_length_ok_def] >>
  Cases_on `es` >> gvs[] >> first_x_assum drule_all >> simp[]
QED
Resume intcall_pure_immutables_mutual[typebuiltin]:
  rpt strip_tac >>
  gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
      ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac lift_sum_state >> gvs[] >> metis_tac[]
QED
Resume intcall_pure_immutables_mutual[nil]:
  simp[Once evaluate_def, return_def]
QED
Resume intcall_pure_immutables_mutual[cons]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac read_result_state >> gvs[] >> metis_tac[]
QED
Resume intcall_pure_immutables_mutual[fields_nil]:
  simp[Once evaluate_def, return_def]
QED
Resume intcall_pure_immutables_mutual[fields_cons]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac read_result_state >> gvs[] >> metis_tac[]
QED
Resume intcall_pure_immutables_mutual[place_name]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
      type_check_def, assert_def, return_def, raise_def, AllCaseEqs()]
QED
Resume intcall_pure_immutables_mutual[place_global]:
  PairCases_on `id` >> rpt strip_tac >>
  gvs[Once evaluate_def] >> metis_tac[lookup_global_immutables]
QED
Resume intcall_pure_immutables_mutual[place_subscript]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >>
  gvs[] >> metis_tac[]
QED
Resume intcall_pure_immutables_mutual[place_rest]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac select_result_state >> gvs[] >> metis_tac[]
QED
Finalise intcall_pure_immutables_mutual

Theorem intcall_pure_expr_immutables:
  supported_pure_expr tops e /\ eval_expr cx e es = (r,ee) ==>
  ee.immutables = es.immutables
Proof
  metis_tac[intcall_pure_immutables_mutual]
QED

Theorem intcall_pure_results_immutables:
  !args tops cx es r ee.
    supported_pure_exprs tops args /\
    eval_expr_results cx args es = (r,ee) ==>
    ee.immutables = es.immutables
Proof
  Induct >> simp[supported_pure_expr_def, Once evaluate_def, return_def] >>
  rpt strip_tac >> gvs[bind_def, AllCaseEqs(), return_def] >>
  metis_tac[intcall_pure_expr_immutables]
QED
