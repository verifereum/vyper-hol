(* Supported loop bodies without internal calls cannot halt the transaction. *)
Theory supportedEvalResults
Ancestors
  supportedStmts supportedStmtTraverse supportedExprTraverse supportedExprs vyperInterpreter
  vyperState vyperStatePreservation vyperMisc vyperCallOutcome vyperCallOutcomeProps

Theorem bind_no_halt:
  (!s t. f s <> (INR HaltException,t)) /\
  (!v s t. g v s <> (INR HaltException,t)) ==>
  !s t. bind f g s <> (INR HaltException,t)
Proof
  simp[bind_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem bind_no_halt_guarded:
  (!s t. f s <> (INR HaltException,t)) /\
  (!v s t u. f s = (INL v,t) ==>
    g v t <> (INR HaltException,u)) ==>
  !s t. bind f g s <> (INR HaltException,t)
Proof
  simp[bind_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem ignore_bind_no_halt:
  (!s t. f s <> (INR HaltException,t)) /\
  (!s t. g s <> (INR HaltException,t)) ==>
  !s t. ignore_bind f g s <> (INR HaltException,t)
Proof
  rewrite_tac[ignore_bind_def] >> strip_tac >>
  irule bind_no_halt >> simp[]
QED

Theorem finally_no_halt:
  (!s t. f s <> (INR HaltException,t)) /\
  (!s t. g s <> (INR HaltException,t)) ==>
  !s t. finally f g s <> (INR HaltException,t)
Proof
  simp[finally_def, ignore_bind_def, bind_def, return_def,
       raise_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem primitive_no_halt[simp]:
  (!v s t. return v s <> (INR HaltException,t)) /\
  (!e s t. raise (Error e) s <> (INR HaltException,t)) /\
  (!b str s t. check b str s <> (INR HaltException,t)) /\
  (!b str s t. type_check b str s <> (INR HaltException,t)) /\
  (!x str s t. lift_option x str s <> (INR HaltException,t)) /\
  (!x str s t. lift_option_type x str s <> (INR HaltException,t)) /\
  (!x s t. lift_sum x s <> (INR HaltException,t)) /\
  (!x s t. lift_sum_runtime x s <> (INR HaltException,t))
Proof
  simp[return_def, raise_def, check_def, type_check_def, assert_def,
       lift_option_def, lift_option_type_def, lift_sum_def,
       lift_sum_runtime_def, option_CASE_rator, sum_CASE_rator,
       return_def, raise_def, AllCaseEqs()]
QED

Theorem get_storage_backend_no_halt[simp]:
  !cx tr s t. get_storage_backend cx tr s <> (INR HaltException,t)
Proof
  Cases_on `tr` >>
  simp[get_storage_backend_def, bind_def, get_transient_storage_def,
       get_accounts_def, return_def]
QED

Theorem get_immutables_no_halt[simp]:
  !cx src s t. get_immutables cx src s <> (INR HaltException,t)
Proof
  simp[get_immutables_def, get_address_immutables_def, bind_def,
       return_def, AllCaseEqs()] >> metis_tac[primitive_no_halt]
QED

Theorem read_storage_slot_no_halt[simp]:
  !cx tr slot tv s t.
    read_storage_slot cx tr slot tv s <> (INR HaltException,t)
Proof
  rewrite_tac[read_storage_slot_def] >> rpt gen_tac >>
  irule bind_no_halt >> simp[]
QED

Theorem read_place_no_halt[simp]:
  !cx p s t. read_place cx p s <> (INR HaltException,t)
Proof
  Cases_on `p` >> simp[read_place_def, get_scopes_def, bind_def,
    return_def, prod_CASE_rator, sum_CASE_rator, AllCaseEqs()] >>
  metis_tac[primitive_no_halt, get_immutables_no_halt]
QED

Theorem read_result_no_halt[simp]:
  !cx pv s t. read_result cx pv s <> (INR HaltException,t)
Proof
  Cases_on `pv` >> simp[read_result_def]
QED

Theorem read_results_no_halt[simp]:
  !cx results s t. read_results cx results s <> (INR HaltException,t)
Proof
  gen_tac >> Induct >> simp[read_results_def] >> rpt gen_tac >>
  irule bind_no_halt >> simp[] >> gen_tac >>
  irule bind_no_halt >> simp[]
QED

Theorem lookup_global_no_halt[simp]:
  !cx src n s t. lookup_global cx src n s <> (INR HaltException,t)
Proof
  simp[lookup_global_def, bind_def, prod_CASE_rator, sum_CASE_rator,
       option_CASE_rator, var_decl_info_CASE_rator, AllCaseEqs()] >>
  metis_tac[primitive_no_halt, get_immutables_no_halt]
QED

Theorem place_type_value_no_halt[simp]:
  !cx p s t. place_type_value cx p s <> (INR HaltException,t)
Proof
  Cases_on `p` >> simp[place_type_value_def, get_scopes_def, bind_def,
    return_def, prod_CASE_rator, sum_CASE_rator, AllCaseEqs()] >>
  metis_tac[primitive_no_halt, get_immutables_no_halt]
QED

Theorem conditional_result_no_halt[simp]:
  !cx pv s t. conditional_result cx pv s <> (INR HaltException,t)
Proof
  Cases_on `pv` >> simp[conditional_result_def, bind_def,
    return_def, prod_CASE_rator, sum_CASE_rator, COND_RATOR,
    AllCaseEqs()] >>
  metis_tac[primitive_no_halt, place_type_value_no_halt, read_place_no_halt]
QED

Theorem write_storage_slot_no_halt[simp]:
  !cx tr slot tv v s t.
    write_storage_slot cx tr slot tv v s <> (INR HaltException,t)
Proof
  Cases_on `tr` >> simp[write_storage_slot_def, bind_def,
    get_storage_backend_def, set_storage_backend_def,
    get_transient_storage_def, get_accounts_def, update_accounts_def,
    update_transient_def, return_def, prod_CASE_rator, sum_CASE_rator,
    AllCaseEqs()] >> metis_tac[primitive_no_halt]
QED

Theorem set_immutable_no_halt[simp]:
  !cx src n tv v s t. set_immutable cx src n tv v s <> (INR HaltException,t)
Proof
  simp[set_immutable_def, bind_def, get_address_immutables_def,
    set_address_immutables_def, return_def, prod_CASE_rator,
    sum_CASE_rator, AllCaseEqs()] >> metis_tac[primitive_no_halt]
QED

Theorem write_place_no_halt[simp]:
  !cx p v s t. write_place cx p v s <> (INR HaltException,t)
Proof
  Cases_on `p` >> simp[write_place_def, bind_def, ignore_bind_def,
    get_scopes_def, set_scopes_def, return_def, prod_CASE_rator,
    sum_CASE_rator, AllCaseEqs()] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  gvs[bind_def, ignore_bind_def, set_scopes_def, return_def,
    AllCaseEqs()] >>
  metis_tac[primitive_no_halt, write_storage_slot_no_halt,
    get_immutables_no_halt, set_immutable_no_halt]
QED

Theorem resolve_array_element_no_halt[simp]:
  !cx tr slot tv subs s t.
    resolve_array_element cx tr slot tv subs s <> (INR HaltException,t)
Proof
  ho_match_mp_tac resolve_array_element_ind >> rpt conj_tac >>
  rpt gen_tac >> simp[Once resolve_array_element_def] >>
  rpt strip_tac >>
  gvs[bind_def, ignore_bind_def, return_def, prod_CASE_rator,
      sum_CASE_rator, AllCaseEqs()] >>
  qmatch_asmsub_rename_tac `bound_CASE bd` >> Cases_on `bd` >>
  gvs[bind_def, ignore_bind_def, return_def, prod_CASE_rator,
      sum_CASE_rator, AllCaseEqs()] >>
  metis_tac[primitive_no_halt, get_storage_backend_no_halt]
QED

Theorem extend_storage_place_no_halt[simp]:
  !cx tr slot tv sb s t.
    extend_storage_place cx tr slot tv sb s <> (INR HaltException,t)
Proof
  gen_tac >> gen_tac >> gen_tac >> gen_tac >> Cases_on `sb`
  >- (Cases_on `tv` >> Cases_on `v` >>
      simp[extend_storage_place_def, bind_def, ignore_bind_def,
           return_def, prod_CASE_rator, sum_CASE_rator, AllCaseEqs()] >>
      rpt strip_tac >> rpt (pairarg_tac >> gvs[return_def]) >>
      gvs[return_def] >> metis_tac[resolve_array_element_no_halt]) >>
  Cases_on `tv` >>
  simp[extend_storage_place_def, bind_def, return_def,
       prod_CASE_rator, sum_CASE_rator, AllCaseEqs()] >>
  rpt strip_tac >> rpt (pairarg_tac >> gvs[return_def]) >>
  gvs[return_def] >> metis_tac[primitive_no_halt]
QED

Theorem extend_place_no_halt[simp]:
  !cx pv sb s t. extend_place cx pv sb s <> (INR HaltException,t)
Proof
  ho_match_mp_tac extend_place_ind >> rpt gen_tac >>
  simp[extend_place_def, bind_def, ignore_bind_def, return_def,
       prod_CASE_rator, sum_CASE_rator, value_type_CASE_rator,
       AllCaseEqs()] >>
  metis_tac[primitive_no_halt, extend_storage_place_no_halt,
    place_type_value_no_halt, read_place_no_halt]
QED

Theorem select_result_no_halt[simp]:
  !cx ty pv sb s t. select_result cx ty pv sb s <> (INR HaltException,t)
Proof
  Cases_on `pv` >> simp[select_result_def, bind_def, return_def,
    prod_CASE_rator, sum_CASE_rator, AllCaseEqs()] >>
  metis_tac[primitive_no_halt, extend_place_no_halt]
QED

Theorem append_place_no_halt[simp]:
  !cx p v s t. append_place cx p v s <> (INR HaltException,t)
Proof
  ho_match_mp_tac append_place_ind >> rpt gen_tac >>
  simp[append_place_def, bind_def, ignore_bind_def, return_def,
    prod_CASE_rator, sum_CASE_rator, AllCaseEqs()] >>
  metis_tac[primitive_no_halt, get_storage_backend_no_halt,
    write_storage_slot_no_halt, place_type_value_no_halt,
    read_place_no_halt, write_place_no_halt]
QED

Theorem pop_place_no_halt[simp]:
  !cx p s t. pop_place cx p s <> (INR HaltException,t)
Proof
  ho_match_mp_tac pop_place_ind >> rpt gen_tac >>
  simp[pop_place_def, bind_def, ignore_bind_def, return_def,
    prod_CASE_rator, sum_CASE_rator, get_scopes_def, set_scopes_def,
    AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[bind_def, ignore_bind_def, return_def,
    prod_CASE_rator, sum_CASE_rator, set_scopes_def, AllCaseEqs()]) >>
  metis_tac[primitive_no_halt, get_storage_backend_no_halt,
    write_storage_slot_no_halt, get_immutables_no_halt,
    set_immutable_no_halt]
QED

Theorem get_place_no_halt[simp]:
  !pv s t. get_place pv s <> (INR HaltException,t)
Proof
  Cases_on `pv` >> simp[get_place_def]
QED

Theorem scope_no_halt[simp]:
  (!s t. push_scope s <> (INR HaltException,t)) /\
  (!n tv v s t. push_scope_with_var n tv v s <> (INR HaltException,t)) /\
  (!s t. pop_scope s <> (INR HaltException,t)) /\
  (!n tv v s t. new_variable n tv v s <> (INR HaltException,t)) /\
  (!log s t. push_log log s <> (INR HaltException,t))
Proof
  simp[push_scope_def, push_scope_with_var_def, pop_scope_def,
    new_variable_def, push_log_def, bind_def, ignore_bind_def,
    get_scopes_def, set_scopes_def, return_def, raise_def,
    list_CASE_rator, prod_CASE_rator, sum_CASE_rator, AllCaseEqs()] >>
  metis_tac[primitive_no_halt]
QED

Theorem switch_BoolV_no_halt:
  (!s t. f s <> (INR HaltException,t)) /\
  (!s t. g s <> (INR HaltException,t)) ==>
  !s t. switch_BoolV cx pv f g s <> (INR HaltException,t)
Proof
  simp[switch_BoolV_def, bind_def, prod_CASE_rator,
    sum_CASE_rator, COND_RATOR, AllCaseEqs()] >>
  metis_tac[primitive_no_halt, read_result_no_halt]
QED

Theorem result_array_length_value_no_halt[local]:
  !v s t.
    (case v of
     | ArrayV (DynArrayV vs) => return (LENGTH vs)
     | ArrayV (SArrayV vs) => return (LENGTH vs)
     | ArrayV (TupleV vs) => return (LENGTH vs)
     | BytesV bs => return (LENGTH bs)
     | StringV bs => return (LENGTH bs)
     | _ => raise (Error (TypeError "result_array_length"))) s <>
    (INR HaltException,t)
Proof
  Cases_on `v` >> simp[] >>
  rename1 `array_value_CASE av` >> Cases_on `av` >> simp[]
QED

Theorem result_array_length_no_halt[simp]:
  !cx pv s t. result_array_length cx pv s <> (INR HaltException,t)
Proof
  ho_match_mp_tac result_array_length_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[result_array_length_def] >> irule bind_no_halt >>
  simp[result_array_length_value_no_halt]
QED

Theorem take_call_outcome_no_halt[simp]:
  !target calldata value_opt s t.
    take_call_outcome target calldata value_opt s <> (INR HaltException,t)
Proof
  rpt strip_tac >> drule take_call_outcome_error >> simp[]
QED

Theorem eval_ext_call_effects_no_halt[simp]:
  !cx target calldata value_opt gas accounts s t.
    eval_ext_call_effects cx target calldata value_opt gas accounts s <>
    (INR HaltException,t)
Proof
  rpt gen_tac >> Cases_on `s.outcomes` >>
  simp[eval_ext_call_effects_def, bind_def, ignore_bind_def, return_def,
    get_transient_storage_def, prod_CASE_rator, sum_CASE_rator, pairTheory.UNCURRY] >>
  rpt strip_tac >>
  gvs[AllCaseEqs(), update_accounts_def, update_transient_def,
    append_logs_def, update_pending_deletions_def,
    adopt_call_outcome_equation, return_def, raise_def, COND_RATOR] >>
  metis_tac[primitive_no_halt, take_call_outcome_no_halt]
QED

Theorem eval_ext_call_no_halt[simp]:
  !cx static skip sig opts vs s t.
    eval_ext_call cx static skip sig opts vs s <> (INR HaltException,t)
Proof
  rpt gen_tac >> PairCases_on `sig` >> Cases_on `vs` >>
  simp[eval_ext_call_def, bind_def, ignore_bind_def,
    type_check_def, check_def, assert_def, lift_option_type_def,
    get_accounts_def, return_def, raise_def,
    prod_CASE_rator, sum_CASE_rator, option_CASE_rator,
    COND_RATOR, AllCaseEqs()] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[primitive_no_halt, eval_ext_call_effects_no_halt]
QED

Theorem eval_send_no_halt[simp]:
  !cx has_gas vs s t. eval_send cx has_gas vs s <> (INR HaltException,t)
Proof
  gen_tac >> gen_tac >> Cases_on `vs` >- simp[eval_send_def] >>
  Cases_on `t` >- simp[eval_send_def] >>
  rpt gen_tac >> spose_not_then assume_tac >>
  gvs[eval_send_def, bind_def, ignore_bind_def, return_def,
    get_accounts_def, get_transient_storage_def, update_accounts_def,
    update_transient_def, append_logs_def, update_pending_deletions_def,
    adopt_call_outcome_equation, type_check_def, check_def, assert_def,
    lift_option_type_def, raise_def, prod_CASE_rator, sum_CASE_rator,
    option_CASE_rator, COND_RATOR, AllCaseEqs()] >>
  gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[bind_def, ignore_bind_def, return_def,
    check_def, assert_def, adopt_call_outcome_equation,
    prod_CASE_rator, sum_CASE_rator, COND_RATOR, AllCaseEqs()]) >>
  metis_tac[primitive_no_halt, take_call_outcome_no_halt]
QED

Theorem eval_exprs_no_halt:
  !es cx.
    EVERY (\e. !s t. eval_expr cx e s <> (INR HaltException,t)) es ==>
    !s t. eval_exprs cx es s <> (INR HaltException,t)
Proof
  Induct >> simp[Once evaluate_def] >> rpt gen_tac >> strip_tac >>
  irule bind_no_halt >> simp[] >> gen_tac >>
  irule bind_no_halt >> simp[] >> gen_tac >>
  irule bind_no_halt >> simp[]
QED

Theorem next_gas_reading_no_halt[simp]:
  !s t. next_gas_reading s <> (INR HaltException,t)
Proof
  rpt gen_tac >> Cases_on `s.gas_obs` >>
  simp[next_gas_reading_def]
QED

Theorem builtin_no_halt:
  !es cx ty bt.
    EVERY (\e. !s t. eval_expr cx e s <> (INR HaltException,t)) es ==>
    !s t. eval_expr cx (Builtin ty bt es) s <> (INR HaltException,t)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `bt = Len`
  >- (gvs[] >> Cases_on `es`
      >- simp[Once evaluate_def, vyperContextTheory.builtin_args_length_ok_def,
              type_check_def, assert_def, ignore_bind_def, bind_def] >>
      gvs[] >> simp[Once evaluate_def, ignore_bind_def] >>
      irule bind_no_halt >> simp[] >>
      irule bind_no_halt >> simp[] >>
      irule bind_no_halt >> simp[] >> gen_tac >>
      irule bind_no_halt >> simp[]) >>
  Cases_on `bt = Env MsgGas`
  >- (simp[Once evaluate_def, ignore_bind_def] >>
      irule bind_no_halt >> simp[] >>
      irule bind_no_halt >> simp[]) >>
  simp[Once evaluate_def, ignore_bind_def] >>
  irule bind_no_halt >> simp[] >>
  irule bind_no_halt >> simp[] >>
  irule bind_no_halt >>
  simp[eval_exprs_no_halt] >> gen_tac >>
  irule bind_no_halt >> simp[get_accounts_def, return_def] >>
  gen_tac >> irule bind_no_halt >> simp[] >>
  gen_tac >> irule bind_no_halt >> simp[] >>
  rpt strip_tac >> drule precompile_call_success_exception >> simp[]
QED

Theorem name_no_halt[simp]:
  !cx ty nm s t. eval_expr cx (Name ty nm) s <> (INR HaltException,t)
Proof
  simp[Once evaluate_def, get_scopes_def, bind_def, ignore_bind_def,
       return_def, type_check_def, assert_def, raise_def, AllCaseEqs()]
QED

Theorem literal_no_halt[simp]:
  !cx ty l s t. eval_expr cx (Literal ty l) s <> (INR HaltException,t)
Proof
  simp[Once evaluate_def]
QED

Theorem top_level_name_no_halt[simp]:
  !cx ty nm s t. eval_expr cx (TopLevelName ty nm) s <> (INR HaltException,t)
Proof
  rpt gen_tac >> PairCases_on `nm` >> simp[Once evaluate_def]
QED

Theorem if_exp_no_halt:
  (!s t. eval_expr cx e1 s <> (INR HaltException,t)) /\
  (!s t. eval_expr cx e2 s <> (INR HaltException,t)) /\
  (!s t. eval_expr cx e3 s <> (INR HaltException,t)) ==>
  !s t. eval_expr cx (IfExp ty e1 e2 e3) s <> (INR HaltException,t)
Proof
  strip_tac >> simp[Once evaluate_def] >>
  irule bind_no_halt >> simp[] >> gen_tac >>
  irule bind_no_halt >> simp[] >>
  irule switch_BoolV_no_halt >> simp[]
QED

Theorem struct_lit_no_halt:
  EVERY (\e. !s t. eval_expr cx e s <> (INR HaltException,t)) (MAP SND fs) ==>
  !s t. eval_expr cx (StructLit ty nm fs) s <> (INR HaltException,t)
Proof
  strip_tac >> PairCases_on `nm` >> simp[Once evaluate_def] >>
  irule bind_no_halt >> simp[eval_exprs_no_halt]
QED

Theorem subscript_no_halt:
  (!s t. eval_expr cx e1 s <> (INR HaltException,t)) /\
  (!s t. eval_expr cx e2 s <> (INR HaltException,t)) ==>
  !s t. eval_expr cx (Subscript ty e1 e2) s <> (INR HaltException,t)
Proof
  strip_tac >> simp[Once evaluate_def] >>
  irule bind_no_halt >> simp[] >> gen_tac >>
  irule bind_no_halt >> simp[] >> gen_tac >>
  irule bind_no_halt >> simp[]
QED

Theorem attribute_no_halt:
  (!s t. eval_expr cx e s <> (INR HaltException,t)) ==>
  !s t. eval_expr cx (Attribute ty e nm) s <> (INR HaltException,t)
Proof
  strip_tac >> simp[Once evaluate_def] >> irule bind_no_halt >> simp[]
QED

Theorem type_builtin_no_halt:
  EVERY (\e. !s t. eval_expr cx e s <> (INR HaltException,t)) es ==>
  !s t. eval_expr cx (TypeBuiltin ty bt typ es) s <> (INR HaltException,t)
Proof
  strip_tac >> simp[Once evaluate_def, ignore_bind_def] >>
  irule bind_no_halt >> simp[] >>
  irule bind_no_halt >> simp[eval_exprs_no_halt] >> gen_tac >>
  irule bind_no_halt >> simp[]
QED

Theorem supported_pure_no_halt:
  (!tops e. supported_pure_expr tops e ==>
    !cx s t. eval_expr cx e s <> (INR HaltException,t)) /\
  (!tops es. supported_pure_exprs tops es ==>
    EVERY (\e. !cx s t. eval_expr cx e s <> (INR HaltException,t)) es) /\
  (!tops fs. supported_pure_fields tops fs ==>
    EVERY (\e. !cx s t. eval_expr cx e s <> (INR HaltException,t)) (MAP SND fs)) /\
  (!tops e. supported_place_expr tops e ==>
    !cx s t. eval_expr cx e s <> (INR HaltException,t))
Proof
  ho_match_mp_tac supported_pure_expr_ind >> rpt conj_tac >>
  rpt gen_tac >> simp[Once supported_pure_expr_def] >>
  rpt (disch_then strip_assume_tac) >>
  gvs[supported_pure_expr_def, listTheory.EVERY_MEM] >>
  rpt gen_tac
  >~ [`eval_expr cx (IfExp ty a b c)`]
  >- (irule if_exp_no_halt >> simp[])
  >~ [`eval_expr cx (StructLit ty nm fs)`]
  >- (irule struct_lit_no_halt >> simp[listTheory.EVERY_MEM])
  >~ [`eval_expr cx (Builtin ty bt es)`]
  >- (irule builtin_no_halt >> simp[listTheory.EVERY_MEM])
  >~ [`eval_expr cx (TypeBuiltin ty bt typ es)`]
  >- (irule type_builtin_no_halt >> simp[listTheory.EVERY_MEM])
  >>~- ([`eval_expr cx (Subscript ty a b)`],
          irule subscript_no_halt >> simp[])
  >> irule attribute_no_halt >> simp[]
QED

Theorem eval_expr_results_no_halt:
  !es cx.
    EVERY (\e. !s t. eval_expr cx e s <> (INR HaltException,t)) es ==>
    !s t. eval_expr_results cx es s <> (INR HaltException,t)
Proof
  Induct >> simp[Once evaluate_def] >> rpt gen_tac >> strip_tac >>
  irule bind_no_halt >> simp[] >> gen_tac >>
  irule bind_no_halt >> simp[]
QED

Theorem send_call_no_halt:
  EVERY (\e. !s t. eval_expr cx e s <> (INR HaltException,t)) es ==>
  !s t. eval_expr cx (Call ty (Send gas) es dflt) s <> (INR HaltException,t)
Proof
  strip_tac >> simp[Once evaluate_def, ignore_bind_def] >>
  irule bind_no_halt >> simp[] >>
  irule bind_no_halt >> simp[eval_exprs_no_halt]
QED

Theorem ext_call_no_halt:
  EVERY (\e. !s t. eval_expr cx e s <> (INR HaltException,t)) es ==>
  !s t. eval_expr cx (Call ty (ExtCall static skip sig opts) es NONE) s <>
    (INR HaltException,t)
Proof
  strip_tac >> simp[Once evaluate_def] >>
  irule bind_no_halt >>
  simp[eval_exprs_no_halt, rich_listTheory.EVERY_TAKE] >> gen_tac >>
  irule bind_no_halt >>
  simp[eval_expr_results_no_halt, rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP] >>
  gen_tac >> irule bind_no_halt >>
  simp[eval_exprs_no_halt, rich_listTheory.EVERY_DROP] >> gen_tac >>
  irule bind_no_halt >> simp[]
QED

Theorem top_pop_no_halt[simp]:
  !cx ty nm s t.
    eval_expr cx (Pop ty (TopLevelNameTarget nm)) s <> (INR HaltException,t)
Proof
  rpt gen_tac >> PairCases_on `nm` >> simp[Once evaluate_def] >>
  irule bind_no_halt >> simp[] >>
  simp[Once evaluate_def] >> irule bind_no_halt >> simp[] >>
  simp[Once evaluate_def]
QED

Theorem supported_effect_no_halt:
  (!tops e. supported_effect_expr tops e ==>
    ~supported_expr_exists expr_internal_call_root e ==>
    !cx s t. eval_expr cx e s <> (INR HaltException,t)) /\
  (!tops e. supported_effect_place_expr tops e ==>
    ~supported_expr_exists expr_internal_call_root e ==>
    !cx s t. eval_expr cx e s <> (INR HaltException,t))
Proof
  ho_match_mp_tac supported_effect_expr_ind >> rpt conj_tac >>
  rpt gen_tac >> simp[Once supported_effect_expr_def,
    supported_expr_exists_def, expr_internal_call_root_def] >>
  rpt (disch_then strip_assume_tac) >>
  gvs[top_pop_no_halt] >>
  rpt gen_tac
  >~ [`eval_expr cx (Call ty (ExtCall static skip sig opts) args NONE)`]
  >- (irule ext_call_no_halt >>
      drule (cj 2 supported_pure_no_halt) >>
      simp[listTheory.EVERY_MEM])
  >>~- ([`eval_expr cx (Call ty (Send gas) _ NONE)`],
         irule send_call_no_halt >>
         simp[] >> metis_tac[cj 1 supported_pure_no_halt])
  >>~- ([`eval_expr cx (Subscript ty _ _)`],
          irule subscript_no_halt >>
          metis_tac[cj 1 supported_pure_no_halt, cj 4 supported_pure_no_halt])
  >> irule attribute_no_halt >> simp[]
QED

Theorem supported_expr_no_halt:
  supported_expr tops e /\
  ~supported_expr_exists expr_internal_call_root e ==>
  !cx s t. eval_expr cx e s <> (INR HaltException,t)
Proof
  simp[supported_expr_def] >>
  metis_tac[cj 1 supported_pure_no_halt, cj 1 supported_effect_no_halt]
QED

Theorem base_place_name_no_halt[simp]:
  (!cx nm s t. eval_base_place cx (NameTarget nm) s <> (INR HaltException,t)) /\
  (!cx nm s t. eval_base_place cx (TopLevelNameTarget nm) s <> (INR HaltException,t))
Proof
  conj_tac
  >- simp[Once evaluate_def, get_scopes_def, bind_def, ignore_bind_def,
       return_def, type_check_def, assert_def, raise_def, AllCaseEqs()] >>
  rpt gen_tac >> PairCases_on `nm` >> simp[Once evaluate_def]
QED

Theorem base_place_subscript_no_halt:
  (!s t. eval_base_place cx bt s <> (INR HaltException,t)) /\
  (!s t. eval_expr cx e s <> (INR HaltException,t)) ==>
  !s t. eval_base_place cx (SubscriptTarget bt e) s <> (INR HaltException,t)
Proof
  strip_tac >> simp[Once evaluate_def] >>
  irule bind_no_halt >> simp[] >> gen_tac >>
  irule bind_no_halt >> simp[] >> gen_tac >>
  irule bind_no_halt >> simp[]
QED

Theorem base_place_attribute_no_halt:
  (!s t. eval_base_place cx bt s <> (INR HaltException,t)) ==>
  !s t. eval_base_place cx (AttributeTarget bt nm) s <> (INR HaltException,t)
Proof
  strip_tac >> simp[Once evaluate_def] >> irule bind_no_halt >> simp[]
QED

Theorem target_place_no_halt:
  (!s t. eval_base_place cx bt s <> (INR HaltException,t)) ==>
  !s t. eval_target_place cx bt s <> (INR HaltException,t)
Proof
  strip_tac >> simp[Once evaluate_def] >> irule bind_no_halt >> simp[]
QED

Theorem supported_target_info_no_halt:
  !bt tops bindings pt.
    supported_target_info tops bindings bt = SOME pt /\
    ~supported_target_exists expr_internal_call_root bt ==>
    !cx s t. eval_base_place cx bt s <> (INR HaltException,t)
Proof
  gen_tac >> measureInduct_on `base_assignment_target_size bt` >>
  Cases_on `bt` >> rpt gen_tac >>
  simp[supportedTargetsTheory.supported_target_info_def,
    supported_expr_exists_def, AllCaseEqs()] >>
  rpt gen_tac >> rpt (disch_then strip_assume_tac) >>
  rpt gen_tac
  >>~- ([`eval_base_place cx (SubscriptTarget _ _)`],
    irule base_place_subscript_no_halt >> reverse conj_tac
    >- (irule supported_expr_no_halt >> simp[] >> metis_tac[]) >>
    first_x_assum irule >> simp[vyperASTTheory.expr_size_def] >>
    metis_tac[])
  >> irule base_place_attribute_no_halt >>
  first_x_assum irule >> simp[vyperASTTheory.expr_size_def] >>
  metis_tac[]
QED

Theorem supported_target_no_halt:
  supported_target tops bindings bt /\
  ~supported_target_exists expr_internal_call_root bt ==>
  !cx s t. eval_target_place cx bt s <> (INR HaltException,t)
Proof
  Cases_on `bt` >> simp[supported_target_def]
  >- (strip_tac >> gen_tac >> irule target_place_no_halt >> simp[])
  >- (strip_tac >> gen_tac >> irule target_place_no_halt >> simp[]) >>
  rename1 `base_assignment_target_CASE b` >> Cases_on `b` >>
  simp[supported_expr_exists_def] >> rpt (disch_then strip_assume_tac) >>
  gen_tac >> irule target_place_no_halt
  >- (irule base_place_subscript_no_halt >> simp[] >>
      irule supported_expr_no_halt >> metis_tac[]) >>
  irule base_place_attribute_no_halt >> simp[]
QED

Theorem supported_info_target_no_halt:
  supported_target_info tops bindings bt = SOME pt /\
  ~supported_target_exists expr_internal_call_root bt ==>
  !cx s t. eval_target_place cx bt s <> (INR HaltException,t)
Proof
  strip_tac >> gen_tac >> irule target_place_no_halt >>
  irule supported_target_info_no_halt >> metis_tac[]
QED

Theorem supported_append_target_no_halt:
  supported_append_target tops bt ==>
  !cx s t. eval_target_place cx bt s <> (INR HaltException,t)
Proof
  Cases_on `bt` >> simp[supported_append_target_def] >>
  strip_tac >> gen_tac >> irule target_place_no_halt >> simp[]
QED

Theorem flat_assignments_no_halt:
  !gs vs tops bindings.
    EVERY (\g. case g of BaseTarget bt => supported_target tops bindings bt
      | TupleTarget _ => F) gs /\
    ~supported_assignments_exists expr_internal_call_root gs ==>
    !cx s t. assign_tuple_target_list cx gs vs s <> (INR HaltException,t)
Proof
  Induct >> Cases_on `vs` >>
  simp[Once evaluate_def, supported_assignment_exists_def] >>
  rpt gen_tac >> rpt (disch_then strip_assume_tac) >>
  qmatch_asmsub_rename_tac `assignment_target_CASE g` >>
  Cases_on `g` >> gvs[supported_assignment_exists_def] >>
  gen_tac >> simp[Once evaluate_def, ignore_bind_def] >>
  irule bind_no_halt >> conj_tac
  >- (metis_tac[]) >>
  irule bind_no_halt >> simp[] >>
  irule supported_target_no_halt >> metis_tac[]
QED

Theorem supported_assignment_no_halt:
  supported_assignment tops bindings g e /\
  ~supported_assignment_exists expr_internal_call_root g ==>
  !cx v s t. assign_tuple_targets cx g v s <> (INR HaltException,t)
Proof
  Cases_on `g` >> simp[supported_assignment_def,
    supported_assignment_exists_def] >>
  rpt (disch_then strip_assume_tac)
  >- (rpt gen_tac >> simp[Once evaluate_def] >>
      irule bind_no_halt >> simp[] >>
      irule supported_target_no_halt >> metis_tac[])
  >- (rpt gen_tac >> simp[Once evaluate_def] >>
      irule bind_no_halt >> simp[] >>
      Cases_on `supported_target_info tops bindings b` >> gvs[] >>
      rename1 `supported_target_info _ _ _ = SOME pty` >>
      Cases_on `pty` >> gvs[] >>
      irule supported_info_target_no_halt >> metis_tac[]) >>
  gen_tac >> Cases_on `v` >> simp[Once evaluate_def] >>
  rename1 `array_value_CASE av` >> Cases_on `av` >> simp[] >>
  irule flat_assignments_no_halt >> metis_tac[]
QED

Theorem supported_range_endpoints_pure[local]:
  supported_iterator tops ty (Range a b) n ==>
  supported_pure_expr tops a /\ supported_pure_expr tops b
Proof
  Cases_on `a` >> simp[supported_iterator_def, supported_pure_expr_def] >>
  Cases_on `b` >> simp[supported_pure_expr_def]
QED

Theorem supported_iterator_no_halt:
  supported_iterator tops ty it n ==>
  !cx s t. eval_iterator cx it s <> (INR HaltException,t)
Proof
  Cases_on `it`
  >- (strip_tac >> drule supported_array_iterator_shape >> strip_tac >>
      gvs[] >> simp[Once evaluate_def] >> gen_tac >>
      irule bind_no_halt >> simp[] >> gen_tac >>
      irule bind_no_halt >> simp[] >> gen_tac >>
      irule bind_no_halt >> simp[] >> gen_tac >>
      irule bind_no_halt >> simp[]) >>
  strip_tac >> drule supported_range_endpoints_pure >> strip_tac >>
  gen_tac >> simp[Once evaluate_def] >>
  irule bind_no_halt >> reverse conj_tac
  >- (irule (cj 1 supported_pure_no_halt) >> metis_tac[]) >>
  gen_tac >> simp[] >> irule bind_no_halt >> simp[] >> gen_tac >>
  irule bind_no_halt >> reverse conj_tac
  >- (irule (cj 1 supported_pure_no_halt) >> metis_tac[]) >>
  gen_tac >> simp[] >> irule bind_no_halt >> simp[] >> gen_tac >>
  irule bind_no_halt >> simp[]
QED

Theorem loop_try_no_halt[local]:
  (!s t. f s <> (INR HaltException,t)) ==>
  !s t. try f handle_loop_exception s <> (INR HaltException,t)
Proof
  simp[try_def, AllCaseEqs()] >> rpt strip_tac >>
  Cases_on `e = ContinueException` >>
  Cases_on `e = BreakException` >>
  gvs[handle_loop_exception_def, return_def, raise_def] >> metis_tac[]
QED

Theorem eval_for_no_halt:
  !cx ss. (!s t. eval_stmts cx ss s <> (INR HaltException,t)) ==>
  !tyv nm vs s t. eval_for cx tyv nm ss vs s <> (INR HaltException,t)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> gen_tac >> Induct >>
  simp[Once evaluate_def] >> gen_tac >>
  irule ignore_bind_no_halt >> simp[] >>
  irule bind_no_halt >> reverse conj_tac
  >- (irule finally_no_halt >> simp[] >> irule loop_try_no_halt >>
      irule ignore_bind_no_halt >> simp[]) >>
  gen_tac >> Cases_on `v` >> simp[]
QED

Theorem supported_string_reason_no_halt[local]:
  !tops e. supported_string_reason tops e ==>
  !cx s t. eval_expr cx e s <> (INR HaltException,t)
Proof
  rpt gen_tac >> Cases_on `e` >>
  simp[supported_string_reason_def] >>
  rpt (disch_then strip_assume_tac) >> gen_tac
  >>~- ([`eval_expr cx (Literal _ l)`], simp[])
  >> irule (cj 1 supported_pure_no_halt) >> metis_tac[]
QED

Theorem supported_stmt_evaluation_no_halt:
  (!tops bindings st.
    supported_stmt tops bindings st /\
    ~supported_stmt_expr_exists expr_internal_call_root st ==>
    !cx s t. eval_stmt cx st s <> (INR HaltException,t)) /\
  (!tops bindings ss.
    supported_stmts tops bindings ss /\
    ~supported_stmts_expr_exists expr_internal_call_root ss ==>
    !cx s t. eval_stmts cx ss s <> (INR HaltException,t))
Proof
  ho_match_mp_tac supported_stmt_ind >>
  simp[supported_stmt_def, supported_stmt_expr_exists_def,
    supported_expr_exists_def] >> rpt conj_tac
  >- simp[Once evaluate_def]
  >- simp[Once evaluate_def, raise_def]
  >- simp[Once evaluate_def, raise_def]
  >- suspend "expr"
  >- simp[Once evaluate_def, raise_def]
  >- suspend "return"
  >- suspend "annassign"
  >- suspend "assign"
  >- suspend "augassign"
  >- suspend "append"
  >- suspend "if"
  >- suspend "assert"
  >- suspend "raise"
  >- suspend "log"
  >- suspend "for"
  >- simp[Once evaluate_def]
  >> suspend "cons"
QED

Resume supported_stmt_evaluation_no_halt[expr]:
  rpt gen_tac >> disch_then strip_assume_tac >> gen_tac >>
  simp[Once evaluate_def] >>
  irule bind_no_halt >> simp[] >>
  irule supported_expr_no_halt >> metis_tac[]
QED

Resume supported_stmt_evaluation_no_halt[return]:
  rpt gen_tac >> disch_then strip_assume_tac >> gen_tac >>
  simp[Once evaluate_def] >>
  irule bind_no_halt >> reverse conj_tac
  >- (irule supported_expr_no_halt >> metis_tac[]) >>
  gen_tac >> simp[] >> irule bind_no_halt >> simp[raise_def]
QED

Resume supported_stmt_evaluation_no_halt[annassign]:
  rpt gen_tac >> disch_then strip_assume_tac >> gen_tac >>
  simp[Once evaluate_def] >>
  irule bind_no_halt >> simp[] >> gen_tac >>
  irule bind_no_halt >> reverse conj_tac
  >- (irule supported_expr_no_halt >> metis_tac[]) >>
  gen_tac >> simp[] >> irule bind_no_halt >> simp[]
QED

Resume supported_stmt_evaluation_no_halt[assign]:
  rpt gen_tac >> disch_then strip_assume_tac >> gen_tac >>
  `!s t. eval_expr cx e s <> (INR HaltException,t)` by
    (irule supported_expr_no_halt >>
     gvs[supported_assignment_def] >> metis_tac[]) >>
  `!v s t. assign_tuple_targets cx target v s <> (INR HaltException,t)` by
    (irule supported_assignment_no_halt >> metis_tac[]) >>
  Cases_on `target`
  >- (`!s t. eval_target_place cx b s <> (INR HaltException,t)` by
        (gvs[supported_assignment_def, supported_assignment_exists_def]
         >- (irule supported_target_no_halt >> metis_tac[]) >>
         Cases_on `supported_target_info tops bindings b` >> gvs[] >>
         rename1 `supported_target_info _ _ _ = SOME pty` >>
         Cases_on `pty` >> gvs[] >>
         irule supported_info_target_no_halt >> metis_tac[]) >>
      simp[Once evaluate_def] >> irule bind_no_halt >> simp[] >>
      gen_tac >> irule bind_no_halt >> simp[] >>
      gen_tac >> irule bind_no_halt >> simp[]) >>
  simp[Once evaluate_def] >> irule bind_no_halt >> simp[] >>
  gen_tac >> irule bind_no_halt >> simp[]
QED
Resume supported_stmt_evaluation_no_halt[augassign]:
  rpt gen_tac >> disch_tac >> gen_tac >>
  `!s t. eval_target_place cx target s <> (INR HaltException,t)` by
    (pop_assum strip_assume_tac
     >- (irule supported_target_no_halt >> metis_tac[]) >>
     gvs[supported_aug_target_def] >>
     Cases_on `supported_target_info tops bindings target` >> gvs[] >>
     rename1 `supported_target_info _ _ _ = SOME pty` >>
     Cases_on `pty` >> gvs[] >>
     irule supported_info_target_no_halt >> metis_tac[]) >>
  gnvs[] >>
  simp[Once evaluate_def] >> irule bind_no_halt >> simp[] >>
  gen_tac >> irule bind_no_halt >> simp[] >>
  gen_tac >> irule bind_no_halt >> simp[] >> gen_tac >>
  irule bind_no_halt >> reverse conj_tac
  >- (irule supported_expr_no_halt >> metis_tac[]) >>
  gen_tac >> simp[bind_def, AllCaseEqs()] >>
  metis_tac[read_result_no_halt, primitive_no_halt, write_place_no_halt]
QED
Resume supported_stmt_evaluation_no_halt[append]:
  rpt gen_tac >> disch_then strip_assume_tac >> gen_tac >>
  simp[Once evaluate_def] >> irule bind_no_halt >> reverse conj_tac
  >- (irule supported_append_target_no_halt >> metis_tac[]) >>
  gen_tac >> simp[] >> irule bind_no_halt >> reverse conj_tac
  >- (irule (cj 1 supported_pure_no_halt) >> metis_tac[]) >>
  gen_tac >> simp[] >> irule bind_no_halt >> simp[]
QED
Resume supported_stmt_evaluation_no_halt[if]:
  rpt gen_tac >> rpt (disch_then strip_assume_tac) >> gen_tac >>
  simp[Once evaluate_def] >> irule bind_no_halt >> reverse conj_tac
  >- (irule (cj 1 supported_pure_no_halt) >> metis_tac[]) >>
  gen_tac >> simp[] >> irule ignore_bind_no_halt >> simp[] >>
  irule finally_no_halt >> simp[] >>
  irule switch_BoolV_no_halt >> metis_tac[]
QED
Resume supported_stmt_evaluation_no_halt[assert]:
  rpt gen_tac >> Cases_on `reason` >>
  simp[supported_assert_reason_def] >>
  disch_then strip_assume_tac >> gen_tac >>
  simp[Once evaluate_def] >> irule bind_no_halt >> reverse conj_tac
  >- (irule (cj 1 supported_pure_no_halt) >> metis_tac[])
  >- (gen_tac >> simp[] >> irule switch_BoolV_no_halt >> simp[raise_def])
  >- (irule (cj 1 supported_pure_no_halt) >> metis_tac[])
  >- (gen_tac >> simp[] >> irule switch_BoolV_no_halt >> simp[raise_def])
  >- (irule (cj 1 supported_pure_no_halt) >> metis_tac[]) >>
  gen_tac >> simp[] >> irule switch_BoolV_no_halt >> simp[] >>
  irule bind_no_halt >> reverse conj_tac
  >- (irule supported_string_reason_no_halt >> metis_tac[]) >>
  gen_tac >> simp[] >> irule bind_no_halt >> simp[] >>
  gen_tac >> irule bind_no_halt >> simp[raise_def]
QED
Resume supported_stmt_evaluation_no_halt[raise]:
  rpt gen_tac >> Cases_on `reason` >>
  simp[supported_raise_reason_def] >>
  disch_then strip_assume_tac >> gen_tac >>
  simp[Once evaluate_def, raise_def] >>
  irule bind_no_halt >> reverse conj_tac
  >- (irule supported_string_reason_no_halt >> metis_tac[]) >>
  gen_tac >> simp[] >> irule bind_no_halt >> simp[] >>
  gen_tac >> irule bind_no_halt >> simp[raise_def]
QED
Resume supported_stmt_evaluation_no_halt[log]:
  rpt gen_tac >> disch_then strip_assume_tac >> gen_tac >>
  gvs[supported_log_def] >> simp[Once evaluate_def] >>
  irule bind_no_halt >> reverse conj_tac
  >- (irule eval_exprs_no_halt >>
      drule (cj 2 supported_pure_no_halt) >>
      simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  gen_tac >> simp[] >> irule bind_no_halt >> simp[push_log_def,
    return_def, bind_def]
QED
Resume supported_stmt_evaluation_no_halt[for]:
  rpt gen_tac >> rpt (disch_then strip_assume_tac) >> gen_tac >>
  simp[Once evaluate_def] >> irule bind_no_halt >> simp[] >> gen_tac >>
  irule bind_no_halt >> reverse conj_tac
  >- (irule supported_iterator_no_halt >> metis_tac[]) >>
  gen_tac >> simp[] >> irule ignore_bind_no_halt >> simp[] >>
  irule eval_for_no_halt >> metis_tac[]
QED
Resume supported_stmt_evaluation_no_halt[cons]:
  rpt gen_tac >> rpt (disch_then strip_assume_tac) >> gen_tac >>
  simp[Once evaluate_def] >> irule ignore_bind_no_halt >> metis_tac[]
QED
Finalise supported_stmt_evaluation_no_halt

Theorem supported_stmts_no_halt:
  !tops bindings stmts cx es res es'.
    supported_stmts tops bindings stmts /\
    ~supported_stmts_expr_exists expr_internal_call_root stmts /\
    eval_stmts cx stmts es = (res,es') ==>
    res <> INR HaltException
Proof
  metis_tac[cj 2 supported_stmt_evaluation_no_halt]
QED
