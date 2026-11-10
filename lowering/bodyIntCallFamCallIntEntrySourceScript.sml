(* Source-only boundaries for the nested internal-call prefix. *)
Theory bodyIntCallFamCallIntEntrySource
Ancestors
  bodyIntCallSeamDefs stmtSimForRounds vyperInterpreter vyperState vyperCall
Libs
  monadsyntax

Theorem intcall_source_prefix:
  get_module_code cx NONE = SOME tops /\
  lookup_callable_function cx.in_deploy name tops =
    SOME (mut,F,args,[],ret,ss) /\ LENGTH es = LENGTH args ==>
  eval_expr cx (Call ann (IntCall (NONE,name)) es dflt) =
    do type_check (~MEM (NONE,name) cx.stk) "recursion";
       results <- eval_expr_results cx es;
       prev <- get_scopes;
       vs <- read_results cx results;
       penv <- lift_option_type (bind_arguments (get_tenv cx) args vs)
         "IntCall bind_arguments";
       rtv <- lift_option_type (evaluate_type (get_tenv cx) ret) "IntCall eval ret";
       push_function (NONE,name) penv cx;
       intcall_rest cx name mut ss prev rtv
    od
Proof
  strip_tac >> Cases_on `MEM (NONE,name) cx.stk`
  >- (simp[Once evaluate_def, type_check_def, vyperStateTheory.assert_def, ignore_bind_def, bind_def, raise_def, FUN_EQ_THM]) >>
  drule_all eval_expr_intcall_empty_defaults >> disch_then (qspecl_then [`ann`, `dflt`] SUBST1_TAC) >>
  simp[intcall_rest_def, type_check_def, vyperStateTheory.assert_def, bind_return,
       push_function_def, bind_assoc, ignore_bind_def, FUN_EQ_THM,
       bind_def, return_def]
QED

Theorem intcall_source_rest_admissible:
  ~MEM (NONE,name) cx.stk /\ get_module_code cx NONE = SOME tops /\
  lookup_callable_function cx.in_deploy name tops =
    SOME (mut,F,args,[],ret,ss) /\ LENGTH es = LENGTH args /\
  gas_admissible (eval_expr cx (Call ann (IntCall (NONE,name)) es dflt))
    expr_vv_res_ok start /\
  (!tail. eval_expr_results cx es (start with gas_obs := used ++ tail) =
    (INL results,mid with gas_obs := tail)) /\
  (!tail. read_results cx results (mid with gas_obs := tail) =
    (INL vs,mid with gas_obs := tail)) /\
  bind_arguments (get_tenv cx) args vs = SOME penv /\
  evaluate_type (get_tenv cx) ret = SOME rtv ==>
  gas_admissible (intcall_rest cx name mut ss mid.scopes rtv)
    expr_vv_res_ok (mid with <|scopes := [penv]; gas_obs := []|>)
Proof
  strip_tac >> drule_all intcall_source_prefix >>
  disch_then (qspecl_then [`dflt`, `ann`] assume_tac) >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  simp[gasContextTheory.gas_admissible_def] >>
  disch_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspec_then `used ++ gs` mp_tac) >>
  simp[type_check_def, vyperStateTheory.assert_def, ignore_bind_def,
       bind_def, return_def, get_scopes_def, lift_option_type_def,
       push_function_def] >>
  metis_tac[]
QED
