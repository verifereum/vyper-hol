(* Request-prefix cases for the body induction. *)
Theory s1PrefixCases
Ancestors
  s1PrefixDefs s1PrefixPreds s1PrefixReturnSome s1PrefixReturnNone s1PrefixExits
  s1PrefixStmtZero s1PrefixExprStmt s1PrefixNames s1PrefixLiteralWord
  s1PrefixMsgGas s1PrefixFrame stmtExprAllocationPreProps bodyInvCodeProps
  compileUnit vyperStorageTrace vyperState alist
  allocLimits allocLimitsProps bodyExprPreFacts bodySim
  exprSimHypsDefs gasContext gasShadow supportedExprs supportedStmts
  supportedExprTraverse supportedStmtTraverse
  vyperAST vyperContext vyperInterpreter vyperTypeSystem vyperTypeCallGraph

Theorem body_return_case_prefix:
  !cx e.
    body_expr_full_ok cx e /\ body_expr_prefix_ok cx e ==>
    body_stmt_prefix_ok cx (Return (SOME e))
Proof
  rw[body_stmt_prefix_ok_def, gas_shadow_stmt_def] >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  `~supported_expr_exists (const_name_root cx) e` by
    (drule_all body_inv_stmt_const_name_free >>
     simp[supported_stmt_expr_exists_def, supported_expr_exists_def]) >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (irule (Q.SPECL [`cenv`, `cx`, `env`, `e`, `es`, `[]`]
              stmt_expr_body_pre) >>
     gvs[type_stmt_def, stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
         supported_expr_exists_def, int_calls_stmt_def, int_calls_expr_def,
         body_inv_def]
     >- (irule allocLimitsPropsTheory.alloc_limits_expr_not_extcode >>
         qexists_tac `cenv` >>
         fs[alloc_limits_stmt_def, alloc_limits_expr_def]) >>
     metis_tac[]) >>
  irule compile_return_some_frag_prefix >>
  qpat_x_assum `body_expr_prefix_ok cx e`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
  first_x_assum (qspecl_then [`DF`, `lo`, `d`, `PG`, `tops`, `ctx`,
    `shadow_ctx`, `func`, `shadow_func`, `cenv`, `env`, `ret_ty`, `es`] mp_tac) >>
  simp[]
QED

Theorem body_return_none_case_prefix:
  !cx. body_stmt_prefix_ok cx (Return NONE)
Proof
  simp[body_stmt_prefix_ok_def, gas_shadow_stmt_def,
       compile_return_none_frag_prefix]
QED

Theorem body_break_case_prefix:
  !cx. body_stmt_prefix_ok cx Break
Proof
  simp[body_stmt_prefix_ok_def, compile_loop_jump_frag_prefix]
QED

Theorem body_continue_case_prefix:
  !cx. body_stmt_prefix_ok cx Continue
Proof
  simp[body_stmt_prefix_ok_def, compile_loop_jump_frag_prefix]
QED

Theorem body_raise_bare_case_prefix:
  !cx. body_stmt_prefix_ok cx (Raise RaiseBare)
Proof
  simp[body_stmt_prefix_ok_def, compile_raise_frag_prefix]
QED

Theorem body_raise_unreachable_case_prefix:
  !cx. body_stmt_prefix_ok cx (Raise RaiseUnreachable)
Proof
  simp[body_stmt_prefix_ok_def, compile_raise_frag_prefix]
QED

Theorem body_pass_case_prefix:
  !cx. body_stmt_prefix_ok cx Pass
Proof
  simp[body_stmt_prefix_ok_def, gas_shadow_stmt_def, compile_pass_frag_prefix]
QED

Theorem body_stmts_nil_case_prefix:
  !cx. body_stmts_prefix_ok cx []
Proof
  simp[body_stmts_prefix_ok_def, stmt_frag_nil_prefix]
QED

Theorem body_expr_stmt_case_prefix:
  !cx e.
    body_expr_full_ok cx e /\
    body_expr_prefix_ok cx e ==>
    body_stmt_prefix_ok cx (Expr e)
Proof
  rw[body_stmt_prefix_ok_def] >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  `well_typed_expr env e` by gvs[type_stmt_def] >>
  qpat_assum `body_inv tops ctx cenv cx`
    (assume_tac o MATCH_MP bodyInvCodePropsTheory.contract_inv_cenv_modules
      o MATCH_MP body_inv_contract) >>
  `expr_body_pre cenv cx env e es` by
    (mp_tac (Q.INST [`tops` |-> `tops`, `ctx` |-> `ctx`, `s` |-> `Expr e`]
       stmtExprAllocationPrePropsTheory.body_inv_stmt_expr_pre_singleton) >>
     simp[supported_stmt_expr_exists_def, int_calls_stmt_def] >>
     disch_then irule >>
     `~is_extcode e` by
       (irule allocLimitsPropsTheory.alloc_limits_expr_not_extcode >>
        qexists_tac `cenv` >> fs[stmt_exprs_ok_def, allocLimitsTheory.alloc_limits_stmt_def]) >>
     mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`, `exps` |-> `[]`, `calls` |-> `[]`]
       stmt_expr_body_pre_main_mods) >>
     gvs[compileUnitTheory.main_module_def, alistTheory.ALOOKUP_def,
         stmt_exprs_ok_flat, supported_stmt_expr_exists_def, int_calls_stmt_def]) >>
  irule compile_expr_stmt_frag_ok_prefix >>
  qpat_x_assum `body_expr_prefix_ok cx e`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
  first_x_assum (qspecl_then [`DF`, `lo`, `d`, `PG`, `tops`, `ctx`,
    `shadow_ctx`, `func`, `shadow_func`, `cenv`, `env`, `expr_type e`, `es`] mp_tac) >>
  simp[]
QED

Theorem body_msg_gas_prefix_case:
  !cx ann args.
    body_expr_prefix_ok cx (Builtin ann (Env MsgGas) args)
Proof
  rw[body_expr_prefix_ok_def] >>
  `args = [] /\ ann = env_item_type MsgGas` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  gvs[compile_msg_gas_sim_prefix]
QED

Theorem body_expr_prefix_ok_leaf:
  !cx e.
    (?a id. e = Name a id) \/ (?a nsid. e = TopLevelName a nsid) \/
    (?a nsid mid. e = FlagMember a nsid mid) \/ (?a l. e = Literal a l) ==>
    body_expr_prefix_ok cx e
Proof
  rpt strip_tac >> gvs[body_expr_prefix_ok_def, name_value_prefix, name_vv_prefix,
                       toplevel_name_value_prefix, toplevel_name_vv_prefix,
                       literal_word_value_prefix, literal_vv_prefix] >>
  rw[expr_sim_prefix_def, expr_vv_sim_prefix_def,
     expr_sim_full_pre_def, expr_vv_sim_full_pre_def] >>
  irule gas_prefix_full_no_outcome >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, Once evaluate_def] >>
  PairCases_on `nsid` >>
  simp[lookup_flag_mem_def] >> rpt gen_tac >> rpt BasicProvers.TOP_CASE_TAC >>
  simp[bind_def, read_result_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[]
QED
