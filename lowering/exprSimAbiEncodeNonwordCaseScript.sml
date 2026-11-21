Theory exprSimAbiEncodeNonwordCase
Ancestors
  abiBuiltinEncodeCode builtinAbi emitHelper compileEnv
  vyperInterpreter vyperState exprSimSource exprSimWordArgs exprLoweringProps vyperAST list
  fragExec vyperContext loweringPosts loweringStateRelDefs venomState

Theorem abi_encode_endpoint_nonempty:
  lower_abi_encode mid maxlen encode sa = (out,sb) ==>
  sb.cs_current_insts <> []
Proof
  strip_tac >> drule lower_abi_encode_trace >> strip_tac >>
  qpat_x_assum `abi_builtin_encode_finish _ _ _ _ = _` mp_tac >>
  simp[abi_builtin_encode_finish_def] >>
  IF_CASES_TAC >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

Theorem eval_expr_singleton_type_builtin_cases:
  type_builtin_args_length_ok tb 1 /\
  eval_expr cx (TypeBuiltin ann tb ty [e]) es = (res,es') ==>
  (?exc. bind (eval_expr cx e) (read_result cx) es = (INR exc,es') /\
         res = INR exc) \/
  ?v. bind (eval_expr cx e) (read_result cx) es = (INL v,es') /\
    res = (case evaluate_type_builtin cx tb ty [expr_type e] [v] of
             INL w => INL (Value w) | INR err => INR (Error err))
Proof
  strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def] >>
  Cases_on `eval_exprs cx [e] es` >>
  rename1 `eval_exprs cx [e] es = (rr,es1)` >>
  drule eval_exprs_cons_cases >> strip_tac >> gvs[eval_exprs_nil] >>
  simp[bind_def, return_def, lift_sum_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[bind_def, AllCaseEqs()] >>
  Cases_on `evaluate_type_builtin cx tb ty [expr_type e] [v]` >>
  gvs[return_def, raise_def] >> metis_tac[]
QED

Theorem eval_expr_singleton_type_builtin_action:
  type_builtin_args_length_ok tb 1 ==>
  eval_expr cx (TypeBuiltin ann tb ty [e]) =
  bind (bind (eval_expr cx e) (read_result cx))
    (\v es. ((case evaluate_type_builtin cx tb ty [expr_type e] [v] of
                INL w => INL (Value w) | INR err => INR (Error err)), es))
Proof
  strip_tac >> pure_rewrite_tac[FUN_EQ_THM] >> gen_tac >>
  Cases_on `eval_expr cx (TypeBuiltin ann tb ty [e]) x` >>
  drule_all eval_expr_singleton_type_builtin_cases >> strip_tac >>
  gvs[bind_def]
QED

Theorem abi_encode_vv_post_pointer_cong:
  p.ptr_operand = q.ptr_operand /\ p.ptr_location = q.ptr_location ==>
  (vv_post (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx e es sa sb s0 es' tv (LocatedValue ty p) s <=>
   vv_post H ctx func ce cx e es sa sb s0 es' tv (LocatedValue ty q) s)
Proof
  simp[vv_post_def, vv_holds_def, vv_at_def, vv_own_def, vv_place_ptr_def]
QED

Theorem abi_encode_vv_post_fields_transport:
  vv_post (H0:(bool # bytes32 # type_value) list # num list) ctx func ce cx e es sa sb s0 es' tv
    (LocatedValue ty p) u /\
  p.ptr_location = LocMemory /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx es' s /\
  storage_well_formed_on cx es' (FST H) /\
  u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
  u.vs_requests = s.vs_requests /\ u.vs_call_ctx = s.vs_call_ctx ==>
  vv_post H ctx func ce cx e es sa sb s0 es' tv (LocatedValue ty p) u
Proof
  rewrite_tac[vv_post_def, stmt_state_rel_def,
              loweringStateRelDefsTheory.state_rel_def] >>
  strip_tac >> fs[] >>
  gvs[loweringStateRelDefsTheory.storage_rel_def,
      loweringStateRelDefsTheory.transient_rel_def,
      loweringStateRelDefsTheory.accounts_rel_def,
      venomStateTheory.contract_storage_def,
      venomStateTheory.contract_transient_def] >>
  metis_tac[]
QED
