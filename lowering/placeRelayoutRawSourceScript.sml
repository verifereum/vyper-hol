(* Raw internal-call results can be read after effectful target evaluation. *)
Theory placeRelayoutRawSource
Ancestors
  exprSimIfExpCompat exprSimHypsDefs exprSimSource
  vyperTypeSystem vyperTypeInvariants vyperInterpreter vyperState
  exprLowering compileEnv

Theorem internal_call_delayed_read:
  eval_expr cx (Call ty (IntCall fid) args drv) es = (INL pv,ee) ==>
  ?v. pv = Value v /\ !ff. read_result cx pv ff = (INL v,ff)
Proof
  Cases_on `fid` >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def,
       raise_def, AllCaseEqs()] >> rpt strip_tac >> gvs[read_result_def, return_def]
QED

Theorem strict_widened_rhs_delayed_read:
  expr_body_pre cenv cx env e es /\
  ~(lowered_value_type cenv e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type cenv e) /\
    arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
  !st pv ee. eval_expr cx e st = (INL pv,ee) ==>
  ?v. pv = Value v /\ !ff. read_result cx pv ff = (INL v,ff)
Proof
  strip_tac >>
  drule expr_body_pre_var_types_well_formed >> strip_tac >>
  `well_typed_expr env e /\
   sfields_tenv_consistent cenv.ce_struct_fields env.type_defs` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  drule ifexp_lowered_type_classify >>
  disch_then (qspec_then `cenv` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >> gvs[] >>
  metis_tac[internal_call_delayed_read]
QED
