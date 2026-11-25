Theory s1PrefixAnnAssignEmptyRhs
Ancestors
  s1PrefixFrame s1PrefixOfVV stmtLowering vyperInterpreter vyperContext
  vyperStorageTrace vyperState vyperAST vyperValue list
Libs
  monadsyntax

Theorem eval_empty_rhs_state[local]:
  is_empty_value_expr e ==> SND (eval_expr cx e st) = st
Proof
  strip_tac >> Cases_on `e` >> gvs[is_empty_value_expr_def]
  >~ [`Literal ann lit`]
  >- simp[Once evaluate_def, return_def]
  >~ [`TypeBuiltin ann tb target args`]
  >- (Cases_on `tb` >> gvs[is_empty_value_expr_def] >>
      Cases_on `args` >>
      simp[Ntimes evaluate_def 2, type_builtin_args_length_ok_def,
           type_check_def, assert_def, ignore_bind_def, bind_def, raise_def,
           return_def, evaluate_type_builtin_def, lift_sum_def] >>
      Cases_on `evaluate_type (get_tenv cx) target` >>
      simp[lift_sum_def, bind_def, return_def, raise_def]) >>
  rename1 `Builtin ann bt args` >> Cases_on `bt` >>
  gvs[is_empty_value_expr_def] >>
  rename1 `MakeArray et bd` >> Cases_on `et` >> gvs[is_empty_value_expr_def] >>
  Cases_on `args` >> gvs[is_empty_value_expr_def] >>
  rename1 `MakeArray (SOME et) bd` >>
  simp[Ntimes evaluate_def 2, builtin_args_length_ok_def,
       type_check_def, assert_def, ignore_bind_def, bind_def, return_def,
       get_accounts_def, evaluate_builtin_def, is_self_codesize_def,
       precompile_call_success_def, precompile_builtin_def] >>
  Cases_on `compatible_bound bd 0` >>
  Cases_on `evaluate_type (get_tenv cx) et` >>
  simp[bind_def, return_def, raise_def, lift_sum_def]
QED

Theorem annassign_empty_rhs_prefix:
  is_empty_value_expr e /\ ~s.vs_halted ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
Proof
  simp[gas_prefix_full_bind_read_result] >> strip_tac >>
  irule gas_prefix_full_no_outcome >> simp[evaluate_storage_trace_frame] >>
  rpt strip_tac >>
  `SND (eval_expr cx e (es with gas_obs := gobs)) = es with gas_obs := gobs` by
    simp[eval_empty_rhs_state] >>
  gvs[]
QED
