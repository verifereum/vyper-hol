(* Expression and target boundaries used by statement compilation. *)
Theory gasShadowCompileStmtHelpers
Ancestors
  gasShadowCompileStmtOps gasShadowCompileStmtBase gasShadowCompile
  gasShadowCompileHelpers gasShadowCenv gasShadowCenvStmt gasShadowCompileLiteral gasShadowCompileContext gasShadow gasShadowState
  stmtLowering exprLowering compileEnv vyperAST list

Theorem gas_shadow_stmt_compile_expr:
  gas_shadow_compiles (compile_expr cenv ty e)
    (compile_expr (gas_shadow_cenv cenv) ty (gas_shadow_expr e))
Proof
  qspecl_then [`cenv`, `ty`, `e`, `T`] mp_tac (cj 1 gas_shadow_compile_expr) >> simp[]
QED

Theorem gas_shadow_stmt_lower_value:
  gas_shadow_compiles (lower_value compile_expr cenv ty e)
    (lower_value compile_expr (gas_shadow_cenv cenv) ty (gas_shadow_expr e))
Proof
  `!sh. gas_shadow_compiles (lower_value compile_expr cenv ty e)
     (lower_value (\c. compile_expr (gas_shadow_cenv c)) cenv ty
        (if sh then gas_shadow_expr e else e))`
    suffices_by (disch_then (qspec_then `T` mp_tac) >> simp[gsc_shift_thms]) >>
  gen_tac >> irule gas_shadow_compiles_lower_value >>
  simp[cj 1 gas_shadow_compile_expr]
QED

Theorem gas_shadow_stmt_get_target_ptr:
  gas_shadow_compiles (compile_get_target_ptr compile_expr cenv bt)
    (compile_get_target_ptr compile_expr (gas_shadow_cenv cenv) (gas_shadow_target bt))
Proof
  `!target ce sh. gas_shadow_compiles (compile_get_target_ptr compile_expr ce target)
     (compile_get_target_ptr (\c. compile_expr (gas_shadow_cenv c)) ce
        (if sh then gas_shadow_target target else target))`
    suffices_by (disch_then (qspecl_then [`bt`, `cenv`, `T`] mp_tac) >>
                 simp[gsc_shift_thms]) >>
  irule gas_shadow_compiles_get_target_ptr >>
  simp[cj 1 gas_shadow_compile_expr]
QED

Theorem gas_shadow_compile_log_eval_all:
  !es. gas_shadow_compiles (compile_log_eval_all cenv es)
    (compile_log_eval_all (gas_shadow_cenv cenv) (MAP gas_shadow_expr es))
Proof
  Induct >> simp[compile_log_eval_all_def, gas_shadow_compiles_bind,
    gas_shadow_compiles_return, gas_shadow_stmt_lower_value]
QED

Theorem gas_shadow_stmt_compile_expr_same[local]:
  gas_shadow_compiles (compile_expr cenv ty e)
    (compile_expr (gas_shadow_cenv cenv) ty e)
Proof
  qspecl_then [`cenv`, `ty`, `e`, `F`] mp_tac (cj 1 gas_shadow_compile_expr) >> simp[]
QED

Theorem gas_shadow_compile_reason_message:
  gas_shadow_compiles (compile_reason_message cenv e)
    (compile_reason_message (gas_shadow_cenv cenv) (gas_shadow_expr e))
Proof
  Cases_on `e` >>
  simp[gas_shadow_expr_def, compile_reason_message_def] >>
  simp[GSYM gas_shadow_expr_def, gas_shadow_stmt_compile_expr,
       gas_shadow_stmt_compile_expr_same] >>
  Cases_on `t` >> Cases_on `l` >>
  simp[compile_reason_message_def, gas_shadow_stmt_compile_expr_same] >>
  Cases_on `b` >>
  simp[compile_reason_message_def, gas_shadow_stmt_compile_expr_same,
       gas_shadow_compiles_bind, gas_shadow_compiles_return,
       gas_shadow_compiles_bytelike_literal]
QED

Theorem gas_shadow_compile_tuple_store_all:
  !tys targets vals.
  gas_shadow_compiles (compile_tuple_store_all cenv tys targets vals)
    (compile_tuple_store_all (gas_shadow_cenv cenv) tys
       (MAP gas_shadow_assignment targets) vals)
Proof
  Induct >> Cases_on `targets` >> Cases_on `vals` >>
  simp[compile_tuple_store_all_def, gas_shadow_compiles_return] >>
  rename1 `at::ats` >> Cases_on `at` >>
  simp[gas_shadow_assignment_def, compile_tuple_store_all_def,
       comp_ignore_bind_def, gas_shadow_compiles_bind,
       gas_shadow_compiles_emit_void] >> gen_tac >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- simp[gas_shadow_stmt_get_target_ptr] >>
  gen_tac >>
  rpt (ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- (rpt IF_CASES_TAC >>
           simp[gas_shadow_compiles_return, gas_shadow_compiles_store_at_loc,
                gas_shadow_compiles_emit_void, gas_shadow_compiles_assign_value]) >>
       gen_tac) >> simp[]
QED

Theorem gas_shadow_compile_tuple_unpack:
  gas_shadow_compiles (compile_tuple_unpack cenv ty stage targets src)
    (compile_tuple_unpack (gas_shadow_cenv cenv) ty stage
       (MAP gas_shadow_assignment targets) src)
Proof
  simp[compile_tuple_unpack_def] >>
  qmatch_goalsub_abbrev_tac `EXISTS _ etys` >>
  IF_CASES_TAC
  >- simp[gas_shadow_compiles_emit_inst] >> simp[] >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (rpt IF_CASES_TAC >>
      simp[comp_ignore_bind_def, gas_shadow_compiles_bind,
           gas_shadow_compiles_return, gas_shadow_compiles_alloc_buffer,
           gas_shadow_compiles_emit_void]) >>
  gen_tac >> ho_match_mp_tac gas_shadow_compiles_bind >>
  simp[gas_shadow_compiles_tuple_load_all, gas_shadow_compile_tuple_store_all]
QED
