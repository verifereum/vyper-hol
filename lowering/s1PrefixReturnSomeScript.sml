(* A valued return preserves the request prefix of its value expression. *)
Theory s1PrefixReturnSome
Ancestors
  s1PrefixDefs s1PrefixOfVV externalReturnPrefix stmtSimReturn
  stmtLoweringMono exprLoweringProps gasShadowCompileStmtHelpers gasShadowState
  loweringPosts compileEnv fragExec stmtLowering vyperInterpreter vyperState pair

Theorem compile_return_some_frag_prefix:
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ret_ty e es ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (Return (SOME e)))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (Return (SOME (gas_shadow_expr e))))
    (eval_stmt cx (Return (SOME e))) es
Proof
  strip_tac >> pure_rewrite_tac[stmt_frag_prefix_def, stmt_frag_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `lower_value compile_expr cenv ret_ty e sa` >>
  rename1 `lower_value compile_expr cenv ret_ty e sa = (op,sm)` >>
  Cases_on `lower_value compile_expr (gas_shadow_env T cenv) ret_ty
              (gas_shadow_expr e) shadow_sa` >>
  rename1 `lower_value compile_expr _ ret_ty (gas_shadow_expr e) shadow_sa =
             (shadow_op,shadow_sm)` >>
  `op = shadow_op /\ gas_shadow_state sm shadow_sm` by
    (`gas_shadow_compiles (lower_value compile_expr cenv ret_ty e)
        (lower_value compile_expr (gas_shadow_env T cenv) ret_ty (gas_shadow_expr e))`
       by irule gas_shadow_stmt_lower_value_env >>
     pop_assum (qspecl_then [`sa`, `shadow_sa`] mp_tac o
       REWRITE_RULE [gas_shadow_compiles_def]) >> simp[]) >>
  qpat_x_assum `op = shadow_op` (SUBST_ALL_TAC o SYM) >>
  `cs_extends sm sb /\ cs_extends shadow_sm shadow_sb` by
    metis_tac[return_value_code_prefix] >>
  `cs_extends sa sm /\ cs_extends shadow_sa shadow_sm` by
    (conj_tac
     >- (qspecl_then [`cenv`, `ret_ty`, `e`, `sa`] mp_tac
           (cj 2 ci_mono_compile_expr_sa) >> simp[ci_mono_def]) >>
     qspecl_then [`gas_shadow_env T cenv`, `ret_ty`, `gas_shadow_expr e`, `shadow_sa`]
       mp_tac (cj 2 ci_mono_compile_expr_sa) >> simp[ci_mono_def]) >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func` by
    metis_tac[fn_has_code_split] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[return_forced_admissible] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x` by fs[ret_pc_ok_def] >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_prefix_def, expr_sim_full_pre_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `shadow_sm`,
                           `op`, `s0`, `G0`, `tn0`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  `!qe. SND (eval_stmt cx (Return (SOME e)) qe) =
        SND (bind (eval_expr cx e) (read_result cx) qe)` by
    (gen_tac >> simp[eval_return_forced, SF boolSimps.ETA_ss] >>
     Cases_on `bind (eval_expr cx e) (read_result cx) qe` >>
     rename1 `_ = (res,ee)` >> Cases_on `res` >>
     simp[bind_def, raise_def]) >>
  metis_tac[gas_prefix_full_state_cong]
QED
