(* Static cuts and source callbacks for strict bytestring comparisons. *)
Theory bodyBopBytestringPrepareMods
Ancestors
  bodyFullPredsMods exprBodyPreProps exprSimFullBundleProps
  bodyPtrBopHashSuffix bytestringHashProps exprLoweringProps
  gasShadowCompilePure fragExec exprBopSimProps gasContext
  exprSimDefs exprSimHypsDefs vyperTypeInvariants vyperTypeSystem
  vyperTypeBuiltins vyperTypeCallGraph vyperTypeCallStackSoundness
  supportedExprTraverse allocLimits list loweringShapeDefs vyperState
Libs monadsyntax

Theorem bop_bytestring_child_pres_mods:
  expr_body_pre_mods mods cenv cx env (Builtin ann (Bop bop) [e1;e2]) es ==>
  expr_body_pre_mods mods cenv cx env e1 es /\
  !mid. expr_sim_inv_mods mods cenv cx env mid ==>
        expr_body_pre_mods mods cenv cx env e2 mid
Proof
  simp[expr_body_pre_mods_def, Once well_typed_expr_def, well_typed_builtin_app_def,
       int_calls_expr_def, byte_widths_expr_def, alloc_limits_expr_def,
       expr_has_evm_run_thm, supported_expr_exists_def, EVERY_APPEND] >>
  strip_tac >>
  drule_then assume_tac call_evaluation_safe_append_left >>
  drule_then assume_tac call_evaluation_safe_append_right >>
  fs[constSubstCorrectTheory.frame_well_typed_exprs_cons]
QED

Theorem bop_bytestring_child_sim_mods:
  body_expr_full_ok_mods mods exps cx e /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env e es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type e) e es
Proof
  strip_tac >> qpat_x_assum `body_expr_full_ok_mods _ _ _ e`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type e) e es /\
   expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type e) e es` by
    (first_x_assum irule >> simp[] >> conj_tac
     >- (qexistsl_tac [`src`,`tops`] >> simp[]) >> qexists_tac `env` >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Theorem bop_bytestring_forced_head:
  gas_admissible (bind src (next : value -> evaluation_state -> value evaluation_result)) expr_res_ok es ==>
  gas_admissible (src : evaluation_state -> value evaluation_result) expr_res_ok es
Proof
  simp[gas_admissible_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  first_x_assum irule >> qexistsl_tac [`ee`,`gs`] >> simp[bind_def]
QED

val cut = ``(case bytestring_literal_hash e of
  NONE => compile_bytestring_hash (FST (lower_value compile_expr cenv (expr_type e) e sa))
    (SND (lower_value compile_expr cenv (expr_type e) e sa))
  | SOME digest => (Lit digest,sa))``;

Theorem bop_bytestring_child_cut_mods:
  ^cut = (h,sz) /\ gas_shadow_state sa shadow_sa /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_inst_ids_distinct func /\ fn_has_code sa sz func /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  (!m cb. bytestring_literal_hash e = NONE /\
     lower_value compile_expr cenv (expr_type e) e sa = (m,cb) ==>
     ?shadow_cb. lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e) shadow_sa = (m,shadow_cb) /\ gas_shadow_state cb shadow_cb) /\
  (!m cb. bytestring_literal_hash (gas_shadow_expr e) = NONE /\
      lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
        (gas_shadow_expr e) shadow_sa = (m,cb) ==> fn_has_code shadow_sa cb shadow_func) ==>
  (case bytestring_literal_hash e of
     SOME digest => h = Lit digest /\ sz = sa
   | NONE => ?m cb shadow_cb.
       lower_value compile_expr cenv (expr_type e) e sa = (m,cb) /\
       lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e)
         shadow_sa = (m,shadow_cb) /\
       expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,cb,shadow_sa,shadow_cb) /\
       compile_bytestring_hash m cb = (h,sz) /\ fn_has_code cb sz func /\
       gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es) /\
  sa.cs_next_id <= sz.cs_next_id
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `bytestring_literal_hash e` >> fs[] >>
  Cases_on `lower_value compile_expr cenv (expr_type e) e sa` >>
  fs[] >> rename1 `lower_value _ _ _ _ _ = (m,cb)` >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule bop_hash_compile_layout >> strip_tac >>
  reverse conj_tac
  >- (drule compile_bytestring_hash_shape >> simp[ci_mono_def] >> decide_tac) >>
  drule_all_then strip_assume_tac fn_has_code_split >>
  simp[expr_sim_full_code_def]
QED
