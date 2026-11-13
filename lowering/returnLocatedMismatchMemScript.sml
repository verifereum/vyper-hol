(* The compiled value-view prefix of a Return, and impossible located posts. *)
Theory returnLocatedMismatchMem
Ancestors
  returnNoNormalMem externalReturnPrefix exprSimMemDefs exprSimMemorySource
  exprSimUnwrap exprLoweringProps stmtSimReturn stmtSimDefs loweringPosts
  stmtLowering exprLowering compileEnv fragExec

Theorem return_compile_expr_code_prefix:
  stmt_env cenv lctx ret (Return (SOME e)) sa = (cenv',sb) /\
  compile_expr cenv ret e sa = (vv,sm) /\ fn_has_code sa sb func ==>
  fn_has_code sa sm func
Proof
  strip_tac >>
  Cases_on `unwrap_value cenv vv sm` >> rename1 `_ = (op,s1)` >>
  `lower_value compile_expr cenv ret e sa = (op,s1)` by
    simp[lower_value_def, comp_bind_def] >>
  drule_all return_value_code_prefix >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >>
  drule (cj 1 compile_expr_grows) >> strip_tac >>
  metis_tac[fn_has_code_split, cs_extends_trans]
QED

Theorem return_located_mismatch_mem:
  expr_vv_sim_mem ctx func cenv cx ret e es /\
  (!sa vv sm. compile_expr cenv ret e sa = (vv,sm) ==>
    ?declared p. vv = LocatedValue declared p /\
      declared <> post_value_type cenv e /\
      ~(is_bytestring_type (post_value_type cenv e) /\ is_bytestring_type declared)) ==>
  stmt_frag_mem d ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ret (Return (SOME e)))
    (eval_stmt cx (Return (SOME e))) es
Proof
  strip_tac >> simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `compile_expr cenv ret e sa` >> rename1 `_ = (vv,sm)` >>
  `fn_has_code sa sm func` by metis_tac[return_compile_expr_code_prefix] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[return_forced_admissible, forced_expr_admissible_raw] >>
  qpat_x_assum `!sa vv sm. _` drule >> strip_tac >> gvs[] >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _` mp_tac >>
  simp[expr_vv_sim_mem_def] >>
  disch_then (qspecl_then [`sa`, `sm`, `LocatedValue declared p`, `s0`] mp_tac) >>
  simp[] >> disch_tac >>
  irule return_no_normal_vv_outcome_mem >>
  qexists_tac `\raw ee t.
    vv_post ctx func cenv cx e es sa sm s0 ee raw (LocatedValue declared p) t /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` >>
  gvs[vv_post_def, vv_holds_def]
QED
