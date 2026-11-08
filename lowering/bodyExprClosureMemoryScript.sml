(* Reachability-aligned recursive expression memory closure. *)
Theory bodyExprClosureMemory
Ancestors
  bodyNameMemory
  bodyNotFlagMemory bodyNotBytesMemory bodyNotUintMemory
  bodyAbsMemory bodyNotBoolMemory
  exprSimSource
  bodyMemoryPreds bodyMemoryDefs bodyIfExpMemory exprSimOperators exprSimHyps
  exprLoweringProps vyperInterpreter vyperState
  bodyLiteralMemory bodyLiteralForceMemory bodyAllocMemory bodyFieldMemory vyperTypeCallGraph
  bodyUnopMemory bodyNegMemory bodyCalldataMemory bodyEnvMemory bodyFlagMemberMemory
  vyperTyping vyperValue vyperAST vyperTypeSystem loweringPosts

Theorem body_ifexp_word_mem_case:
  !cx t c a b. is_word_type t /\
    (!s tv s'. eval_expr cx c s = (INL tv,s') ==> body_expr_mem_ok cx a) /\
    (!s tv s'. eval_expr cx c s = (INL tv,s') ==> body_expr_mem_ok cx b) /\
    body_expr_mem_ok cx c ==> body_expr_mem_ok cx (IfExp t c a b)
Proof
  rpt gen_tac >> strip_tac >> pure_rewrite_tac[body_expr_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  drule expr_body_pre_ifexp >> strip_tac >>
  `expr_sim_mem ctx func cenv cx (BaseT BoolT) c es` by
    metis_tac[body_expr_mem_ok_def] >>
  `!tv es1. (do result <- eval_expr cx c; read_result cx result od) es = (INL tv,es1) ==>
     expr_sim_mem ctx func cenv cx ty a es1 /\
     expr_sim_mem ctx func cenv cx ty b es1` by
    (rpt gen_tac >> strip_tac >>
     drule_all expr_body_pre_eval >> strip_tac >>
     drule eval_expr_read_INL >> strip_tac >>
     metis_tac[body_expr_mem_ok_def]) >>
  conj_tac
  >- (irule compile_ifexp_word_sim_mem >> simp[] >>
      metis_tac[compile_expr_grows]) >>
  pure_rewrite_tac[expr_vv_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  `expr_read_res_ok cx es' res` by
    metis_tac[expr_body_pre_ifexp_word_readable] >>
  irule fragExecMemTheory.frag_exec_mem_weaken >>
  qexists_tac `\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\ alloca_history func s` >>
  qexists_tac `\s. (?tv. res = INL tv /\
    vv_post ctx func cenv cx (IfExp t c a b) es sa sb s0 es' tv vv s) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s` >>
  qexists_tac `expr_exit res` >> simp[] >>
  irule compile_ifexp_vv_sim_mem >> simp[post_value_type_word] >>
  conj_tac >- metis_tac[compile_expr_grows] >> qexists_tac `ty` >>
  simp[] >> metis_tac[compile_expr_grows]
QED

Theorem body_attribute_name_mem_case:
  !cx ann sid id fld.
    body_expr_mem_ok cx (Attribute ann (Name (StructT sid) id) fld)
Proof
  pure_rewrite_tac[body_expr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  metis_tac[compile_attribute_name_body_sim_mem,
            compile_attribute_name_body_vv_sim_mem]
QED

Theorem body_not_bool_mem_case:
  !cx ann e. expr_type e = BaseT BoolT /\ body_expr_mem_ok cx e ==>
    body_expr_mem_ok cx (Builtin ann Not [e])
Proof
  rpt gen_tac >> strip_tac >> pure_rewrite_tac[body_expr_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `ann = BaseT BoolT` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  gvs[] >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule expr_body_pre_builtin_arg >> simp[] >>
     qexistsl_tac [`BaseT BoolT`, `[e]`, `Not`, `es`] >> simp[]) >>
  `expr_sim_mem ctx func cenv cx (BaseT BoolT) e es` by
    metis_tac[body_expr_mem_ok_def] >>
  `!v es1. (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es1) ==>
      ?b. v = BoolV b` by
    (rpt gen_tac >> strip_tac >>
     `word_value_type (expr_type e)` by simp[word_value_type_def] >>
     drule_all expr_body_pre_word_result >> strip_tac >>
     gvs[evaluate_type_def] >> Cases_on `v` >> gvs[value_has_type_def]) >>
  metis_tac[compile_not_bool_sim_mem, compile_not_bool_vv_sim_mem]
QED

Theorem body_abs_mem_case:
  !cx ann e. body_expr_mem_ok cx e ==>
    body_expr_mem_ok cx (Builtin ann Abs [e])
Proof
  rpt gen_tac >> strip_tac >> pure_rewrite_tac[body_expr_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `ann = BaseT (IntT 256) /\ expr_type e = BaseT (IntT 256)` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  gvs[] >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule expr_body_pre_builtin_arg >> simp[] >>
     qexistsl_tac [`BaseT (IntT 256)`, `[e]`, `Abs`, `es`] >> simp[]) >>
  `expr_sim_mem ctx func cenv cx ty e es` by
    metis_tac[body_expr_mem_ok_def] >>
  metis_tac[compile_abs_sim_mem, compile_abs_vv_sim_mem]
QED

Theorem body_not_uint256_mem_case:
  !cx ann e. is_uint256_type (expr_type e) /\ body_expr_mem_ok cx e ==>
    body_expr_mem_ok cx (Builtin ann Not [e])
Proof
  rpt gen_tac >> strip_tac >> pure_rewrite_tac[body_expr_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `ann = expr_type e` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  gvs[] >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule expr_body_pre_builtin_arg >> simp[] >>
     qexistsl_tac [`expr_type e`, `[e]`, `Not`, `es`] >> simp[]) >>
  `expr_sim_mem ctx func cenv cx (expr_type e) e es` by
    metis_tac[body_expr_mem_ok_def] >>
  metis_tac[compile_not_uint256_sim_mem, compile_not_uint256_vv_sim_mem]
QED

Theorem body_not_bytes32_mem_case:
  !cx ann e. is_bytes32_type (expr_type e) /\ body_expr_mem_ok cx e ==>
    body_expr_mem_ok cx (Builtin ann Not [e])
Proof
  rpt gen_tac >> strip_tac >> pure_rewrite_tac[body_expr_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `ann = expr_type e` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  gvs[] >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule expr_body_pre_builtin_arg >> simp[] >>
     qexistsl_tac [`expr_type e`, `[e]`, `Not`, `es`] >> simp[]) >>
  `expr_sim_mem ctx func cenv cx (expr_type e) e es` by
    metis_tac[body_expr_mem_ok_def] >>
  metis_tac[compile_not_bytes32_sim_mem, compile_not_bytes32_vv_sim_mem]
QED

Theorem body_not_flag_mem_case:
  !cx ann e. is_flag_type (expr_type e) /\ body_expr_mem_ok cx e ==>
    body_expr_mem_ok cx (Builtin ann Not [e])
Proof
  rpt gen_tac >> strip_tac >> pure_rewrite_tac[body_expr_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `ann = expr_type e` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  gvs[] >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule expr_body_pre_builtin_arg >> simp[] >>
     qexistsl_tac [`expr_type e`, `[e]`, `Not`, `es`] >> simp[]) >>
  `expr_sim_mem ctx func cenv cx (expr_type e) e es` by
    metis_tac[body_expr_mem_ok_def] >>
  metis_tac[compile_not_flag_sim_mem, compile_not_flag_vv_sim_mem]
QED

Theorem body_neg_mem_case:
  !cx ann e. body_expr_mem_ok cx e ==>
    body_expr_mem_ok cx (Builtin ann Neg [e])
Proof
  rpt gen_tac >> strip_tac >> pure_rewrite_tac[body_expr_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env e es` by
    metis_tac[expr_body_pre_neg] >>
  `expr_sim_mem ctx func cenv cx (expr_type e) e es` by
    metis_tac[body_expr_mem_ok_def] >>
  metis_tac[compile_neg_sim_mem, compile_neg_vv_sim_mem]
QED

