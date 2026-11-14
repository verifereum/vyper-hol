Theory bodyFullExtCallBoundary
Ancestors
  bodyFullPreds exprSimUnwrap exprOperandVar aggregateEvaluatedLayout
  vyperTypeEvalSoundness vyperEvalExprPreservesScopesDom

Theorem extcall_unwrap_boundary_facts:
  expr_body_pre cenv cx env
    (Call ann (ExtCall static skip sig opts) args dflt) es /\
  compile_expr cenv ty
    (Call ann (ExtCall static skip sig opts) args dflt) sa = (vv,sm) /\
  local_ptrs_reserved cenv sa /\
  eval_expr cx (Call ann (ExtCall static skip sig opts) args dflt)
    (es with gas_obs := obs) = (INL tv,ee) ==>
  post_value_type cenv (Call ann (ExtCall static skip sig opts) args dflt) = ann /\
  local_ptrs_reserved cenv sm /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!rt. evaluate_type (get_tenv cx) ann = SOME rt /\ ~is_word_type ann ==>
    type_memory_bytes cenv ann = type_memory_size rt /\
    type_memory_size rt < 2 ** 64) /\
  (?rt. evaluate_type (get_tenv cx) ann = SOME rt /\
    !v. read_result cx tv ee = (INL v,ee) ==> value_has_type rt v) /\
  (is_word_type ann \/ (?t op0. vv = StackValue t op0) \/
    (?t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory))
Proof
  strip_tac >> simp[vyperASTTheory.expr_type_def] >>
  drule compile_expr_extends >> strip_tac >>
  conj_tac
  >- (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
      qexists_tac `sa` >> simp[]) >>
  conj_tac
  >- (drule (cj 1 compiler_compile_var) >> simp[]) >>
  conj_tac
  >- (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  conj_tac
  >- (drule body_post_type_allocation_bound >> simp[vyperASTTheory.expr_type_def]) >>
  conj_tac
  >- (drule exprSimHypsTheory.expr_body_pre_type_evaluates >>
      simp[vyperASTTheory.expr_type_def, optionTheory.IS_SOME_EXISTS] >>
      disch_then (qx_choose_then `rt` assume_tac) >>
      qexists_tac `rt` >> simp[] >> rpt strip_tac >>
      `vyperState$bind (eval_expr cx (Call ann (ExtCall static skip sig opts) args dflt))
         (\result. read_result cx result) (es with gas_obs := obs) = (INL v,ee)` by
        simp[vyperStateTheory.bind_def] >>
      drule_at (Pat `vyperState$bind _ _ _ = _`) eval_expr_read_type_sound >>
      disch_then (qspec_then `env` mp_tac) >>
      gvs[exprSimHypsDefsTheory.expr_body_pre_def,
          exprSimHypsDefsTheory.expr_sim_inv_def,
          vyperTypeExprSoundnessTheory.value_runtime_typed_def,
          vyperASTTheory.expr_type_def] >> strip_tac >>
      gvs[vyperTypeInvariantsTheory.env_consistent_def,
          vyperTypeInvariantsTheory.env_context_consistent_def]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once exprLoweringTheory.compile_expr_def] >>
  PairCases_on `sig` >> Cases_on `args`
  >- (simp[exprLoweringTheory.compile_call_def, vyperASTTheory.expr_type_def,
           LET_THM, pairTheory.UNCURRY] >> strip_tac >> gvs[]) >>
  simp[exprLoweringTheory.compile_call_def, vyperASTTheory.expr_type_def,
       LET_THM, pairTheory.UNCURRY] >>
  Cases_on `sig2 = NoneT` >> simp[] >> strip_tac >>
  gvs[contextTheory.mk_ptr_def]
QED
