(* Runtime evaluation of layouts used by if-expression arms. *)
Theory bodyIfExpArmLayout
Ancestors
  bodyIfExpReturnLayout exprSimHyps exprSimHypsDefs memoryLocalRhsProps
  exprLowering bodySim vyperTypeInvariants vyperTypeSystem

Theorem ifexp_lowered_type_evaluates[local]:
  !cenv e tops ctx cx env es.
    body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
    type_memory_bytes cenv (lowered_value_type cenv e) < 2 ** 64 ==>
    IS_SOME (evaluate_type (get_tenv cx) (lowered_value_type cenv e))
Proof
  recInduct lowered_value_type_ind >> rpt conj_tac >> rpt gen_tac >>
  strip_tac >> gvs[lowered_value_type_def]
  >- (simp[optionTheory.IS_SOME_EXISTS] >>
      irule bytestring_memory_bound_evaluates >>
      simp[compileEnvTheory.is_bytestring_type_def] >>
      qexists_tac `cenv` >> fs[optionTheory.IS_SOME_EXISTS])
  >- (simp[optionTheory.IS_SOME_EXISTS] >>
      irule bytestring_memory_bound_evaluates >>
      simp[compileEnvTheory.is_bytestring_type_def] >>
      qexists_tac `cenv` >> fs[optionTheory.IS_SOME_EXISTS])
  >- (simp[optionTheory.IS_SOME_EXISTS] >>
      irule bytestring_memory_bound_evaluates >>
      conj_tac
      >- (rw[concat_buffer_type_def] >> CASE_TAC >>
          simp[compileEnvTheory.is_bytestring_type_def] >> CASE_TAC >>
          simp[compileEnvTheory.is_bytestring_type_def]) >>
      qexists_tac `cenv` >> fs[optionTheory.IS_SOME_EXISTS])
  >- (simp[optionTheory.IS_SOME_EXISTS] >>
      irule bytestring_memory_bound_evaluates >>
      simp[compileEnvTheory.is_bytestring_type_def] >>
      qexists_tac `cenv` >> fs[optionTheory.IS_SOME_EXISTS])
  >- (`expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
      fs[expr_body_pre_def, vyperTypeCallGraphTheory.int_calls_expr_def] >>
      Cases_on `func_id` >> gvs[] >>
      `?sig. FLOOKUP env.fn_sigs (NONE,r) = SOME sig` by
        fs[well_typed_expr_def, optionTheory.IS_SOME_EXISTS] >>
      drule_all ifexp_body_signature_return >> strip_tac >>
      drule_all frame_signature_return_well_formed >>
      fs[well_formed_type_def, expr_sim_inv_def, env_consistent_def,
         env_context_consistent_def, compileEnvTheory.nsid_to_string_def]) >>
  drule expr_body_pre_type_evaluates >>
  simp[vyperASTTheory.expr_type_def]
QED

Theorem ifexp_same_layout_runtime_size[local]:
  !tops ctx cenv cx env e es t tvt.
    body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
    same_memory_layout cenv (lowered_value_type cenv e) t /\
    evaluate_type (get_tenv cx) t = SOME tvt /\
    type_memory_bytes cenv t < 2 ** 64 ==>
    ?lvt. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME lvt /\
          type_memory_size tvt <= type_memory_size lvt
Proof
  rpt strip_tac >>
  `type_memory_bytes cenv (lowered_value_type cenv e) < 2 ** 64` by
    fs[contextTheory.same_memory_layout_def] >>
  drule_all ifexp_lowered_type_evaluates >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  qexists_tac `x` >> simp[] >>
  `type_memory_bytes cenv t = type_memory_size tvt` by
    metis_tac[expr_sim_inv_memory_size] >>
  `type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size x` by
    metis_tac[expr_sim_inv_memory_size] >>
  fs[contextTheory.same_memory_layout_def]
QED

Theorem ifexp_body_arm_runtime_sizes:
  !tops ctx cenv cx env a b es t.
    body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env a es /\
    expr_body_pre cenv cx env b es /\ expr_type a = t /\ expr_type b = t /\
    ~is_word_type t ==>
    !e tvt. (e = a \/ e = b) /\
      same_memory_layout cenv (lowered_value_type cenv e) t /\
      evaluate_type (get_tenv cx) t = SOME tvt ==>
      ?lvt. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME lvt /\
            type_memory_size tvt <= type_memory_size lvt
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env e es /\ expr_type e = t` by metis_tac[] >>
  `type_memory_bytes cenv t < 2 ** 64` by
    metis_tac[expr_body_pre_copy_ok] >>
  irule ifexp_same_layout_runtime_size >> metis_tac[]
QED
