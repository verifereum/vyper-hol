(* Source typing at the actual lowered type, allowing widened internal returns. *)
Theory bodyPtrTypeBuiltinsSourceTyping
Ancestors memoryLocalRhsProps bodyPtrTypeBuiltinsLayoutProbe
  supportedExprs supportedExprForms vyperTypeSystem exprLowering exprSimHypsDefs compileEnv
Libs monadsyntax

Theorem internal_call_lowered_bytestring:
  supported_expr tops (Call ty (IntCall id) args d) /\
  supported_program tops /\ get_module_code cx NONE = SOME tops /\
  cenv.ce_func_return_type = build_func_return_type tops /\
  expr_body_pre cenv cx env (Call ty (IntCall id) args d) es /\
  is_bytestring_type ty ==>
  is_bytestring_type
    (lowered_value_type cenv (Call ty (IntCall id) args d))
Proof
  Cases_on `d` >> PairCases_on `id` >> strip_tac >>
  gvs[expr_body_pre_def, supported_expr_def, supported_pure_expr_def,
      supported_effect_expr_def, AllCaseEqs()] >>
  gvs[well_typed_expr_def] >>
  qpat_x_assum `IS_SOME _` mp_tac >>
  Cases_on `supported_function_decl tops (id0,id1) Internal` >> simp[] >>
  rename1 `supported_function_decl tops (id0,id1) Internal = SOME decl` >>
  PairCases_on `decl` >>
  drule_all supported_internal_signature_return >> strip_tac >>
  simp[lowered_value_type_def] >>
  metis_tac[type_widens_to_def, compileEnvTheory.arg_type_fits_bytestring_source]
QED

Theorem source_lowered_bytestring:
  !cenv e tops cx env es.
  supported_expr tops e /\ supported_program tops /\
  get_module_code cx NONE = SOME tops /\
  cenv.ce_func_return_type = build_func_return_type tops /\
  expr_body_pre cenv cx env e es /\ is_bytestring_type (expr_type e) ==>
  is_bytestring_type (lowered_value_type cenv e)
Proof
  recInduct lowered_value_type_ind >>
  rpt strip_tac >>
  gvs[lowered_value_type_def, is_bytestring_type_def, vyperASTTheory.expr_type_def] >>
  drule_all internal_call_lowered_bytestring >>
  simp[lowered_value_type_def]
QED

Theorem source_read_lowered_layout:
  supported_expr tops e /\ supported_program tops /\
  get_module_code cx NONE = SOME tops /\
  cenv.ce_func_return_type = build_func_return_type tops /\
  expr_body_pre cenv cx env e es /\ is_bytestring_type (expr_type e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') ==>
  is_bytestring_type (lowered_value_type cenv e) /\
  ?tv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
       value_has_type tv v /\
       type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size tv
Proof
  strip_tac >> conj_tac
  >- (drule_all source_lowered_bytestring >> simp[]) >>
  drule_all memory_rhs_read_lowered_typed >> strip_tac >>
  gvs[expr_body_pre_def] >> drule_all memory_rhs_runtime_layout >> simp[]
QED

Theorem source_read_zero_bytes:
  expr_body_pre cenv cx env e es /\ supported_expr tops e /\
  cenv.ce_func_return_type = build_func_return_type tops /\
  supported_program tops /\ get_module_code cx NONE = SOME tops /\
  lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') ==>
  v = BytesV []
Proof
  strip_tac >> drule_all memory_rhs_read_lowered_typed >>
  strip_tac >> gvs[expr_body_pre_def] >>
  drule_all memory_rhs_runtime_layout >>
  simp[vyperValueTheory.evaluate_type_def] >> strip_tac >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def]
QED

Theorem source_read_zero_string:
  expr_body_pre cenv cx env e es /\ supported_expr tops e /\
  cenv.ce_func_return_type = build_func_return_type tops /\
  supported_program tops /\ get_module_code cx NONE = SOME tops /\
  lowered_value_type cenv e = BaseT (StringT 0) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') ==>
  v = StringV []
Proof
  strip_tac >> drule_all memory_rhs_read_lowered_typed >>
  strip_tac >> gvs[expr_body_pre_def] >>
  drule_all memory_rhs_runtime_layout >>
  simp[vyperValueTheory.evaluate_type_def] >> strip_tac >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def]
QED

Theorem bytestring_typed_value_view:
  is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v ==>
  (?n bs. ty = BaseT (BytesT (Dynamic n)) /\ v = BytesV bs /\ LENGTH bs <= n) \/
  (?n str. ty = BaseT (StringT n) /\ v = StringV str /\ LENGTH str <= n)
Proof
  Cases_on `ty` >> simp[is_bytestring_type_def] >>
  rename1 `is_bytestring_type (BaseT bt)` >> Cases_on `bt` >>
  simp[is_bytestring_type_def, vyperValueTheory.evaluate_type_def] >>
  TRY (rename1 `is_bytestring_type (BaseT (BytesT bd))` >>
       Cases_on `bd` >> simp[is_bytestring_type_def,
                             vyperValueTheory.evaluate_type_def]) >>
  strip_tac >> gvs[] >> Cases_on `v` >>
  gvs[vyperTypingTheory.value_has_type_def]
QED

Theorem source_read_bytestring_view:
  expr_body_pre cenv cx env e es /\ is_bytestring_type (expr_type e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') ==>
  (?n bs. expr_type e = BaseT (BytesT (Dynamic n)) /\
          v = BytesV bs /\ LENGTH bs <= n) \/
  (?n str. expr_type e = BaseT (StringT n) /\
           v = StringV str /\ LENGTH str <= n)
Proof
  strip_tac >> drule_all exprSimHypsTheory.memory_rhs_read_annotation_typed >>
  strip_tac >> gvs[expr_body_pre_def] >>
  drule_all memory_rhs_runtime_layout >> strip_tac >>
  drule_all bytestring_typed_value_view >> simp[]
QED

Theorem source_lowered_nonzero_capacity:
  supported_expr tops e /\ supported_program tops /\
  get_module_code cx NONE = SOME tops /\
  cenv.ce_func_return_type = build_func_return_type tops /\
  expr_body_pre cenv cx env e es /\ is_bytestring_type (expr_type e) /\
  lowered_value_type cenv e <> BaseT (BytesT (Dynamic 0)) /\
  lowered_value_type cenv e <> BaseT (StringT 0) ==>
  64 <= type_memory_bytes cenv (lowered_value_type cenv e)
Proof
  strip_tac >> drule_all source_lowered_bytestring >> strip_tac >>
  irule bytestring_nonzero_capacity >> simp[]
QED
