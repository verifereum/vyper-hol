Theory bodyPtrTypeBuiltinsMemoryOperandSemantics
Ancestors
  bodyPtrTypeBuiltinsConvertOperandBoundary bodyPtrSignedConvertSourceTyping
  exprSimConvertBytes exprSimHyps exprSimHypsDefs memoryLocalRhsProps
  exprBopSimProps valueCopyBytes exprLoweringProps bodySim exprSimConvert
  typedMemoryCopy valueEncodingTyping
Libs monadsyntax

Theorem convert_memory_operand_semantics:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert target [e]) (es with gas_obs := gs) /\
  is_bytestring_type (expr_type e) /\ is_bytestring_type target /\
  ~((?a f args drv. e = Call a (IntCall f) args drv) /\
    lowered_value_type cenv e <> expr_type e) /\
  (do r <- eval_expr cx e; read_result cx r od) (es with gas_obs := gs) = (INL v,ee) ==>
  ?tv tout. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    evaluate_type (get_tenv cx) target = SOME tout /\
    type_memory_bytes cenv target = type_memory_size tout /\
    value_has_type tv v /\ val_wf tv v /\
    val_footprint tv v <= type_memory_bytes cenv (lowered_value_type cenv e) /\
    is_bytestring_type (lowered_value_type cenv e) /\
    0 < type_memory_bytes cenv (lowered_value_type cenv e) /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by
    (drule expr_body_pre_convert >> simp[] >> metis_tac[]) >>
  `ann = target` by (drule expr_body_pre_convert >> simp[]) >>
  drule_all memory_rhs_read_annotation_typed >> strip_tac >>
  `expr_sim_inv cenv cx env (es with gas_obs := gs)` by fs[expr_body_pre_def] >>
  drule_all memory_rhs_runtime_layout >> strip_tac >>
  `is_bytestring_type (lowered_value_type cenv e)` by
    (irule body_source_lowered_bytestring >> metis_tac[]) >>
  `val_footprint tv v <= type_memory_bytes cenv (lowered_value_type cenv e)` by
    (irule bytestring_read_lowered_footprint >> metis_tac[]) >>
  `?tout. evaluate_type (get_tenv cx) target = SOME tout` by
    (qpat_assum `expr_body_pre _ _ _ (TypeBuiltin _ _ _ _) _`
       (mp_then Any mp_tac expr_body_pre_type_evaluates) >>
     simp[vyperASTTheory.expr_type_def] >>
     Cases_on `evaluate_type (get_tenv cx) target` >> simp[]) >>
  `type_memory_bytes cenv target = type_memory_size tout` by
    (irule typed_copy_memory_size >> fs[expr_sim_inv_def] >> metis_tac[]) >>
  qexistsl_tac [`tv`,`tout`] >> simp[bytestring_memory_bytes_positive] >>
  conj_tac >- metis_tac[value_has_type_val_wf] >>
  drule bop_value_scopes_dom >> simp[]
QED
