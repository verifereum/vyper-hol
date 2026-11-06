(* Robust lifting of the existing capacity-parametric bytestring layout
   transfer in valueCopyBytes; no duplicate pointwise lemma. *)
Theory bodyPtrTypeBuiltinsLoweredRepresentation
Ancestors
  valueCopyBytes bodyPtrDefs memoryLocalRhsProps exprSimHypsDefs
  exprSimHyps exprLoweringProps valueEncoding valueTypingMemoryProps
  vyperTypeExprSoundness
Libs
  monadsyntax

Theorem bytestring_robust_memory_transfer:
  is_bytestring_type tsrc /\ is_bytestring_type tdst /\
  evaluate_type tenv tsrc = SOME tv /\
  evaluate_type tenv tdst = SOME tv' /\ value_has_type tv' v /\
  (!m. mem_agree_outside bad mem m ==> val_in_memory tv v off m) ==>
  !m. mem_agree_outside bad mem m ==> val_in_memory tv' v off m
Proof
  rpt strip_tac >> irule bytestring_val_in_memory_transfer >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem bytestring_read_lowered_layout:
  expr_body_pre cenv cx env e es /\ supported_expr tops e /\
  cenv.ce_func_return_type = build_func_return_type tops /\
  supported_program tops /\ get_module_code cx NONE = SOME tops /\
  expr_sim_inv cenv cx env es /\
  is_bytestring_type (expr_type e) /\
  is_bytestring_type (lowered_value_type cenv e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') /\
  (!m. mem_agree_outside bad mem m ==> val_in_memory tv v off m) ==>
  ?ltv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME ltv /\
    value_has_type ltv v /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size ltv /\
    val_footprint tv v <= type_memory_bytes cenv (lowered_value_type cenv e) /\
    (!m. mem_agree_outside bad mem m ==> val_in_memory ltv v off m)
Proof
  strip_tac >> drule_all memory_rhs_read_lowered_typed >> strip_tac >>
  drule_all memory_rhs_runtime_layout >> strip_tac >>
  drule_all memory_rhs_read_annotation_typed >> strip_tac >>
  drule_all memory_rhs_runtime_layout >> strip_tac >>
  qexists_tac `tv'` >> gvs[] >> conj_tac
  >- (irule bytestring_val_footprint_le >> metis_tac[]) >>
  rpt strip_tac >> irule bytestring_val_in_memory_transfer >> metis_tac[]
QED
