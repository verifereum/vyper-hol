Theory bodySimConvertWidenedFacts
Ancestors
  exprSimHyps exprSimHypsDefs valueCopyBytes

Theorem intcall_bytestring_read_footprint:
  !ce cx env a fid args drv es v es' tv.
    expr_body_pre ce cx env (Call a (IntCall fid) args drv) es /\
    is_bytestring_type a /\
    evaluate_type (get_tenv cx) a = SOME tv /\
    (do r <- eval_expr cx (Call a (IntCall fid) args drv);
        read_result cx r od) es = (INL v, es') ==>
    val_footprint tv v <=
      type_memory_bytes ce (lowered_value_type ce (Call a (IntCall fid) args drv))
Proof
  rpt strip_tac >>
  drule_all ifexp_intcall_read_physical_typed >> strip_tac >>
  drule ifexp_body_pre_intcall_physical >> strip_tac >>
  drule_all memory_rhs_read_annotation_typed >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_body_pre_def, expr_sim_inv_def,
        vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  simp[vyperTypeExprSoundnessTheory.value_runtime_typed_def,
       vyperASTTheory.expr_type_def] >> strip_tac >>
  `is_bytestring_type (lowered_value_type ce (Call a (IntCall fid) args drv))` by
    metis_tac[compileEnvTheory.arg_type_fits_bytestring_source] >>
  `type_memory_bytes ce (lowered_value_type ce (Call a (IntCall fid) args drv)) =
   type_memory_size stv` by
    metis_tac[expr_sim_inv_memory_size, expr_body_pre_def] >>
  simp[] >> irule bytestring_val_footprint_le >> metis_tac[]
QED

Theorem intcall_lowered_zero_read_empty:
  !ce cx env a fid args drv es v es'.
    expr_body_pre ce cx env (Call a (IntCall fid) args drv) es /\
    (lowered_value_type ce (Call a (IntCall fid) args drv) = BaseT (BytesT (Dynamic 0)) \/
     lowered_value_type ce (Call a (IntCall fid) args drv) = BaseT (StringT 0)) /\
    (do r <- eval_expr cx (Call a (IntCall fid) args drv);
        read_result cx r od) es = (INL v, es') ==>
    (v = BytesV [] \/ v = StringV "")
Proof
  rpt strip_tac >>
  drule_all ifexp_intcall_read_physical_typed >> strip_tac >>
  gvs[vyperValueTheory.evaluate_type_def] >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def]
QED
