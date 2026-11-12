(* Static capacity facts for the plain bytestring convert source. *)
Theory bodyMemTbConvertSourceSizing
Ancestors
  bodyMemTbConvertSourceDispatch bodyMemTbConvertLoweredSize
  exprSimSource exprSimHyps exprSimHypsDefs vyperTypeInvariants
  vyperTypeSystem vyperValue compileEnv

Theorem convert_plain_nonzero_source_size:
  expr_body_pre ce cx env e es /\ is_bytestring_type (expr_type e) /\
  (!a f args d. e = Call a (IntCall f) args d ==>
     lowered_value_type ce e = expr_type e) /\
  lowered_value_type ce e <> BaseT (BytesT (Dynamic 0)) /\
  lowered_value_type ce e <> BaseT (StringT 0) ==>
  64 <= type_memory_bytes ce (expr_type e)
Proof
  strip_tac >>
  drule expr_body_pre_var_types_well_formed >> strip_tac >>
  `well_typed_expr env e /\
   sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    gvs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
        env_context_consistent_def] >>
  drule_all convert_plain_lowered_type_compatible >> strip_tac
  >- (irule convert_nonzero_bytestring_memory_size >> metis_tac[]) >>
  `is_bytestring_type (lowered_value_type ce e)` by
    metis_tac[memoryLocalRhsPropsTheory.arg_type_fits_bytestring_source] >>
  `64 <= type_memory_bytes ce (lowered_value_type ce e)` by
    (irule convert_nonzero_bytestring_memory_size >> simp[]) >>
  drule_all memoryLocalRhsPropsTheory.arg_type_fits_bytestring_memory_bytes >>
  disch_then (qspec_then `ce` assume_tac) >> decide_tac
QED
