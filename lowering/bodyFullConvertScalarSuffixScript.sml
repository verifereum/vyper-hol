Theory bodyFullConvertScalarSuffix
Ancestors
  exprSimConvert exprSimConvertFromBytes bodyPtrTypeBuiltinsScalarChecks
  bodyPtrTypeBuiltinsScalarArithmetic convertScalarFlags
  gasOutcomeFullCompose bodyFullPreds loweringPosts exprSimDefs
  exprLoweringProps fragGasSeqPtr fragGasOriginPtr vyperAST venomState

Theorem zero_convert_full_outcome:
  is_bytestring_type src /\ is_word_type dst /\
  valid_conversion src dst /\ well_formed_type (get_tenv cx) dst /\
  evaluate_type (get_tenv cx) src = SOME tv /\ value_has_type tv v /\
  (v = BytesV [] \/ v = StringV []) /\ ~s.vs_halted ==>
  gas_outcome_full (DF,lo,explicit,ctx,fn,PG) tops cx st0
    (\st. (convert_result cx src dst v,st)) (ee,s,G,tn)
    (\H res fin Gf tnf t. ?vout dtv.
      res = INL vout /\ evaluate_type (get_tenv cx) dst = SOME dtv /\
      typed_val_to_w256 dtv vout = 0w /\
      fin = ee with gas_obs := [] /\ t = s /\ Gf = G /\ tnf = tn) R
Proof
  strip_tac >>
  `~is_bytestring_type dst` by metis_tac[is_word_type_not_bytestring] >>
  `?vout dtv. convert_result cx src dst v = INL vout /\
    evaluate_type (get_tenv cx) dst = SOME dtv /\
    typed_val_to_w256 dtv vout = 0w` by
    metis_tac[dynamic_empty_scalar_convert] >>
  irule gas_outcome_full_pure >>
  simp[] >> qexistsl_tac [`G`,`ee`,`INL vout`,`s`,`tn`] >>
  simp[gas_origin_ptr_path_rules] >> metis_tac[]
QED

Theorem zero_convert_child_post:
  expr_post H ctx func cenv cx e es sa s1 s0 ee v1 x s /\
  is_word_type ann /\ evaluate_type (get_tenv cx) ann = SOME tv /\
  typed_val_to_w256 tv v = 0w ==>
  expr_post H ctx func cenv cx (TypeBuiltin ann Convert ann [e]) es sa s1 s0
    ee v (Lit 0w) s
Proof
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       expr_type_def, eval_operand_def] >> metis_tac[]
QED
