Theory bodyPtrTypeBuiltinsBytesWordInputs
Ancestors bodyPtrTypeBuiltinsBytesWordActual bodyPtrSignedConvertSourceTyping
  exprSimHash exprSimHashBoundary bodyPtrDefs loweringPosts exprLoweringProps
  vyperValue valueEncoding venomState

Theorem bytes_word_child_memory_inputs:
  expr_post ctx fn cenv cx e es ca sa s0 ee v op s /\
  is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
  ptr_val_ok cx (expr_type e) v op G tn s /\ ptr_buf_ok cenv e op G s /\
  64 <= type_memory_bytes cenv (lowered_value_type cenv e) ==>
  ?src a. op = Var src /\ lookup_var src s = SOME a /\
    ptr_mem_ok cx (expr_type e) v (Var src) G tn s /\
    op_taint tn (Var src) = {} /\
    w2n a+32 < dimword(:256) /\ val_in_memory tv v (w2n a) s.vs_memory
Proof
  strip_tac >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_bytestring >> simp[]) >>
  `~is_word_type (expr_type e)` by
    metis_tac[exprSimConvertTheory.is_word_type_not_bytestring] >>
  `?a. eval_operand op s = SOME a /\ val_in_memory tv v (w2n a) s.vs_memory` by
    gvs[expr_post_def, expr_val_rel_def] >>
  `?src. op = Var src` by
    (gvs[ptr_buf_ok_def] >> first_x_assum drule >> simp[] >> metis_tac[]) >>
  gvs[] >>
  `lookup_var src s = SOME a` by fs[eval_operand_def] >>
  `ptr_mem_ok cx (expr_type e) v (Var src) G tn s /\
   op_taint tn (Var src) = {}` by fs[ptr_val_ok_def] >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_bytestring >> simp[]) >>
  drule_all hash_post_footprint_bound >> strip_tac >>
  `32 <= val_footprint tv v` by
    (drule_all bytestring_typed_value_view >> strip_tac >>
     gvs[vyperValueTheory.evaluate_type_def, val_footprint_def]) >>
  simp[]
QED

Theorem bytes_word_source_length:
  is_bytestring_type src /\ ~is_bytestring_type dst /\ valid_conversion src dst /\
  well_formed_type tenv dst /\
  evaluate_type (get_tenv cx) src = SOME tv /\ value_has_type tv v ==>
  (?bs. v = BytesV bs /\ LENGTH bs <= 32 /\ tv <> BaseTV AddressT /\
     (!k. tv <> BaseTV (BytesT (Fixed k)))) \/
  (?str. v = StringV str /\ LENGTH str <= 32)
Proof
  strip_tac >> drule_all bodyPtrTypeBuiltinsBytesWordTypesTheory.bytestring_scalar_type_partition >> strip_tac >>
  drule_all bytestring_typed_value_view >> strip_tac >>
  gvs[vyperValueTheory.evaluate_type_def, vyperTypingTheory.value_has_type_def,
      vyperTypeSystemTheory.well_formed_type_def] >> decide_tac
QED
