Theory bodyPtrTypeBuiltinsMemoryContinue
Ancestors bodyPtrTypeBuiltinsMemoryPost bodyPtrTypeBuiltinsLoweredRepresentation
  bodyPtrTypeBuiltinsMemoryInterface
  bodyPtrTypeBuiltinsHeaderLoad representationCleanPtr exprSimHyps
  bodyPtrDefs exprSimDefs vyperTyping valueEncoding vyperValue
  vyperTypeSystem compileEnv venomState loweringPosts
Libs monadsyntax

Theorem memory_source_representation:
  is_bytestring_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ ptr_val_ok cx ty v x G tn s /\
  eval_operand x s = SOME w ==>
  ?src. x = Var src /\ lookup_var src s = SOME w /\
    op_taint tn (Var src) = {} /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n w) m) /\
    (!j. w2n w <= j /\ j < w2n w + 32 ==> j NOTIN tn.t_mem)
Proof
  strip_tac >>
  `~is_word_type ty` by metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  `ptr_mem_ok cx ty v x G tn s` by gvs[ptr_val_ok_def] >>
  `val_footprint tv v <> 0` by
    (Cases_on `ty` >> gvs[is_bytestring_type_def] >>
     rename1 `is_bytestring_type (BaseT bt)` >> Cases_on `bt` >>
     gvs[is_bytestring_type_def, evaluate_type_def] >>
     TRY (rename1 `BytesT bd` >> Cases_on `bd` >>
          gvs[is_bytestring_type_def, evaluate_type_def]) >>
     Cases_on `v` >> gvs[value_has_type_def, val_footprint_def]) >>
  `?src b sz. x = Var src /\ FLOOKUP G src = SOME (b,sz)` by
    (fs[ptr_mem_ok_def, eval_operand_def] >> metis_tac[]) >>
  gvs[eval_operand_def] >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n w) m` by
    (fs[ptr_mem_ok_def, eval_operand_def] >> metis_tac[]) >>
  simp[] >> conj_tac
  >- gvs[ptr_val_ok_def, eval_operand_def] >>
  Cases_on `ty` >> gvs[is_bytestring_type_def] >>
  rename1 `is_bytestring_type (BaseT bt)` >> Cases_on `bt` >>
  gvs[is_bytestring_type_def, evaluate_type_def] >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd` >>
       gvs[is_bytestring_type_def, evaluate_type_def]) >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  metis_tac[robust_val_in_memory_bytes_clean, robust_val_in_memory_string_clean]
QED

Theorem memory_source_packet:
  body_inv tops ctx cenv cx /\ ~cx.in_deploy /\
  expr_body_pre cenv cx env e es /\ is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  ptr_val_ok cx (expr_type e) v x G tn s /\ ptr_buf_ok cenv e x G s /\
  eval_operand x s = SOME w ==>
  ?src ltv. x = Var src /\ lookup_var src s = SOME w /\
    ptr_covers G tn src s (type_memory_bytes cenv (lowered_value_type cenv e)) /\
    (!j. w2n w <= j /\ j < w2n w + 32 ==> j NOTIN tn.t_mem) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n w) m) /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME ltv /\
    value_has_type ltv v /\
    val_footprint tv v <= type_memory_bytes cenv (lowered_value_type cenv e) /\
    32 <= type_memory_bytes cenv (lowered_value_type cenv e) /\
    type_memory_bytes cenv (lowered_value_type cenv e) MOD 32 = 0
Proof
  strip_tac >> drule_all memory_source_representation >> strip_tac >> gvs[] >>
  drule_all bytestring_read_lowered_layout >> strip_tac >>
  drule_all bodyPtrTypeBuiltinsBodyTypingTheory.body_runtime_source_lowered_bytestring >>
  strip_tac >>
  `32 <= type_memory_bytes cenv (lowered_value_type cenv e) /\
   type_memory_bytes cenv (lowered_value_type cenv e) MOD 32 = 0` by
    (qspecl_then [`lowered_value_type cenv e`,`lowered_value_type cenv e`]
       mp_tac memory_convert_shapes >> simp[] >> strip_tac >>
     gvs[compileEnvTheory.type_memory_bytes_def, evaluate_type_def,
         type_memory_size_def] >> simp[]) >>
  `ptr_covers G tn src s (type_memory_bytes cenv (lowered_value_type cenv e))` by
    (irule ptr_buf_ok_covers >> simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `ltv` >> simp[]
QED
