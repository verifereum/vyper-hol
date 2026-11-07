Theory bodyPtrTypeBuiltinsMemoryPost
Ancestors bodyPtrTypeBuiltinsMemoryInterface bodyPtrTypeBuiltinsWidenSemantic
  bodyPtrTypeBuiltinsCastExecution bodyPtrTypeBuiltinsWidenExecution
  bodyPtrTypeBuiltinsSourceTyping exprSimConvert vyperValueOperation
  vyperTyping vyperValue valueEncoding compileEnv arithmetic loweringPosts bodyPtrDefs
  ptrDiscipline
Libs intLib

Theorem memory_widen_length_bound:
  !len sz n. sz MOD 32 = 0 /\ len + 32 <= sz /\
    sz < 32 * ((n + 31) DIV 32) + 32 ==> len <= n
Proof
  rpt gen_tac >> qspec_then `32` mp_tac DIVISION >> simp[] >>
  disch_then (fn th => map_every (fn q => qspec_then q mp_tac th) [`sz`,`n+31`]) >>
  map_every (fn (tm,v) => Q.SPEC_TAC (tm,v))
    [(`(n+31) MOD 32`,`r`), (`(n+31) DIV 32`,`q`),
     (`sz MOD 32`,`srem`), (`sz DIV 32`,`squot`)] >> COOPER_TAC
QED

Theorem memory_widen_semantic_success:
  is_bytestring_type tsrc /\ is_bytestring_type tdst /\
  evaluate_type (get_tenv cx) tsrc = SOME tv /\ value_has_type tv v /\
  val_footprint tv v <= sz /\ sz MOD 32 = 0 /\
  sz < type_memory_bytes cenv tdst ==>
  ?v'. convert_result cx tsrc tdst v = INL v'
Proof
  strip_tac >> qspecl_then [`tsrc`,`tdst`] mp_tac memory_convert_shapes >>
  simp[] >> strip_tac >>
  gvs[evaluate_type_def] >> Cases_on `v` >>
  gvs[value_has_type_def, val_footprint_def, type_memory_bytes_def,
      convert_result_def, evaluate_convert_from_def, evaluate_convert_def] >>
  rename1 `LENGTH payload + 32 <= sz` >>
  `LENGTH payload <= n` by (irule memory_widen_length_bound >> metis_tac[]) >> simp[]
QED

Theorem memory_conversion_layout:
  is_bytestring_type tsrc /\ is_bytestring_type tdst /\
  evaluate_type (get_tenv cx) tsrc = SOME tv /\
  evaluate_type (get_tenv cx) tdst = SOME tv2 /\ value_has_type tv v /\
  convert_result cx tsrc tdst v = INL v' ==>
  value_has_type tv2 v' /\ val_wf tv2 v' /\
  val_footprint tv2 v' = val_footprint tv v /\
  (!off mem. val_in_memory tv2 v' off mem <=> val_in_memory tv v off mem)
Proof
  strip_tac >> qspecl_then [`tsrc`,`tdst`] mp_tac memory_convert_shapes >>
  simp[] >> strip_tac >> gvs[evaluate_type_def] >> Cases_on `v` >>
  gvs[value_has_type_def, convert_result_def, evaluate_convert_from_def,
      evaluate_convert_def, AllCaseEqs(), val_footprint_def, val_wf_def,
      val_in_memory_def, abiDecoderStringTheory.abi_decoder_string_bytes_roundtrip] >>
  simp[type_memory_size_def] >>
  mp_tac (Q.SPEC `n` exprSimPropsTheory.le_word_size_mul) >> decide_tac
QED

Theorem memory_conversion_expr_post:
  is_bytestring_type (expr_type e1) /\ is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e1) = SOME tv /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv2 /\ value_has_type tv v /\
  convert_result cx (expr_type e1) (expr_type e) v = INL v' /\
  expr_post ctx fn cenv cx e1 es sa sb s0 es1 v op t ==>
  expr_post ctx fn cenv cx e es sa sb s0 es1 v' op t
Proof
  strip_tac >> drule_all memory_conversion_layout >> strip_tac >>
  `~is_word_type (expr_type e1) /\ ~is_word_type (expr_type e)` by
    metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  gvs[expr_post_def, expr_val_rel_def, expr_val_at_def] >>
  simp[] >>
  qspecl_then [`expr_type e1`,`expr_type e`] mp_tac memory_convert_shapes >>
  simp[] >> strip_tac >> gvs[evaluate_type_def] >>
  metis_tac[exprSimPropsTheory.local_val_at_base, LESS_EQ_REFL]
QED

Theorem memory_outer_annotation:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert dst [e]) es ==>
  ann = dst
Proof
  strip_tac >> drule expr_body_pre_convert >> simp[]
QED

Theorem memory_outer_buffer_covered:
  lookup_var src s = SOME w /\ ptr_covers G tn src s (type_memory_bytes cenv dst) ==>
  ptr_buf_ok cenv (TypeBuiltin dst Convert dst [e]) (Var src) G s
Proof
  simp[ptr_buf_ok_def, convert_outer_lowered_type, ptr_covers_def,
       venomStateTheory.eval_operand_def] >> rpt strip_tac >>
  gvs[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem memory_post_inst_idx:
  expr_post ctx fn cenv cx e es sa sb s0 es1 v op
    (s with vs_inst_idx := pc) <=>
  expr_post ctx fn cenv cx e es sa sb s0 es1 v op s
Proof
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       exprLoweringPropsTheory.stmt_state_rel_inst_idx,
       venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
       local_region_def, locals_kept_def]
QED
