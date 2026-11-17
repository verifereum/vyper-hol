Theory bodyPtrPrecompileBuiltinsArithmeticSource
Ancestors exprSimECArith exprSimHash exprSimHashBoundary exprSimProps loweringPosts valueEncoding valueEncodingDefs compileEnv
          vyperValue vyperTyping exprSimDefs valueEncodingProofs
          vyperValueOperation vyperContext extCallOracle vfmExecution list

Theorem ec_point_eval_bound:
  stmt_state_rel H ctx fn cenv cx es s /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo hi es v p s ==>
  ?w. eval_operand p s = SOME w /\ w2n w + 64 < dimword(:256)
Proof
  strip_tac >>
  `?w. eval_operand p s = SOME w` by
    (gvs[expr_val_at_def, evaluate_type_def, is_word_type_def,
         type_slot_size_def, wordsTheory.dimword_def] >> metis_tac[]) >>
  drule_all ec_point_pointer_bound >> strip_tac >> qexists `w` >> simp[]
QED

Theorem ecmul_memory_semantics:
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v1 /\
  value_has_type (BaseTV (UintT 256)) v2 /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v1 p1 s /\
  expr_val_rel cx (BaseT (UintT 256)) v2 p2 s ==>
  ?point sw. eval_operand p1 s = SOME point /\ eval_operand p2 s = SOME sw /\
    evaluate_ecmul [v1;v2] =
      (case vfmExecution$ecmul
        (w2n (mem_word_at (w2n point) s.vs_memory),
         w2n (mem_word_at (w2n point+32) s.vs_memory)) (w2n sw) of
         NONE => INR (RuntimeError "ECMul invalid point")
       | SOME r => INL (mk_ec_result r))
Proof
  strip_tac >>
  qpat_assum `value_has_type _ v1` (mp_then Any mp_tac ec_point_memory_words) >>
  disch_then drule >> strip_tac >>
  rename1 `eval_operand p1 s = SOME first_point` >>
  qexists `first_point` >> simp[] >>
  drule ec_uint256_encoding >> strip_tac >> gvs[] >>
  qpat_x_assum `expr_val_rel cx (BaseT (UintT 256)) _ _ _` mp_tac >>
  simp[expr_val_rel_def, evaluate_type_def, is_word_type_def] >> strip_tac >> gvs[] >>
  simp[evaluate_ecmul_def, wordsTheory.w2n_n2w, wordsTheory.dimword_def]
QED

Theorem ecadd_memory_semantics:
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v1 /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v2 /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v1 p1 s /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v2 p2 s ==>
  ?point point2. eval_operand p1 s = SOME point /\ eval_operand p2 s = SOME point2 /\
    evaluate_ecadd [v1;v2] =
      (case vfmExecution$ecadd
        (w2n (mem_word_at (w2n point) s.vs_memory),
         w2n (mem_word_at (w2n point+32) s.vs_memory))
        (w2n (mem_word_at (w2n point2) s.vs_memory),
         w2n (mem_word_at (w2n point2+32) s.vs_memory)) of
         NONE => INR (RuntimeError "ECAdd invalid point")
       | SOME r => INL (mk_ec_result r))
Proof
  strip_tac >>
  qpat_assum `value_has_type _ v1` (mp_then Any mp_tac ec_point_memory_words) >>
  disch_then drule >> strip_tac >>
  rename1 `eval_operand p1 s = SOME first_point` >>
  qexists `first_point` >> simp[] >>
  qpat_assum `value_has_type _ v2` (mp_then Any mp_tac ec_point_memory_words) >>
  disch_then drule >> strip_tac >>
  rename1 `eval_operand p2 s = SOME second_point` >>
  qexists `second_point` >>
  gvs[evaluate_ecadd_def, wordsTheory.w2n_n2w, wordsTheory.dimword_def]
QED
