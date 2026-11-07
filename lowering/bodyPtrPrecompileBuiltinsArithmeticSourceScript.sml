Theory bodyPtrPrecompileBuiltinsArithmeticSource
Ancestors exprSimHash exprSimProps loweringPosts valueEncoding compileEnv
          vyperValue vyperTyping exprSimDefs valueEncodingProofs
          vyperValueOperation vyperContext extCallOracle vfmExecution list

Theorem ec_point_pointer_bound:
  stmt_state_rel ctx fn cenv cx es s /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo hi es v p s /\
  eval_operand p s = SOME w ==>
  w2n w + 64 < dimword(:256)
Proof
  `!v. val_footprint (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v = 64` by
    (Cases >> simp[val_footprint_def, type_memory_size_def]) >>
  simp[expr_val_at_def, evaluate_type_def, is_word_type_def,
       type_slot_size_def, wordsTheory.dimword_def] >> strip_tac >> gvs[] >>
  irule (SRULE [wordsTheory.dimword_def] hash_live_footprint_bound) >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem ec_point_eval_bound:
  stmt_state_rel ctx fn cenv cx es s /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo hi es v p s ==>
  ?w. eval_operand p s = SOME w /\ w2n w + 64 < dimword(:256)
Proof
  strip_tac >>
  `?w. eval_operand p s = SOME w` by
    (gvs[expr_val_at_def, evaluate_type_def, is_word_type_def,
         type_slot_size_def, wordsTheory.dimword_def] >> metis_tac[]) >>
  drule_all ec_point_pointer_bound >> strip_tac >> qexists `w` >> simp[]
QED

Theorem ec_uint256_encoding[local]:
  value_has_type (BaseTV (UintT 256)) v ==>
  ?i. v = IntV i /\ 0 <= i /\ Num i < 2 ** 256 /\
      typed_val_to_w256 (BaseTV (UintT 256)) v = n2w (Num i)
Proof
  Cases_on `v` >> simp[value_has_type_def, typed_val_to_w256_def,
    val_to_w256_def, integer_wordTheory.i2w_def] >>
  strip_tac >> `~(i < 0)` by intLib.ARITH_TAC >> simp[]
QED

Theorem ec_point_index_memory[local]:
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) (ArrayV av) /\
  val_in_memory (ArrayTV (BaseTV (UintT 256)) (Fixed 2))
    (ArrayV av) off mem /\ j < 2 ==>
  ?i. array_index (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) av (&j) = SOME (IntV i) /\
      0 <= i /\ Num i < 2 ** 256 /\
      mem_word_at (off + j * 32) mem = n2w (Num i)
Proof
  Cases_on `av` >> simp[value_has_type_def, val_in_memory_def] >> strip_tac >>
  Cases_on `ALOOKUP l j`
  >- (simp[array_index_def, default_value_def] >>
      first_x_assum (qspec_then `j` mp_tac) >>
      simp[default_value_def, val_in_memory_def, type_memory_size_def,
           val_to_w256_def, integer_wordTheory.i2w_def]) >>
  drule_all sparse_has_type_lookup >>
  disch_then (strip_assume_tac o REWRITE_RULE [value_has_type_def]) >>
  drule ec_uint256_encoding >> strip_tac >> gvs[] >>
  drule_all kvs_in_memory_lookup >>
  simp[array_index_def, val_in_memory_def, type_memory_size_def,
       val_to_w256_def, integer_wordTheory.i2w_def] >>
  `~(i < 0)` by intLib.ARITH_TAC >> simp[]
QED

Theorem ec_point_memory_words:
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v op s ==>
  ?w x y. eval_operand op s = SOME w /\ extract_ec_point v = SOME (x,y) /\
    0 <= x /\ Num x < 2 ** 256 /\ 0 <= y /\ Num y < 2 ** 256 /\
    mem_word_at (w2n w) s.vs_memory = n2w (Num x) /\
    mem_word_at (w2n w+32) s.vs_memory = n2w (Num y)
Proof
  strip_tac >>
  gvs[expr_val_rel_def, evaluate_type_def, is_word_type_def,
      type_slot_size_def, wordsTheory.dimword_def] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  drule ec_point_index_memory >> disch_then drule >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  drule ec_point_index_memory >> disch_then drule >>
  disch_then (qspec_then `1` mp_tac) >> simp[] >> strip_tac >>
  simp[extract_ec_point_def] >> metis_tac[]
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
