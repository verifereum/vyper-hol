Theory exprSimPopNestedLocalSuffix
Ancestors
  exprSimPopNestedLocalPost exprSimPopNestedLocalRun exprSimProps
  venomState words arithmetic list exprSimHyps exprSimHypsDefs vyperTypeEnv

Theorem memory_pop_result_address:
  vs <> [] /\ LENGTH vs < dimword (:256) /\
  w2n (h:bytes32) = locbase + k /\
  locbase + sz < dimword (:256) /\
  k + 32 + (LENGTH vs - 1) * esz <= sz /\
  lookup_var x u = SOME (h + 32w + (n2w (LENGTH vs) - 1w) * n2w esz) ==>
  eval_operand (Var x) u = SOME (h + 32w + (n2w (LENGTH vs) - 1w) * n2w esz) /\
  w2n (h + 32w + (n2w (LENGTH vs) - 1w) * n2w esz) =
    locbase + k + 32 + (LENGTH vs - 1) * esz
Proof
  strip_tac >> conj_tac >- simp[eval_operand_def] >>
  `0 < LENGTH vs` by (Cases_on `vs` >> gvs[]) >>
  `n2w (LENGTH vs) - 1w = n2w (LENGTH vs - 1) : bytes32` by
    simp[GSYM wordsTheory.n2w_sub] >>
  asm_rewrite_tac[] >>
  rewrite_tac[GSYM wordsTheory.word_mul_n2w, GSYM wordsTheory.word_add_n2w,
    wordsTheory.WORD_ADD_ASSOC] >>
  `w2n h + (sz - k) < dimword (:256) /\
   32 + (LENGTH vs - 1) * esz <= sz - k` by decide_tac >>
  drule_all buffer_offset_no_wrap >>
  pure_rewrite_tac[GSYM wordsTheory.word_mul_n2w,
    GSYM wordsTheory.WORD_ADD_ASSOC, GSYM wordsTheory.word_add_n2w] >>
  disch_tac >> decide_tac
QED

Theorem pop_array_element_layout:
  expr_body_pre cenv cx env e es /\
  evaluate_type (get_tenv cx) (ArrayT ann bd) = SOME (ArrayTV etv bd') ==>
  evaluate_type (get_tenv cx) ann = SOME etv /\
  type_memory_bytes cenv ann = type_memory_size etv
Proof
  strip_tac >>
  `evaluate_type (get_tenv cx) ann = SOME etv` by
    gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  simp[] >> irule expr_sim_inv_memory_size >>
  goal_assum (drule_at Any) >> fs[expr_body_pre_def] >> metis_tac[]
QED
