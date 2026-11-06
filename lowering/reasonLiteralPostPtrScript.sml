(* Semantic annotation resources for the reason literal shortcut. *)
Theory reasonLiteralPostPtr
Ancestors reasonLiteralBufferPtr reasonMemorySuccessPtr reasonResourcesPtr
  exprSimPtrLiteralBuffer compileEnv words freshWrites venomState
  venomExecSemantics context ptrDiscipline
  exprSimHyps exprSimHypsDefs vyperTypeSystem allocLimits vyperAST
  vyperValue bodyPtrDefs

Theorem reason_literal_source_bounds:
  expr_body_pre cenv cx env
    (Literal (BaseT (StringT ml)) (StringL str)) es ==>
  LENGTH str <= ml /\ type_alloc_ok cenv (BaseT (StringT ml)) /\
  64 + type_memory_bytes cenv (BaseT (StringT ml)) < dimword (:256)
Proof
  strip_tac >>
  `LENGTH str <= ml /\ type_alloc_ok cenv (BaseT (StringT ml))` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_literal_def,
        alloc_limits_expr_def] >>
  drule reason_encoder_allocation_limit >> simp[]
QED

Theorem reason_literal_string_representation:
  LENGTH str <= ml /\
  mem_word_at b s.vs_memory = n2w (LENGTH str) /\
  mem_bytes_at (b+32) (LENGTH str) s.vs_memory = MAP (n2w o ORD) str /\
  tn'.t_mem = (tn.t_mem UNION dirty) DIFF
    {i | b <= i /\ i < b+32+32*word_size (LENGTH str)} ==>
  val_wf (BaseTV (StringT ml)) (StringV str) /\
  val_in_memory (BaseTV (StringT ml)) (StringV str) b s.vs_memory /\
  val_footprint (BaseTV (StringT ml)) (StringV str) <= 32+32*word_size (LENGTH str) /\
  (!i. b <= i /\ i < b+val_footprint (BaseTV (StringT ml)) (StringV str) ==>
    i NOTIN tn'.t_mem) /\
  val_store_size (BaseTV (StringT ml)) (StringV str) = 32+32*word_size (LENGTH str)
Proof
  strip_tac >> irule literal_ptr_string_representation >> simp[] >>
  qexists_tac `tn with t_mem := tn.t_mem UNION dirty` >> simp[]
QED

Theorem reason_literal_type_evaluates:
  expr_body_pre cenv cx env
    (Literal (BaseT (StringT ml)) (StringL str)) es ==>
  evaluate_type (get_tenv cx) (BaseT (StringT ml)) = SOME (BaseTV (StringT ml))
Proof
  strip_tac >> drule expr_body_pre_type_evaluates >>
  simp[expr_type_def, evaluate_type_def] >> metis_tac[]
QED

Theorem reason_literal_string_ptr_val:
  LENGTH str <= ml /\
  lookup_var p s = SOME (n2w b) /\
  FLOOKUP G p = SOME (b,32+32*word_size ml) /\
  op_taint tn' (Var p) = {} /\ b+32+32*word_size ml < dimword (:256) /\
  mem_word_at b s.vs_memory = n2w (LENGTH str) /\
  mem_bytes_at (b+32) (LENGTH str) s.vs_memory = MAP (n2w o ORD) str /\
  tn'.t_mem = (tn.t_mem UNION dirty) DIFF
    {i | b <= i /\ i < b+32+32*word_size (LENGTH str)} ==>
  ptr_val_ok cx (BaseT (StringT ml)) (StringV str) (Var p) G tn' s
Proof
  strip_tac >> drule_all reason_literal_string_representation >> strip_tac >>
  simp[ptr_val_ok_def, is_word_type_def] >>
  irule literal_clean_ptr_mem_ok >> simp[] >>
  `b < dimword (:256)` by decide_tac >>
  `word_size (LENGTH str) <= word_size ml` by
    metis_tac[exprSimHypsTheory.word_size_monotone] >>
  simp[wordsTheory.w2n_n2w, evaluate_type_def] >> rpt strip_tac >>
  gvs[] >> decide_tac
QED

