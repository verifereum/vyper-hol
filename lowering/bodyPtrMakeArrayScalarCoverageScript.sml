(* Word layout and source provenance for the scalar MLOAD boundary. *)
Theory bodyPtrMakeArrayScalarCoverage
Ancestors
  bodyPtrDefs exprSimProps loweringPosts vyperValue valueEncoding
  context venomState ptrDiscipline compileEnv

Theorem scalar_word_layout:
  is_word_type t /\ evaluate_type tenv t = SOME ty ==>
  val_footprint ty v = 32 /\ val_store_size ty v = 32
Proof
  Cases_on `t` >> gvs[is_word_type_def]
  >- (rename1 `is_word_type (BaseT bt)` >> Cases_on `bt` >>
      gvs[is_word_type_def]
      >~ [`is_word_type (BaseT (BytesT bd))`] >-
        (Cases_on `bd` >> gvs[is_word_type_def] >>
         simp[evaluate_type_def] >> rpt strip_tac >> gvs[] >>
         Cases_on `v` >> simp[val_footprint_def, val_store_size_def, type_memory_size_def]) >>
      simp[evaluate_type_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
      Cases_on `v` >> simp[val_footprint_def, val_store_size_def, type_memory_size_def]) >>
  simp[evaluate_type_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  Cases_on `v` >> simp[val_footprint_def, val_store_size_def, type_memory_size_def]
QED

Theorem scalar_memory_source_coverage:
  is_word_type t /\ evaluate_type (get_tenv cx) t = SOME ty /\
  ptr_mem_ok cx t v op G tn s /\
  eval_operand op s = SOME a /\ op_taint tn op = {} ==>
  ?src. op = Var src /\ ptr_covers G tn src s 32
Proof
  strip_tac >>
  `val_footprint ty v = 32 /\ val_store_size ty v = 32`
    by metis_tac[scalar_word_layout] >>
  gvs[ptr_mem_ok_def] >>
  simp[ptr_covers_def] >>
  gvs[eval_operand_def, lookup_var_def, op_taint_def] >> metis_tac[]
QED
