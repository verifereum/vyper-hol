(* Checked interface diagnostics: lowered capacity is not annotated capacity. *)
Theory stmtSimCustomErrorPtrInterfaceProbe
Ancestors
  stmtSimCustomErrorPtrUnwrap stmtSimCustomErrorPtrStoreHead
  exprSimAggregateLoops bodyMemAggregateStore annAssignPtrMemorySource
  exprLowering compileEnv bodyPtrDefs ptrDiscipline venomState words finite_map

Theorem custom_error_literal_capacity_mismatch[local]:
  lowered_value_type ce (Literal (BaseT (StringT 128)) (StringL "a")) =
    BaseT (StringT 1) /\
  expr_type (Literal (BaseT (StringT 128)) (StringL "a")) = BaseT (StringT 128) /\
  type_memory_bytes ce (BaseT (StringT 1)) = 64 /\
  type_memory_bytes ce (BaseT (StringT 128)) = 160
Proof
  simp[exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def,
       compileEnvTheory.type_memory_bytes_def]
QED

Theorem custom_error_literal_buffer_not_annotated[local]:
  lookup_var p s = SOME (0w:256 word) /\ FLOOKUP G p = SOME (0,64) /\
  op_taint tn (Var p) = {} ==>
  ptr_buf_ok ce (Literal (BaseT (StringT 128)) (StringL "a")) (Var p) G s /\
  ptr_covers G tn p s 64 /\ ~ptr_covers G tn p s 160
Proof
  simp[bodyPtrDefsTheory.ptr_buf_ok_def, bodyPtrDefsTheory.ptr_covers_def,
       venomStateTheory.eval_operand_def, exprLoweringTheory.lowered_value_type_def,
       compileEnvTheory.type_memory_bytes_def] >> strip_tac >> simp[]
QED

(* Robust pointer representation itself covers the padded runtime store size;
   no annotated-capacity buffer premise is required for a positive footprint. *)
Theorem custom_error_runtime_source_coverage[local]:
  ~is_word_type typ /\ ptr_val_ok cx typ v (Var p) G tn s /\
  evaluate_type (get_tenv cx) typ = SOME tv /\ lookup_var p s = SOME w /\
  val_footprint tv v <> 0 ==>
  ptr_covers G tn p s (val_store_size tv v)
Proof
  simp[bodyPtrDefsTheory.ptr_val_ok_def, bodyPtrDefsTheory.ptr_mem_ok_def,
       bodyPtrDefsTheory.ptr_covers_def, venomStateTheory.eval_operand_def] >>
  metis_tac[]
QED

(* A zero-size same-layout store reads no source bytes. *)
Theorem custom_error_zero_store[local]:
  ~is_word_type typ /\ ~is_bytestring_type typ /\
  type_memory_bytes ce typ = 0 ==>
  compile_store_memory ce src dst typ typ su = ((),su)
Proof
  simp[contextTheory.compile_store_memory_def,
       contextPropsTheory.compile_copy_memory_zero]
QED

(* For a nonbytestring with nonzero source buffer, the literal-size
   exception is absent and the expression's buffer contract is enough. *)
Theorem custom_error_nonbytes_buffer_coverage[local]:
  (lowered_value_type ce e = expr_type e \/ is_bytestring_type (expr_type e)) /\
  ~is_bytestring_type (expr_type e) /\
  type_memory_bytes ce (expr_type e) <> 0 /\
  ptr_buf_ok ce e (Var p) G s /\
  ptr_val_ok cx (expr_type e) v (Var p) G tn s /\
  lookup_var p s = SOME w ==>
  ptr_covers G tn p s (type_memory_bytes ce (expr_type e))
Proof
  simp[bodyPtrDefsTheory.ptr_buf_ok_def, bodyPtrDefsTheory.ptr_val_ok_def,
       bodyPtrDefsTheory.ptr_covers_def, venomStateTheory.eval_operand_def] >>
  metis_tac[]
QED

Theorem custom_error_bytestring_store_size[local]:
  is_bytestring_type typ /\ evaluate_type tenv typ = SOME tv /\
  value_has_type tv v ==>
  ?payload_len. val_footprint tv v = 32 + payload_len /\
    val_store_size tv v = 32 + 32 * ((payload_len + 31) DIV 32)
Proof
  strip_tac >>
  `(?n. tv = BaseTV (BytesT (Dynamic n))) \/
   (?n. tv = BaseTV (StringT n))` by
    metis_tac[valueCopyBytesTheory.bytestring_type_value] >>
  Cases_on `v` >>
  gvs[vyperTypingTheory.value_has_type_def,
      loweringPostsTheory.val_footprint_def, exprSimPropsTheory.val_store_size_def,
      vfmConstantsTheory.word_size_def]
QED
