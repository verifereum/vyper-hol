(* Literal slots use the child's annotation.  The source buffer may have
   a different bytestring capacity, but the reserved destination does not. *)
Theory bodyPtrMakeArrayConsLayout
Ancestors
  bodyPtrMakeArrayLayoutTransport exprSimHyps exprSimProps valueCopyBytes
  exprSimHypsDefs abiValueEncoding vyperTyping valueEncoding vfmConstants vyperValue loweringPosts compileEnv context

Theorem literal_annotation_slot:
  expr_body_pre ce cx env e es /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  (~is_word_type (expr_type e) ==> type_memory_size tv < 2 ** 64) /\
  (is_word_type (expr_type e) ==> type_memory_size tv = 32) /\
  (!v. val_wf tv v ==> val_footprint tv v <= type_memory_bytes ce (expr_type e))
Proof
  strip_tac >>
  `expr_sim_inv ce cx env es` by gvs[expr_body_pre_def] >>
  `type_memory_bytes ce (expr_type e) = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  simp[] >> conj_tac
  >- (strip_tac >> drule_all expr_body_pre_copy_ok >> simp[]) >>
  metis_tac[abi_word_type_size, val_footprint_le]
QED

Theorem literal_nonbytes_source_layout:
  expr_body_pre ce cx env e es /\
  (int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  ~is_bytestring_type (expr_type e) ==>
  lowered_value_type ce e = expr_type e
Proof
  strip_tac >> Cases_on `lowered_value_type ce e = expr_type e` >> simp[] >>
  `well_typed_expr env e /\ int_calls_expr e = []` by gvs[expr_body_pre_def] >>
  drule_all call_free_lowered_bytestring_family >>
  disch_then (qspec_then `ce` strip_assume_tac) >> gvs[is_bytestring_type_def]
QED

Theorem literal_bytes_runtime_slot:
  is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v ==>
  ?len.
    ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
     (?str. v = StringV str /\ len = LENGTH str)) /\
    val_footprint tv v <= 32+32*((len+31) DIV 32) /\
    32+32*((len+31) DIV 32) <= type_memory_size tv
Proof
  strip_tac >> drule_all bytestring_type_value >> strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def, val_footprint_def, type_memory_size_def] >>
  metis_tac[word_size_monotone, le_word_size_mul, word_size_def,
    arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_MONO_MULT]
QED
