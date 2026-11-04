(* Statement compilation extends code using generated-label namespaces only. *)
Theory statementLabelPreservation
Ancestors
  expressionLabelPreservation entryLabelPreservation stmtLowering moduleLowering
  loweringShapeDefs compileEnv emitHelper list context decoderLabelPreservation

Theorem label_preserving_stmt_lower_value[local]:
  !s r t. lower_value compile_expr cenv ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  match_mp_tac label_preserving_lower_value >>
  metis_tac[label_preserving_compile_expr]
QED

Theorem label_preserving_log_eval_all[local]:
  !es cenv s r t. compile_log_eval_all cenv es s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  Induct >> gen_tac >> rewrite_tac[compile_log_eval_all_def] >>
  simp_tac pure_ss [LET_THM]
  >- metis_tac[label_preserving_return] >> gen_tac >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_stmt_lower_value] >> gen_tac >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- first_assum MATCH_ACCEPT_TAC >> gen_tac >>
  metis_tac[label_preserving_return]
QED

Theorem label_preserving_encode_log_topic[local]:
  !s r t. compile_encode_log_topic v bs s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[compile_encode_log_topic_def] >> Cases_on `bs` >> simp[]
  >- (ho_match_mp_tac label_preserving_bind >> conj_tac
      >- metis_tac[label_preserving_emit_op] >> gen_tac >>
      ho_match_mp_tac label_preserving_bind >> conj_tac
      >- metis_tac[label_preserving_emit_op] >> gen_tac >>
      metis_tac[label_preserving_emit_op]) >>
  metis_tac[label_preserving_return]
QED

Theorem label_preserving_log_topic_ops[local]:
  !ops s r t. compile_log_topic_ops ops s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  Induct >> rewrite_tac[compile_log_topic_ops_def]
  >- metis_tac[label_preserving_return] >> gen_tac >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_encode_log_topic] >> gen_tac >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- first_assum MATCH_ACCEPT_TAC >> gen_tac >>
  metis_tac[label_preserving_return]
QED

Theorem label_preserving_log_store_data[local]:
  !ops cenv buf off s r t. compile_log_store_data cenv ops buf off s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  Induct >> rewrite_tac[compile_log_store_data_def] >>
  simp_tac pure_ss [LET_THM]
  >- metis_tac[label_preserving_return] >> ntac 4 gen_tac >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_emit_op] >> gen_tac >>
  ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
  >- (rpt IF_CASES_TAC >>
      metis_tac[label_preserving_emit_void, label_preserving_store_bytestring]) >>
  first_assum MATCH_ACCEPT_TAC
QED

val stmt_label_leaves = [label_preserving_return, label_preserving_emit_inst,
  label_preserving_emit_op, label_preserving_emit_void,
  label_preserving_abi_alloc_buffer, label_preserving_unwrap_value];
val STMT_LEAF = rpt strip_tac >> metis_tac stmt_label_leaves;
val STMT_BIND = ho_match_mp_tac label_preserving_bind >> conj_tac
  >- STMT_LEAF >> gen_tac;
val STMT_IGNORE = ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
  >- STMT_LEAF;

Theorem label_preserving_revert_reason[local]:
  !s r t. compile_revert_with_reason cenv vv ty sz s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[compile_revert_with_reason_def] >> simp_tac pure_ss [LET_THM] >>
  STMT_BIND >> simp_tac pure_ss [LET_THM] >>
  STMT_IGNORE >> STMT_BIND >> STMT_BIND >> simp_tac pure_ss [LET_THM] >>
  ntac 5 STMT_BIND >> STMT_IGNORE >> STMT_BIND >>
  simp_tac pure_ss [LET_THM] >>
  STMT_IGNORE >> ntac 8 STMT_BIND >> STMT_IGNORE >>
  STMT_BIND >> STMT_IGNORE >> ntac 3 STMT_BIND >>
  STMT_IGNORE >> STMT_BIND >> STMT_IGNORE >>
  ntac 3 STMT_BIND >> STMT_LEAF
QED

Theorem label_preserving_nonreentrant_unlock[local]:
  !s r t. compile_nonreentrant_unlock key trans view s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[compile_nonreentrant_unlock_def] >>
  rpt IF_CASES_TAC >> STMT_LEAF
QED

Theorem label_preserving_load_tuple_elements[local]:
  !tys cenv ptr off s r t.
    compile_load_tuple_elements cenv ptr tys off s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  Induct >> rewrite_tac[compile_load_tuple_elements_def] >>
  simp_tac pure_ss [LET_THM]
  >- STMT_LEAF >> ntac 4 gen_tac >> ntac 2 STMT_BIND >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- first_assum MATCH_ACCEPT_TAC >> gen_tac >> STMT_LEAF
QED

Theorem label_preserving_internal_return[local]:
  !s r t. compile_internal_return ce rv pc nrets rt src elems buf s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[compile_internal_return_def] >> IF_CASES_TAC
  >- (Cases_on `rv` >> simp_tac pure_ss [optionTheory.option_CLAUSES]
      >- STMT_LEAF >> IF_CASES_TAC
      >- STMT_LEAF >>
      ho_match_mp_tac label_preserving_bind >> conj_tac
      >- metis_tac[label_preserving_load_tuple_elements] >> gen_tac >> STMT_LEAF) >>
  Cases_on `buf` >> simp_tac pure_ss [optionTheory.option_CLAUSES]
  >- STMT_LEAF >> Cases_on `rv` >> simp_tac pure_ss [optionTheory.option_CLAUSES]
  >- STMT_LEAF >>
  ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
  >- metis_tac[label_preserving_store_memory] >> STMT_LEAF
QED

Theorem label_preserving_external_return[local]:
  !s r t. compile_external_return rv prim raw info sz nr key trans view s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[compile_external_return_def] >>
  ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >>
      metis_tac[label_preserving_nonreentrant_unlock, label_preserving_return]) >>
  Cases_on `rv` >> simp_tac pure_ss [optionTheory.option_CLAUSES]
  >- STMT_LEAF >> IF_CASES_TAC
  >- (ntac 2 STMT_BIND >> STMT_LEAF) >> IF_CASES_TAC
  >- (ntac 2 STMT_BIND >> STMT_IGNORE >> STMT_LEAF) >>
  ntac 2 STMT_BIND >> ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_abi_encode_mutual] >> gen_tac >> STMT_LEAF
QED

val stmt_label_leaves = stmt_label_leaves @ [label_preserving_fresh_var,
  label_preserving_new_block, label_preserving_word_copy_loop];
val STMT_LEAF = rpt strip_tac >> metis_tac stmt_label_leaves;
val STMT_BIND = ho_match_mp_tac label_preserving_bind >> conj_tac
  >- STMT_LEAF >> gen_tac;
val STMT_FRESH = ho_match_mp_tac
    (Q.ISPEC `jump_label_ok` label_preserving_bind_result) >> conj_tac
  >- metis_tac[label_preserving_fresh_label] >> gen_tac >> strip_tac;

Theorem label_preserving_dynarray_to_storage[local]:
  !s r t. compile_dynarray_to_storage src dst ew ems trans s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[compile_dynarray_to_storage_def] >> STMT_BIND >>
  ntac 3 STMT_FRESH >> rewrite_tac[comp_ignore_bind_def] >>
  ntac 8 STMT_BIND >> IF_CASES_TAC
  >- (ntac 6 STMT_BIND >>
      ho_match_mp_tac label_preserving_bind >> conj_tac
      >- (IF_CASES_TAC >> STMT_LEAF) >> gen_tac >>
      ntac 4 STMT_BIND >> IF_CASES_TAC >> STMT_LEAF) >>
  ntac 11 STMT_BIND >> IF_CASES_TAC >> STMT_LEAF
QED
