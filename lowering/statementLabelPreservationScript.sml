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

Theorem label_preserving_imm_store_word[local]:
  !s r t. compile_imm_store_word imm off v s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  Cases_on `imm` >> simp_tac pure_ss [compile_imm_store_word_def,
    optionTheory.option_CLAUSES]
  >- STMT_LEAF >> STMT_BIND >> STMT_LEAF
QED

Theorem label_preserving_imm_store_words[local]:
  !n imm src dst off s r t.
    compile_imm_store_words imm src dst n off s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  Induct >> rewrite_tac[compile_imm_store_words_def]
  >- STMT_LEAF >> ntac 4 gen_tac >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_lit_byte_offset] >> gen_tac >> STMT_BIND >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_lit_byte_offset] >> gen_tac >>
  ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
  >- metis_tac[label_preserving_imm_store_word] >> first_assum MATCH_ACCEPT_TAC
QED

val stmt_assign_leaves = stmt_label_leaves @
  [label_preserving_store_memory, label_preserving_typed_copy_mutual,
   label_preserving_copy_memory, label_preserving_imm_store_word,
   label_preserving_imm_store_words, label_preserving_dynarray_to_storage];
val ASSIGN_LEAF = rpt strip_tac >> metis_tac stmt_assign_leaves;
val ASSIGN_BIND = ho_match_mp_tac label_preserving_bind >> conj_tac
  >- ASSIGN_LEAF >> gen_tac;
val ASSIGN_IGNORE = ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
  >- ASSIGN_LEAF;

Theorem label_preserving_assign_value[local]:
  !s r t. compile_assign_value ce dst loc v prim src dt st di sz s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  Cases_on `loc` >> simp_tac pure_ss [compile_assign_value_def,
    compileEnvTheory.data_location_case_def]
  >- suspend "memory"
  >- suspend "storage"
  >- suspend "transient"
  >- suspend "code"
  >> suspend "calldata"
QED

Resume label_preserving_assign_value[memory]:
  IF_CASES_TAC >- ASSIGN_LEAF >> IF_CASES_TAC
  >- (simp_tac pure_ss [LET_THM] >> ntac 2 ASSIGN_BIND >>
      ASSIGN_IGNORE >> ASSIGN_LEAF) >> ASSIGN_LEAF
QED

Resume label_preserving_assign_value[storage]:
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (IF_CASES_TAC >- (ASSIGN_BIND >> ASSIGN_IGNORE >> ASSIGN_LEAF) >>
      ASSIGN_LEAF) >> gen_tac >> IF_CASES_TAC >- ASSIGN_LEAF >>
  Cases_on `di` >> simp_tac pure_ss [optionTheory.option_CLAUSES]
  >- (IF_CASES_TAC >- (ASSIGN_BIND >> ASSIGN_LEAF) >>
      rewrite_tac[compile_memory_to_storage_def] >> ASSIGN_IGNORE >> ASSIGN_LEAF) >>
  PairCases_on `x` >> simp_tac pure_ss [pairTheory.pair_case_thm] >> ASSIGN_LEAF
QED

Resume label_preserving_assign_value[transient]:
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (IF_CASES_TAC >- (ASSIGN_BIND >> ASSIGN_IGNORE >> ASSIGN_LEAF) >>
      ASSIGN_LEAF) >> gen_tac >> IF_CASES_TAC >- ASSIGN_LEAF >>
  Cases_on `di` >> simp_tac pure_ss [optionTheory.option_CLAUSES]
  >- (IF_CASES_TAC >- (ASSIGN_BIND >> ASSIGN_LEAF) >>
      rewrite_tac[compile_memory_to_transient_def] >> ASSIGN_IGNORE >> ASSIGN_LEAF) >>
  PairCases_on `x` >> simp_tac pure_ss [pairTheory.pair_case_thm] >> ASSIGN_LEAF
QED

Resume label_preserving_assign_value[calldata]:
  ASSIGN_IGNORE >> ASSIGN_LEAF
QED

Resume label_preserving_assign_value[code]:
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (IF_CASES_TAC >- (ASSIGN_BIND >> ASSIGN_IGNORE >> ASSIGN_LEAF) >>
      ASSIGN_LEAF) >> gen_tac >> IF_CASES_TAC >- ASSIGN_LEAF >>
  IF_CASES_TAC >- (ASSIGN_BIND >> ASSIGN_LEAF) >> ASSIGN_LEAF
QED

Finalise label_preserving_assign_value

Theorem label_preserving_tuple_load_all[local]:
  !tys ce ptr off s r t. compile_tuple_load_all ce ptr tys off s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  Induct >> rewrite_tac[compile_tuple_load_all_def] >>
  simp_tac pure_ss [LET_THM]
  >- STMT_LEAF >> ntac 4 gen_tac >> STMT_BIND >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (rewrite_tac[compile_load_memory_def] >> IF_CASES_TAC >> STMT_LEAF) >>
  gen_tac >> ho_match_mp_tac label_preserving_bind >> conj_tac
  >- first_assum MATCH_ACCEPT_TAC >> gen_tac >> STMT_LEAF
QED

Theorem label_preserving_store_at_loc[local]:
  !loc s r t. compile_store_at_loc imm dst v loc s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  Cases >> rewrite_tac[compile_store_at_loc_def]
  >- ASSIGN_LEAF >> Cases_on `x` >> rewrite_tac[compile_store_at_loc_def] >>
  ASSIGN_LEAF
QED

Theorem label_preserving_tuple_store_all[local]:
  !ce tys targets vals s r t.
    compile_tuple_store_all ce tys targets vals s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  recInduct compile_tuple_store_all_ind >> rpt conj_tac >>
  rewrite_tac[compile_tuple_store_all_def]
  >- STMT_LEAF
  >- suspend "target"
  >- suspend "other1"
  >- suspend "other2"
  >> STMT_LEAF
QED

Resume label_preserving_tuple_store_all[target]:
  ntac 7 gen_tac >> strip_tac >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (match_mp_tac label_preserving_get_target_ptr >>
      metis_tac[label_preserving_compile_expr]) >> gen_tac >>
  ntac 10 ASSIGN_BIND >>
  ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
  >- (rpt IF_CASES_TAC >>
      metis_tac[label_preserving_store_at_loc, label_preserving_assign_value,
        label_preserving_emit_void]) >> first_assum MATCH_ACCEPT_TAC
QED
Resume label_preserving_tuple_store_all[other1]:
  ntac 4 gen_tac >> strip_tac >> ASSIGN_IGNORE >> first_assum MATCH_ACCEPT_TAC
QED
Resume label_preserving_tuple_store_all[other2]:
  STMT_LEAF
QED
Finalise label_preserving_tuple_store_all

Theorem label_preserving_tuple_unpack[local]:
  !s r t. compile_tuple_unpack ce ty stage targets src s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[compile_tuple_unpack_def] >> simp_tac pure_ss [LET_THM] >>
  IF_CASES_TAC >- STMT_LEAF >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (IF_CASES_TAC >- (ntac 2 ASSIGN_BIND >> ASSIGN_IGNORE >> ASSIGN_LEAF) >>
      ASSIGN_LEAF) >> gen_tac >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_tuple_load_all] >> gen_tac >>
  metis_tac[label_preserving_tuple_store_all]
QED

Theorem label_preserving_range_bound_checks[local]:
  !s r t. compile_range_bound_checks lo hi rounds bound signed s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[compile_range_bound_checks_def] >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (IF_CASES_TAC >> STMT_LEAF) >> gen_tac >>
  STMT_BIND >> STMT_IGNORE >> ntac 2 STMT_BIND >> STMT_LEAF
QED

Theorem label_preserving_iter_elem_copy[local]:
  !s r t. compile_iter_elem_copy ce ep ip sz loc slot dt st s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[compile_iter_elem_copy_def] >> IF_CASES_TAC
  >- (IF_CASES_TAC
      >- (ho_match_mp_tac label_preserving_bind >> conj_tac
          >- metis_tac[label_preserving_ptr_load] >> gen_tac >> STMT_LEAF) >>
      rewrite_tac[compile_slot_to_memory_def] >> ASSIGN_IGNORE >> ASSIGN_LEAF) >>
  IF_CASES_TAC
  >- (IF_CASES_TAC
      >- (ho_match_mp_tac label_preserving_bind >> conj_tac
          >- metis_tac[label_preserving_ptr_load] >> gen_tac >> STMT_LEAF) >>
      Cases_on `loc` >> simp_tac pure_ss [compileEnvTheory.data_location_case_def] >>
      metis_tac[label_preserving_copy_memory, label_preserving_imm_copy_to_memory,
        label_preserving_emit_void]) >>
  IF_CASES_TAC >- (STMT_BIND >> STMT_LEAF) >> ASSIGN_LEAF
QED

Theorem label_preserving_declare_local[local]:
  !s r t. declare_local ce id ty s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[declare_local_def] >> simp_tac pure_ss [LET_THM] >>
  IF_CASES_TAC >- (STMT_BIND >> STMT_LEAF) >> STMT_LEAF
QED

Theorem label_preserving_emit_local_alloca[local]:
  !s r t. emit_local_alloca ce id s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[emit_local_alloca_def] >>
  Cases_on `FLOOKUP ce.ce_vars id` >> simp_tac pure_ss [optionTheory.option_CLAUSES]
  >- STMT_LEAF >> Cases_on `x` >>
  simp_tac (srw_ss()) [] >>
  all_tac >~ [`FLOOKUP _ _ = SOME (PtrVar op sz)`]
  >- (Cases_on `op` >> simp_tac (srw_ss()) [] >> STMT_LEAF) >>
  STMT_LEAF
QED

Theorem label_preserving_declare_stmt_local[local]:
  !stmt s r t. declare_stmt_local ce stmt s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  Cases >> rewrite_tac[declare_stmt_local_def] >>
  metis_tac[label_preserving_declare_local, label_preserving_return]
QED

Theorem label_preserving_internal_return_from_env[local]:
  !s r t. compile_internal_return_from_env ce ty sty v rpc s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[compile_internal_return_from_env_def] >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (Cases_on `ce.ce_return_buf` >>
      simp_tac pure_ss [optionTheory.option_CLAUSES]
      >- STMT_LEAF >> Cases_on `x` >> simp_tac (srw_ss()) [] >>
      all_tac >~ [`emit_op MLOAD`] >- (STMT_BIND >> STMT_LEAF) >> STMT_LEAF) >>
  gen_tac >> STMT_BIND >> metis_tac[label_preserving_internal_return]
QED


Theorem label_preserving_reason_message[local]:
  !e s r t. compile_reason_message ce e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  Cases >> simp_tac (srw_ss()) [compile_reason_message_def] >>
  all_tac >~ [`Literal ty lit`] >-
    (Cases_on `ty` >> simp_tac (srw_ss()) [compile_reason_message_def] >>
     all_tac >~ [`Literal (BaseT bt) lit`] >-
       (Cases_on `bt` >> simp_tac (srw_ss()) [compile_reason_message_def] >>
        all_tac >~ [`Literal (BaseT (StringT n)) lit`] >-
          (Cases_on `lit` >> simp_tac (srw_ss()) [compile_reason_message_def] >>
           all_tac >~ [`compile_bytelike_literal`] >-
             (ho_match_mp_tac label_preserving_bind >> conj_tac
              >- metis_tac[label_preserving_bytelike_literal] >> gen_tac >> STMT_LEAF) >>
           metis_tac[label_preserving_compile_expr]) >>
        metis_tac[label_preserving_compile_expr]) >>
     metis_tac[label_preserving_compile_expr]) >>
  metis_tac[label_preserving_compile_expr]
QED

Theorem label_preserving_compile_stmt_mutual:
  (!ce lc ty stmt s r t. compile_stmt ce lc ty stmt s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) /\
  (!ce lc ty stmts s r t. compile_stmts ce lc ty stmts s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t))
Proof
  ho_match_mp_tac compile_stmt_ind >> rpt conj_tac
  >- suspend "pass" >- suspend "expr" >- suspend "annassign"
  >- suspend "assign" >- suspend "augassign" >- suspend "assert_bare"
  >- suspend "assert_unreachable" >- suspend "assert_reason" >- suspend "log"
  >- suspend "raise_bare" >- suspend "raise_unreachable" >- suspend "raise_reason"
  >- suspend "return_none" >- suspend "return_some" >- suspend "append"
  >- suspend "tuple" >- suspend "if" >- suspend "range" >- suspend "iter"
  >- (rewrite_tac[compile_stmt_def] >> STMT_LEAF)
  >- (rewrite_tac[compile_stmt_def] >> STMT_LEAF)
  >- (rewrite_tac[compile_stmt_def] >> STMT_IGNORE >> STMT_LEAF)
  >- (rewrite_tac[compile_stmt_def] >> STMT_IGNORE >> STMT_LEAF)
  >- (rewrite_tac[compile_stmt_def] >> STMT_IGNORE >> STMT_LEAF)
  >- (rewrite_tac[compile_stmt_def] >> STMT_IGNORE >> STMT_LEAF)
  >- (rewrite_tac[compile_stmt_def] >> STMT_LEAF)
  >> suspend "cons"
QED

Resume label_preserving_compile_stmt_mutual[pass]:
  rewrite_tac[compile_stmt_def] >> STMT_LEAF
QED

Resume label_preserving_compile_stmt_mutual[expr]:
  ntac 4 gen_tac >> rewrite_tac[compile_stmt_def] >>
  ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
  >- metis_tac[label_preserving_compile_expr] >> STMT_LEAF
QED

Resume label_preserving_compile_stmt_mutual[raise_bare]:
  rewrite_tac[compile_stmt_def] >> STMT_LEAF
QED

Resume label_preserving_compile_stmt_mutual[raise_unreachable]:
  rewrite_tac[compile_stmt_def] >> STMT_LEAF
QED

Resume label_preserving_compile_stmt_mutual[assert_bare]:
  ntac 4 gen_tac >> rewrite_tac[compile_stmt_def] >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_stmt_lower_value] >> gen_tac >>
  ntac 2 STMT_FRESH >> rewrite_tac[comp_ignore_bind_def] >>
  ntac 4 STMT_BIND >> STMT_LEAF
QED

Resume label_preserving_compile_stmt_mutual[assert_unreachable]:
  ntac 4 gen_tac >> rewrite_tac[compile_stmt_def] >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_stmt_lower_value] >> gen_tac >>
  ntac 2 STMT_FRESH >> rewrite_tac[comp_ignore_bind_def] >>
  ntac 4 STMT_BIND >> STMT_LEAF
QED

Resume label_preserving_compile_stmt_mutual[raise_reason]:
  ntac 4 gen_tac >> rewrite_tac[compile_stmt_def] >>
  simp_tac pure_ss [LET_THM] >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_reason_message] >> gen_tac >>
  metis_tac[label_preserving_revert_reason]
QED

Resume label_preserving_compile_stmt_mutual[assert_reason]:
  ntac 5 gen_tac >> rewrite_tac[compile_stmt_def] >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_stmt_lower_value] >> gen_tac >>
  ntac 2 STMT_FRESH >> rewrite_tac[comp_ignore_bind_def] >>
  ntac 4 STMT_BIND >> ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_reason_message] >> gen_tac >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_revert_reason] >> gen_tac >> STMT_BIND >> STMT_LEAF
QED

Resume label_preserving_compile_stmt_mutual[tuple]:
  ntac 5 gen_tac >> rewrite_tac[compile_stmt_def] >> simp_tac pure_ss [LET_THM] >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_compile_expr] >> gen_tac >> STMT_BIND >>
  metis_tac[label_preserving_tuple_unpack]
QED

Resume label_preserving_compile_stmt_mutual[augassign]:
  ntac 7 gen_tac >> rewrite_tac[compile_stmt_def] >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (match_mp_tac label_preserving_get_target_ptr >>
      metis_tac[label_preserving_compile_expr]) >> gen_tac >> ntac 2 STMT_BIND >>
  Cases_on `FST (SND a)` >> simp_tac pure_ss [optionTheory.option_CLAUSES]
  >- STMT_LEAF >> ntac 3 STMT_BIND >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_stmt_lower_value] >> gen_tac >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_binop] >> gen_tac >> STMT_LEAF
QED
