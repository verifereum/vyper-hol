(* Statement boundaries consume the expression certificate, not its proof. *)
Theory runtimeLabelStmt
Ancestors
  runtimeLabelExprCallbacks runtimeLabelExprPrimitives runtimeLabelBuiltinArithmetic
  runtimeLabelStmtIO runtimeLabelPrimitives runtimeLabelInvariant runtimeLabelValues runtimeLabelBuiltins runtimeLabelABI
  stmtLowering exprLowering compileEnv context emitHelper venomInst list

Theorem rb_compile_mcopy_guard_for[local]:
  (rb_step_for source_checks) (K T) action ==> (rb_step_for source_checks) (K T) (compile_mcopy_guard ce action)
Proof
  simp[compile_mcopy_guard_def] >> strip_tac >>
  Cases_on `ce.ce_target CapMcopy` >> simp[rb_emit_inst_for]
QED

Theorem rb_compile_revert_with_reason_for[local]:
  (rb_env_ok_for source_checks) ce /\ (rb_value_ok_for source_checks) msg ==>
  (rb_step_for source_checks) (K T) (compile_revert_with_reason ce msg ty n)
Proof
  strip_tac >> pure_rewrite_tac[compile_revert_with_reason_def, LET_THM] >>
  BETA_TAC >>
  irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer_for] >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer_for] >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_unwrap_value_for] >> gen_tac >> strip_tac >>
  rpt (irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer_for] >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  rpt (irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  rpt (irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  rpt (irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  simp[rb_emit_inst_for]
QED

Theorem rb_compile_revert_with_custom_error_for[local]:
  (rb_expr_contract_for source_checks) /\ (rb_env_ok_for source_checks) ce ==>
  (rb_step_for source_checks) (K T) (compile_revert_with_custom_error ce err)
Proof
  strip_tac >> Cases_on `err` >>
  rename1 `CustomError id positional kwargs` >>
  pure_rewrite_tac[compile_revert_with_custom_error_def, LET_THM] >> BETA_TAC >>
  Cases_on `ce.ce_error_info (nsid_to_string id)` >> simp[rb_emit_inst_for] >>
  irule rb_step_bind_for >>
  qexists_tac `EVERY (rb_value_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- (irule rb_compile_ext_call_args_for >>
    gvs[rb_expr_contract_for_def]) >>
  gen_tac >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer_for] >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  irule rb_bind_return_for >> BETA_TAC >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  IF_CASES_TAC
  >- (irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      simp[rb_emit_inst_for]) >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- (irule rb_compile_abi_encode_values_to_buf_for >>
    simp[rb_abi_encode_for, rb_every_zip_fst]) >>
  gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  simp[rb_emit_inst_for]
QED

Theorem rb_compile_reason_message_for[local]:
  !ce e. (rb_expr_contract_for source_checks) /\ (rb_env_ok_for source_checks) ce ==>
  (rb_step_for source_checks) (rb_value_ok_for source_checks) (compile_reason_message ce e)
Proof
  recInduct compile_reason_message_ind >> rpt strip_tac >>
  simp[compile_reason_message_def]
  >- (irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >> BETA_TAC >>
      reverse conj_tac >- simp[rb_compile_bytelike_literal_for] >>
      simp[rb_step_return_for, rb_value_ok_for_def, rb_base_ptr_for]) >>
  gvs[rb_expr_contract_for_def]
QED

Theorem rb_compile_range_bound_checks_for[local]:
  (rb_operand_ok_for source_checks) start /\ (rb_operand_ok_for source_checks) stop /\ (rb_operand_ok_for source_checks) rounds ==>
  (rb_step_for source_checks) (K T) (compile_range_bound_checks start stop rounds bound signed)
Proof
  strip_tac >> pure_rewrite_tac[compile_range_bound_checks_def] >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- (Cases_on `signed` >> simp[rb_emit_op_for]) >>
  gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  simp[rb_emit_void_for]
QED

Theorem rb_compile_iter_elem_copy_for[local]:
  (rb_env_ok_for source_checks) ce /\ (rb_operand_ok_for source_checks) elem /\ (rb_operand_ok_for source_checks) item ==>
  (rb_step_for source_checks) (K T) (compile_iter_elem_copy ce elem item n loc slots tty ety)
Proof
  strip_tac >> pure_rewrite_tac[compile_iter_elem_copy_def] >>
  Cases_on `slots` >> simp[]
  >- (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_compile_slot_to_memory_for, rb_step_return_for]) >>
  Cases_on `loc <> LocMemory` >> simp[]
  >- (Cases_on `n <= 32` >> simp[]
      >- (irule rb_bind_ptr_load_for >> BETA_TAC >>
          gvs[rb_env_ok_for_def, rb_emit_void_for]) >>
      Cases_on `loc` >> simp[rb_emit_void_for, rb_compile_copy_memory_for,
        rb_compile_imm_copy_to_memory_for] >>
      gvs[rb_env_ok_for_def, rb_compile_imm_copy_to_memory_for]) >>
  Cases_on `is_word_type tty` >> simp[]
  >- (irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      simp[rb_emit_void_for]) >>
  simp[rb_compile_store_memory_for]
QED

Theorem rb_compile_assign_value_for[local]:
  (rb_env_ok_for source_checks) ce /\ (rb_operand_ok_for source_checks) dst /\ (rb_operand_ok_for source_checks) src ==>
  (rb_step_for source_checks) (K T) (compile_assign_value ce dst loc src prim sloc dty sty n)
Proof
  strip_tac >> pure_rewrite_tac[compile_assign_value_def] >>
  Cases_on `loc` >> simp[]
  >- (Cases_on `prim` >> simp[rb_emit_void_for] >>
      Cases_on `sloc = SOME LocMemory` >> simp[rb_compile_store_memory_for] >>
      irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >> BETA_TAC >>
      reverse conj_tac >- simp[rb_compile_alloc_buffer_for] >>
      gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
      irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
      reverse conj_tac >- simp[rb_step_return_for] >> gen_tac >> strip_tac >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_compile_copy_memory_for, rb_compile_store_memory_for])
  >~ [`emit_inst INVALID [] []`]
  >- (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_inst_for, rb_step_return_for]) >>
  (irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac
  >- (IF_CASES_TAC >> simp[rb_step_return_for] >>
      irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >> BETA_TAC >>
      reverse conj_tac >- simp[rb_compile_alloc_buffer_for] >>
      gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[cj 1 rb_typed_memory_for, rb_step_return_for]) >>
  gen_tac >> strip_tac >>
  Cases_on `prim` >> simp[rb_emit_void_for, cj 1 rb_slots_for] >>
  gvs[rb_env_ok_for_def, rb_compile_imm_store_word_for] >>
  Cases_on `is_bytestring_type dty` >> simp[rb_compile_store_immutable_bytestring_for] >>
  Cases_on `n <= 32` >> simp[rb_compile_imm_store_words_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_compile_imm_store_word_for])
QED

Theorem rb_compile_tuple_load_all_for[local]:
  !tys offset. (rb_operand_ok_for source_checks) src ==>
  (rb_step_for source_checks) (EVERY (rb_operand_ok_for source_checks)) (compile_tuple_load_all ce src tys offset)
Proof
  Induct >> simp[compile_tuple_load_all_def, rb_step_return_for] >> rpt strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_load_memory_for] >> gen_tac >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `EVERY (rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[] >> simp[rb_step_return_for]
QED

Theorem rb_compile_store_at_loc_for[local]:
  (rb_operand_ok_for source_checks) dst /\ (rb_operand_ok_for source_checks) v /\
  (case imm of NONE => T | SOME op => (rb_operand_ok_for source_checks) op) ==>
  (rb_step_for source_checks) (K T) (compile_store_at_loc imm dst v loc)
Proof
  Cases_on `loc` >> simp[compile_store_at_loc_def, rb_emit_void_for] >>
  rename1 `SOME l` >> Cases_on `l` >>
  simp[compile_store_at_loc_def, rb_emit_void_for, rb_compile_imm_store_word_for]
QED

Theorem rb_compile_tuple_store_all_for[local]:
  !ce tys targets vals. (rb_expr_contract_for source_checks) /\ (rb_env_ok_for source_checks) ce /\ EVERY (rb_operand_ok_for source_checks) vals ==>
  (rb_step_for source_checks) (K T) (compile_tuple_store_all ce tys targets vals)
Proof
  recInduct compile_tuple_store_all_ind >> rpt strip_tac >>
  simp[compile_tuple_store_all_def, rb_step_return_for]
  >- (irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks) o FST` >> BETA_TAC >>
      reverse conj_tac
      >- (irule rb_compile_get_target_ptr_for >> gvs[rb_expr_contract_for_def]) >>
      gen_tac >> strip_tac >>
      rpt (irule rb_bind_return_for >> BETA_TAC) >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> reverse conj_tac >- gvs[] >>
      Cases_on `is_word_type src_ty` >> simp[]
      >- (Cases_on `is_word_type (case SND (SND x) of SOME (ValPT t) => t | _ => src_ty)` >>
          simp[rb_emit_void_for] >> irule rb_compile_store_at_loc_for >>
          gvs[rb_env_ok_for_def]) >>
      irule rb_compile_assign_value_for >> gvs[]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> gvs[rb_emit_void_for]
QED

Theorem rb_compile_tuple_unpack_for[local]:
  (rb_expr_contract_for source_checks) /\ (rb_env_ok_for source_checks) ce /\ (rb_operand_ok_for source_checks) src ==>
  (rb_step_for source_checks) (K T) (compile_tuple_unpack ce ty stage targets src)
Proof
  strip_tac >> pure_rewrite_tac[compile_tuple_unpack_def, LET_THM] >>
  BETA_TAC >> IF_CASES_TAC >- simp[rb_emit_inst_for] >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac
  >- (IF_CASES_TAC >> simp[rb_step_return_for] >>
      irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >> BETA_TAC >>
      reverse conj_tac >- simp[rb_compile_alloc_buffer_for] >>
      gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
      irule rb_bind_return_for >> BETA_TAC >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_void_for, rb_step_return_for]) >>
  gen_tac >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `EVERY (rb_operand_ok_for source_checks)` >> BETA_TAC >>
  simp[rb_compile_tuple_load_all_for, rb_compile_tuple_store_all_for]
QED

Theorem rb_emit_jmp_if_not_terminated_for[local]:
  (rb_operand_ok_for source_checks) (Label l) ==> (rb_step_for source_checks) (K T) (emit_jmp_if_not_terminated l)
Proof
  strip_tac >> rewrite_tac[emit_jmp_if_not_terminated_def] >>
  irule rb_step_bind_for >> qexists_tac `K T` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_step_for_def, comp_get_def] >>
  gen_tac >> strip_tac >> IF_CASES_TAC >> simp[rb_step_return_for, rb_emit_inst_for]
QED

Theorem compile_stmts_label_checks:
  (rb_expr_contract_for source_checks) ==> (rb_stmt_contract_for source_checks)
Proof
  strip_tac >> rewrite_tac[rb_stmt_contract_for_def] >>
  ho_match_mp_tac compile_stmt_ind >> rpt strip_tac >>
  simp[Once compile_stmt_def, rb_step_return_for, rb_emit_inst_for,
       rb_loop_ok_for_def]
  >- suspend "expr"
  >- suspend "annassign"
  >- suspend "assign"
  >- suspend "augassign"
  >- suspend "assert_bare"
  >- suspend "assert_unreachable"
  >- suspend "assert_reason"
  >- suspend "assert_custom"
  >- suspend "log"
  >- suspend "raise_reason"
  >- suspend "raise_custom"
  >- suspend "return_none"
  >- suspend "return_some"
  >- suspend "append"
  >- suspend "tuple"
  >- suspend "if"
  >- suspend "range"
  >- suspend "iter"
  >- suspend "break"
  >- suspend "continue"
  >- suspend "catchall1"
  >- suspend "catchall2"
  >> suspend "stmts"
QED
Resume compile_stmts_label_checks[expr]:
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac
  >- (irule rb_step_weaken_for >> qexists_tac `(rb_value_ok_for source_checks)` >>
      gvs[rb_expr_contract_for_def]) >> simp[rb_step_return_for]
QED
Resume compile_stmts_label_checks[annassign]:
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_local_alloca_for] >>
  irule rb_step_bind_for >> qexists_tac `(rb_value_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- gvs[rb_expr_contract_for_def] >> gen_tac >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac
  >- (IF_CASES_TAC >> simp[rb_step_return_for, rb_unwrap_value_for]) >>
  gen_tac >> strip_tac >> irule rb_bind_return_for >> BETA_TAC >>
  Cases_on `FLOOKUP env.ce_vars id` >> simp[rb_emit_void_for] >>
  rename1 `FLOOKUP _ _ = SOME loc` >>
  `(rb_location_ok_for source_checks) loc` by metis_tac[rb_env_ok_for_def] >>
  Cases_on `loc` >> gvs[rb_location_ok_for_def, rb_emit_void_for] >>
  IF_CASES_TAC >> simp[rb_emit_void_for, rb_compile_assign_value_for]
QED


Resume compile_stmts_label_checks[assign]:
  IF_CASES_TAC
  >- (irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks) o FST` >> BETA_TAC >>
      reverse conj_tac
      >- (irule rb_compile_get_target_ptr_for >> gvs[rb_expr_contract_for_def]) >>
      gen_tac >> strip_tac >> irule rb_compile_store_at_loc_for >>
      gvs[rb_env_ok_for_def]) >>
  irule rb_step_bind_for >> qexists_tac `(rb_value_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- gvs[rb_expr_contract_for_def] >> gen_tac >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `(rb_value_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac
  >- (IF_CASES_TAC >> simp[rb_compile_snapshot_vv_for, rb_vv_with_type_for, rb_step_return_for]) >>
  gen_tac >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks) o FST` >> BETA_TAC >>
  reverse conj_tac
  >- (irule rb_compile_get_target_ptr_for >> gvs[rb_expr_contract_for_def]) >>
  gen_tac >> strip_tac >> rpt (irule rb_bind_return_for >> BETA_TAC) >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_unwrap_value_for] >> gen_tac >> strip_tac >>
  rpt (irule rb_bind_return_for >> BETA_TAC) >>
  rename1 `((rb_operand_ok_for source_checks) o FST) result` >>
  Cases_on `FST (SND result)` >> gvs[rb_emit_void_for, rb_compile_assign_value_for]
QED
Resume compile_stmts_label_checks[augassign]:
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks) o FST` >> BETA_TAC >>
  reverse conj_tac
  >- (irule rb_compile_get_target_ptr_for >> gvs[rb_expr_contract_for_def]) >>
  gen_tac >> strip_tac >> rpt (irule rb_bind_return_for >> BETA_TAC) >>
  gvs[] >> Cases_on `FST (SND x)` >> simp[rb_emit_void_for] >>
  rename1 `FST (SND x) = SOME loc` >> Cases_on `loc` >>
  (rpt (irule rb_bind_return_for >> BETA_TAC) >>
   irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
   irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
   reverse conj_tac >- (irule rb_lower_value_for >> gvs[rb_expr_contract_for_def]) >>
   gen_tac >> strip_tac >>
   irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
   reverse conj_tac >- simp[rb_compile_binop_for] >>
   simp[rb_emit_void_for])
QED

Resume compile_stmts_label_checks[assert_bare]:
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- (irule rb_lower_value_for >> gvs[rb_expr_contract_for_def]) >>
  gen_tac >> strip_tac >>
  ntac 2 (irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_new_block_for, rb_step_return_for]
QED
Resume compile_stmts_label_checks[assert_unreachable]:
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- (irule rb_lower_value_for >> gvs[rb_expr_contract_for_def]) >>
  gen_tac >> strip_tac >>
  ntac 2 (irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_new_block_for, rb_step_return_for]
QED
Resume compile_stmts_label_checks[assert_reason]:
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- (irule rb_lower_value_for >> gvs[rb_expr_contract_for_def]) >>
  gen_tac >> strip_tac >>
  ntac 2 (irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  rpt (irule rb_bind_return_for >> BETA_TAC) >>
  irule rb_step_bind_for >> qexists_tac `(rb_value_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_reason_message_for] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_compile_revert_with_reason_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_new_block_for, rb_step_return_for]
QED
Resume compile_stmts_label_checks[assert_custom]:
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- (irule rb_lower_value_for >> gvs[rb_expr_contract_for_def]) >>
  gen_tac >> strip_tac >>
  ntac 2 (irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_compile_revert_with_custom_error_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_new_block_for, rb_step_return_for]
QED
Resume compile_stmts_label_checks[raise_reason]:
  irule rb_step_bind_for >> qexists_tac `(rb_value_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_reason_message_for] >>
  simp[rb_compile_revert_with_reason_for]
QED
Resume compile_stmts_label_checks[raise_custom]:
  simp[rb_compile_revert_with_custom_error_for]
QED

Resume compile_stmts_label_checks[tuple]:
  irule rb_step_bind_for >> qexists_tac `(rb_value_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- gvs[rb_expr_contract_for_def] >> gen_tac >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_unwrap_value_for] >> simp[rb_compile_tuple_unpack_for]
QED
Resume compile_stmts_label_checks[append]:
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks) o FST` >> BETA_TAC >>
  reverse conj_tac
  >- (irule rb_compile_get_target_ptr_for >> gvs[rb_expr_contract_for_def]) >>
  gen_tac >> strip_tac >> simp[] >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- (irule rb_lower_value_for >> gvs[rb_expr_contract_for_def]) >>
  gen_tac >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac
  >- (IF_CASES_TAC >> simp[rb_step_return_for] >>
      irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >> BETA_TAC >>
      reverse conj_tac >- simp[rb_compile_alloc_buffer_for] >>
      gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_compile_store_memory_for, rb_step_return_for]) >>
  gen_tac >> strip_tac >> irule rb_bind_return_for >> BETA_TAC >>
  irule rb_compile_dynarray_append_for >> gvs[rb_env_ok_for_def]
QED
Resume compile_stmts_label_checks[break]:
  gvs[rb_loop_ok_for_def, rb_emit_inst_for, rb_operand_ok_for_def]
QED
Resume compile_stmts_label_checks[continue]:
  gvs[rb_loop_ok_for_def, rb_emit_inst_for, rb_operand_ok_for_def]
QED
Resume compile_stmts_label_checks[catchall1]:
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_inst_for, rb_step_return_for]
QED
Resume compile_stmts_label_checks[catchall2]:
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_inst_for, rb_step_return_for]
QED
Resume compile_stmts_label_checks[stmts]:
  irule rb_step_bind_for >> qexists_tac `K T` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_step_for_def, comp_get_def] >>
  gen_tac >> strip_tac >> IF_CASES_TAC >- simp[rb_step_return_for] >>
  irule rb_step_bind_for >> qexists_tac `(rb_env_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_declare_stmt_local_for] >>
  gen_tac >> strip_tac >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Resume compile_stmts_label_checks[if]:
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- (irule rb_lower_value_for >> gvs[rb_expr_contract_for_def]) >>
  gen_tac >> strip_tac >>
  ntac 3 (irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[] >>
  irule rb_step_bind_for >> qexists_tac `K T` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_step_for_def, comp_get_def] >> gen_tac >> strip_tac >>
  irule rb_bind_return_for >> BETA_TAC >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_jmp_if_not_terminated_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[] >>
  irule rb_step_bind_for >> qexists_tac `K T` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_step_for_def, comp_get_def] >> gen_tac >> strip_tac >>
  irule rb_bind_return_for >> BETA_TAC >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_jmp_if_not_terminated_for] >>
  IF_CASES_TAC >> simp[rb_step_return_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_new_block_for, rb_step_return_for]
QED
Resume compile_stmts_label_checks[return_none]:
  `(rb_step_for source_checks) (K T)
    (case env.ce_ctor_exit_label of
       SOME l => emit_inst JMP [Label l] []
     | NONE => (\(nr,k,tr,vw). comp_ignore_bind
         (if nr then compile_nonreentrant_unlock k tr vw else comp_return ())
         (emit_inst STOP [] [])) env.ce_nonreentrant)` by
    (Cases_on `env.ce_ctor_exit_label` >> simp[]
     >- (pairarg_tac >> simp[] >>
         irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_inst_for] >>
         IF_CASES_TAC >> simp[rb_compile_nonreentrant_unlock_for, rb_step_return_for]) >>
     gvs[rb_env_ok_for_def, rb_operand_ok_for_def, rb_emit_inst_for]) >>
  Cases_on `env.ce_return_pc` >> simp[] >> rename1 `_ = SOME loc` >>
  `(rb_location_ok_for source_checks) loc` by gvs[rb_env_ok_for_def] >>
  Cases_on `loc` >> gvs[rb_location_ok_for_def] >>
  (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_compile_return_unlock_for])
  >- (irule rb_bind_emit_op_for >> simp[rb_emit_inst_for]) >> simp[rb_emit_inst_for]
QED

Resume compile_stmts_label_checks[log]:
  Cases_on `env.ce_event_info (nsid_to_string event_id)` >> simp[rb_emit_inst_for] >>
  rename1 `_ = SOME info` >> PairCases_on `info` >> simp[] >>
  irule rb_step_bind_for >> qexists_tac `EVERY (rb_value_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- (irule rb_compile_ext_call_args_for >>
    gvs[rb_expr_contract_for_def]) >> qx_gen_tac `saved` >> strip_tac >>
  rpt (irule rb_bind_return_for >> BETA_TAC) >>
  `!tys flags. EVERY (rb_value_ok_for source_checks o FST)
       (FST (split_log_ops (ZIP (saved,tys)) flags)) /\
     EVERY (rb_value_ok_for source_checks o FST)
       (SND (split_log_ops (ZIP (saved,tys)) flags))` by
    (rpt gen_tac >> irule every_split_log_ops >> simp[rb_every_zip_fst]) >>
  irule rb_step_bind_for >> qexists_tac `EVERY (rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_log_saved_topics_for] >> gen_tac >> strip_tac >>
  rpt (irule rb_bind_return_for >> BETA_TAC) >>
  IF_CASES_TAC >- simp[rb_emit_inst_for, rich_listTheory.EVERY_REVERSE] >>
  simp[] >> irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer_for] >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  irule rb_bind_return_for >> BETA_TAC >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- (irule rb_compile_abi_encode_values_to_buf_for >>
    simp[rb_abi_encode_for]) >>
  simp[rb_emit_inst_for, rich_listTheory.EVERY_REVERSE]
QED

Resume compile_stmts_label_checks[return_some]:
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- (irule rb_lower_value_for >> gvs[rb_expr_contract_for_def]) >>
  gen_tac >> strip_tac >>
  Cases_on `env.ce_return_pc` >> simp[]
  >- suspend "return_external" >>
  rename1 `_ = SOME loc` >>
  `(rb_location_ok_for source_checks) loc` by gvs[rb_env_ok_for_def] >>
  Cases_on `loc` >> gvs[rb_location_ok_for_def]
  >- (irule rb_bind_emit_op_for >> simp[rb_compile_internal_return_from_env_for])
  >- suspend "return_external"
  >- suspend "return_external"
  >- suspend "return_external" >>
  simp[rb_compile_internal_return_from_env_for]
QED
Resume compile_stmts_label_checks[return_external]:
  markerLib.RESUME_TAC >> (simp[] >>
   irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
   reverse conj_tac
   >- (IF_CASES_TAC >> simp[rb_step_return_for] >>
       irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >> BETA_TAC >>
       reverse conj_tac >- simp[rb_compile_alloc_buffer_for] >>
       gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
       irule rb_bind_return_for >> BETA_TAC >>
       irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[cj 1 rb_typed_memory_for, rb_step_return_for]) >>
   gen_tac >> strip_tac >> IF_CASES_TAC
   >- (simp[] >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac
       >- (IF_CASES_TAC >> simp[rb_compile_nonreentrant_unlock_for, rb_step_return_for]) >>
       irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >> BETA_TAC >>
       reverse conj_tac >- simp[rb_compile_alloc_buffer_for] >>
       gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
       irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[cj 1 rb_typed_memory_for, rb_compile_external_return_for]) >>
   simp[rb_compile_external_return_for])
QED

Resume compile_stmts_label_checks[range]:
  ntac 2 (irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
    (reverse conj_tac >- (irule rb_lower_value_for >> gvs[rb_expr_contract_for_def])) >>
    gen_tac >> strip_tac) >>
  irule rb_step_bind_for >> qexists_tac `(rb_env_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_declare_local_for] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_local_alloca_for] >>
  ntac 5 (irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule rb_bind_fresh_var_for >> BETA_TAC >> gen_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac
  >- (Cases_on `start_e` >> simp[rb_emit_op_for, rb_step_return_for] >>
      Cases_on `end_e` >> simp[rb_emit_op_for, rb_step_return_for] >>
      CASE_TAC >> simp[rb_emit_op_for, rb_step_return_for] >>
      CASE_TAC >> simp[rb_emit_op_for, rb_step_return_for]) >>
  gen_tac >> strip_tac >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac
  >- (Cases_on `start_e` >> simp[rb_compile_range_bound_checks_for, rb_step_return_for] >>
      Cases_on `end_e` >> simp[rb_compile_range_bound_checks_for, rb_step_return_for] >>
      CASE_TAC >> simp[rb_compile_range_bound_checks_for, rb_step_return_for] >>
      CASE_TAC >> simp[rb_compile_range_bound_checks_for, rb_step_return_for]) >>
  suspend "range_tail"
QED

Resume compile_stmts_label_checks[range_tail]:
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac
  >- (rename1 `(rb_env_ok_for source_checks) bce` >>
      Cases_on `FLOOKUP bce.ce_vars id` >> simp[rb_emit_void_for] >>
      rename1 `_ = SOME loc` >>
      `(rb_location_ok_for source_checks) loc` by metis_tac[rb_env_ok_for_def] >>
      Cases_on `loc` >> gvs[rb_location_ok_for_def, rb_emit_void_for]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac
  >- (first_x_assum irule >> simp[rb_loop_ok_for_def, rb_operand_ok_for_def]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_jmp_if_not_terminated_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  ntac 2 (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> (conj_tac >- simp[rb_emit_inst_for])) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_new_block_for, rb_step_return_for]
QED

Resume compile_stmts_label_checks[iter]:
  irule rb_step_bind_for >> qexists_tac `(rb_value_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- gvs[rb_expr_contract_for_def] >> gen_tac >> strip_tac >>
  rpt (irule rb_bind_return_for >> BETA_TAC) >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac
  >- (IF_CASES_TAC >> simp[rb_step_return_for] >>
      irule rb_compile_ptr_load_for >>
      gvs[rb_env_ok_for_def, AllCaseEqs()] >>
      irule rb_value_operand_for >> first_assum MATCH_ACCEPT_TAC) >>
  gen_tac >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `(rb_env_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_declare_local_for] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_local_alloca_for] >>
  ntac 5 (irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule rb_bind_fresh_var_for >> BETA_TAC >> gen_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac
  >- (IF_CASES_TAC >> simp[rb_step_return_for] >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> simp[rb_emit_void_for]) >>
  suspend "iter_tail"
QED
Resume compile_stmts_label_checks[iter_tail]:
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule rb_bind_return_for >> BETA_TAC >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- (IF_CASES_TAC >> simp[rb_emit_op_for, rb_step_return_for]) >>
  gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >>
  reverse conj_tac >- (simp[] >> irule rb_value_operand_for >> first_assum MATCH_ACCEPT_TAC) >>
  gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac
  >- (rename1 `(rb_env_ok_for source_checks) bce` >>
      Cases_on `FLOOKUP bce.ce_vars id` >> simp[rb_emit_void_for] >>
      rename1 `_ = SOME loc` >>
      `(rb_location_ok_for source_checks) loc` by metis_tac[rb_env_ok_for_def] >>
      Cases_on `loc` >> gvs[rb_location_ok_for_def, rb_emit_void_for,
        rb_compile_iter_elem_copy_for]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac
  >- (first_x_assum irule >> simp[rb_loop_ok_for_def, rb_operand_ok_for_def]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_jmp_if_not_terminated_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  ntac 2 (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> (conj_tac >- simp[rb_emit_inst_for])) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_new_block_for, rb_step_return_for]
QED

Finalise compile_stmts_label_checks

(* The runtime-begin exclusions use the original checks. *)

Theorem rb_compile_mcopy_guard:
  rb_step (K T) action ==> rb_step (K T) (compile_mcopy_guard ce action)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_mcopy_guard_for))
QED

Theorem rb_compile_revert_with_reason:
  rb_env_ok ce /\ rb_value_ok msg ==>
  rb_step (K T) (compile_revert_with_reason ce msg ty n)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_env_ok_legacy,
     rb_step_legacy,
     rb_value_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_revert_with_reason_for))
QED

Theorem rb_compile_revert_with_custom_error:
  rb_expr_contract /\ rb_env_ok ce ==>
  rb_step (K T) (compile_revert_with_custom_error ce err)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_env_ok_legacy,
     rb_expr_contract_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_revert_with_custom_error_for))
QED

Theorem rb_compile_reason_message:
  !ce e. rb_expr_contract /\ rb_env_ok ce ==>
  rb_step rb_value_ok (compile_reason_message ce e)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_env_ok_legacy,
     rb_expr_contract_legacy,
     rb_step_legacy,
     rb_value_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_reason_message_for))
QED

Theorem rb_compile_range_bound_checks:
  rb_operand_ok start /\ rb_operand_ok stop /\ rb_operand_ok rounds ==>
  rb_step (K T) (compile_range_bound_checks start stop rounds bound signed)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_range_bound_checks_for))
QED

Theorem rb_compile_iter_elem_copy:
  rb_env_ok ce /\ rb_operand_ok elem /\ rb_operand_ok item ==>
  rb_step (K T) (compile_iter_elem_copy ce elem item n loc slots tty ety)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_env_ok_legacy,
     rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_iter_elem_copy_for))
QED

Theorem rb_compile_assign_value:
  rb_env_ok ce /\ rb_operand_ok dst /\ rb_operand_ok src ==>
  rb_step (K T) (compile_assign_value ce dst loc src prim sloc dty sty n)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_env_ok_legacy,
     rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_assign_value_for))
QED

Theorem rb_compile_tuple_load_all:
  !tys offset. rb_operand_ok src ==>
  rb_step (EVERY rb_operand_ok) (compile_tuple_load_all ce src tys offset)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_tuple_load_all_for))
QED

Theorem rb_compile_store_at_loc:
  rb_operand_ok dst /\ rb_operand_ok v /\
  (case imm of NONE => T | SOME op => rb_operand_ok op) ==>
  rb_step (K T) (compile_store_at_loc imm dst v loc)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_store_at_loc_for))
QED

Theorem rb_compile_tuple_store_all:
  !ce tys targets vals. rb_expr_contract /\ rb_env_ok ce /\ EVERY rb_operand_ok vals ==>
  rb_step (K T) (compile_tuple_store_all ce tys targets vals)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_env_ok_legacy,
     rb_expr_contract_legacy,
     rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_tuple_store_all_for))
QED

Theorem rb_compile_tuple_unpack:
  rb_expr_contract /\ rb_env_ok ce /\ rb_operand_ok src ==>
  rb_step (K T) (compile_tuple_unpack ce ty stage targets src)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_env_ok_legacy,
     rb_expr_contract_legacy,
     rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_tuple_unpack_for))
QED

Theorem rb_emit_jmp_if_not_terminated:
  rb_operand_ok (Label l) ==> rb_step (K T) (emit_jmp_if_not_terminated l)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_emit_jmp_if_not_terminated_for))
QED

Theorem compile_stmts_no_runtime_begin:
  rb_expr_contract ==> rb_stmt_contract
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_expr_contract_legacy,
     rb_stmt_contract_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] compile_stmts_label_checks))
QED
