(* Statement boundaries consume the expression certificate, not its proof. *)
Theory runtimeLabelStmt
Ancestors
  runtimeLabelExprCallbacks runtimeLabelExprPrimitives runtimeLabelBuiltinArithmetic
  runtimeLabelStmtIO runtimeLabelPrimitives runtimeLabelInvariant runtimeLabelValues runtimeLabelBuiltins runtimeLabelABI
  stmtLowering exprLowering compileEnv context emitHelper venomInst list

Theorem rb_compile_mcopy_guard:
  rb_step (K T) action ==> rb_step (K T) (compile_mcopy_guard ce action)
Proof
  simp[compile_mcopy_guard_def] >> strip_tac >>
  Cases_on `ce.ce_target CapMcopy` >> simp[rb_emit_inst]
QED

Theorem rb_compile_revert_with_reason:
  rb_env_ok ce /\ rb_value_ok msg ==>
  rb_step (K T) (compile_revert_with_reason ce msg ty n)
Proof
  strip_tac >> pure_rewrite_tac[compile_revert_with_reason_def, LET_THM] >>
  BETA_TAC >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_unwrap_value] >> gen_tac >> strip_tac >>
  rpt (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  rpt (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  rpt (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  rpt (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  simp[rb_emit_inst]
QED

Theorem rb_compile_custom_error_store_args:
  !es tys dst off. rb_expr_contract /\ rb_env_ok ce /\ rb_operand_ok dst ==>
  rb_step (K T) (compile_custom_error_store_args ce es tys dst off)
Proof
  Induct >> Cases_on `tys` >>
  simp[compile_custom_error_store_args_def, rb_step_return] >> rpt strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- gvs[rb_expr_contract_def] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (IF_CASES_TAC >> simp[rb_step_return, rb_emit_op]) >>
  gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_unwrap_value] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_compile_store_memory] >>
  first_x_assum irule >> simp[]
QED

Theorem rb_compile_revert_with_custom_error:
  rb_expr_contract /\ rb_env_ok ce ==>
  rb_step (K T) (compile_revert_with_custom_error ce err)
Proof
  strip_tac >> Cases_on `err` >>
  rename1 `CustomError id positional kwargs` >>
  pure_rewrite_tac[compile_revert_with_custom_error_def, LET_THM] >> BETA_TAC >>
  Cases_on `ce.ce_error_info (nsid_to_string id)` >> simp[rb_emit_inst] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_compile_custom_error_store_args] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  IF_CASES_TAC
  >- (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      simp[rb_emit_inst]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_abi_encode] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  simp[rb_emit_inst]
QED

Theorem rb_compile_reason_message:
  !ce e. rb_expr_contract /\ rb_env_ok ce ==>
  rb_step rb_value_ok (compile_reason_message ce e)
Proof
  recInduct compile_reason_message_ind >> rpt strip_tac >>
  simp[compile_reason_message_def]
  >- (irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
      reverse conj_tac >- simp[rb_compile_bytelike_literal] >>
      simp[rb_step_return, rb_value_ok_def, rb_base_ptr]) >>
  gvs[rb_expr_contract_def]
QED

Theorem rb_compile_range_bound_checks:
  rb_operand_ok start /\ rb_operand_ok stop /\ rb_operand_ok rounds ==>
  rb_step (K T) (compile_range_bound_checks start stop rounds bound signed)
Proof
  strip_tac >> pure_rewrite_tac[compile_range_bound_checks_def] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (Cases_on `signed` >> simp[rb_emit_op]) >>
  gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  simp[rb_emit_void]
QED

Theorem rb_compile_iter_elem_copy:
  rb_env_ok ce /\ rb_operand_ok elem /\ rb_operand_ok item ==>
  rb_step (K T) (compile_iter_elem_copy ce elem item n loc slots tty ety)
Proof
  strip_tac >> pure_rewrite_tac[compile_iter_elem_copy_def] >>
  Cases_on `slots` >> simp[]
  >- (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_compile_slot_to_memory, rb_step_return]) >>
  Cases_on `loc <> LocMemory` >> simp[]
  >- (Cases_on `n <= 32` >> simp[]
      >- (irule rb_bind_ptr_load >> BETA_TAC >>
          gvs[rb_env_ok_def, rb_emit_void]) >>
      Cases_on `loc` >> simp[rb_emit_void, rb_compile_copy_memory,
        rb_compile_imm_copy_to_memory] >>
      gvs[rb_env_ok_def, rb_compile_imm_copy_to_memory]) >>
  Cases_on `is_word_type tty` >> simp[]
  >- (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      simp[rb_emit_void]) >>
  simp[rb_compile_store_memory]
QED

Theorem rb_compile_assign_value:
  rb_env_ok ce /\ rb_operand_ok dst /\ rb_operand_ok src ==>
  rb_step (K T) (compile_assign_value ce dst loc src prim sloc dty sty n)
Proof
  strip_tac >> pure_rewrite_tac[compile_assign_value_def] >>
  Cases_on `loc` >> simp[]
  >- (Cases_on `prim` >> simp[rb_emit_void] >>
      Cases_on `sloc = SOME LocMemory` >> simp[rb_compile_store_memory] >>
      irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
      reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
      gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
      irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
      reverse conj_tac >- simp[rb_step_return] >> gen_tac >> strip_tac >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_compile_copy_memory, rb_compile_store_memory])
  >~ [`emit_inst INVALID [] []`]
  >- (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_inst, rb_step_return]) >>
  (irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac
  >- (IF_CASES_TAC >> simp[rb_step_return] >>
      irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
      reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
      gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[cj 1 rb_typed_memory, rb_step_return]) >>
  gen_tac >> strip_tac >>
  Cases_on `prim` >> simp[rb_emit_void, cj 1 rb_slots] >>
  gvs[rb_env_ok_def, rb_compile_imm_store_word] >>
  Cases_on `is_bytestring_type dty` >> simp[rb_compile_store_immutable_bytestring] >>
  Cases_on `n <= 32` >> simp[rb_compile_imm_store_words] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_compile_imm_store_word])
QED

Theorem rb_compile_tuple_load_all:
  !tys offset. rb_operand_ok src ==>
  rb_step (EVERY rb_operand_ok) (compile_tuple_load_all ce src tys offset)
Proof
  Induct >> simp[compile_tuple_load_all_def, rb_step_return] >> rpt strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_load_memory] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `EVERY rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >> simp[rb_step_return]
QED

Theorem rb_compile_store_at_loc:
  rb_operand_ok dst /\ rb_operand_ok v /\
  (case imm of NONE => T | SOME op => rb_operand_ok op) ==>
  rb_step (K T) (compile_store_at_loc imm dst v loc)
Proof
  Cases_on `loc` >> simp[compile_store_at_loc_def, rb_emit_void] >>
  rename1 `SOME l` >> Cases_on `l` >>
  simp[compile_store_at_loc_def, rb_emit_void, rb_compile_imm_store_word]
QED

Theorem rb_compile_tuple_store_all:
  !ce tys targets vals. rb_expr_contract /\ rb_env_ok ce /\ EVERY rb_operand_ok vals ==>
  rb_step (K T) (compile_tuple_store_all ce tys targets vals)
Proof
  recInduct compile_tuple_store_all_ind >> rpt strip_tac >>
  simp[compile_tuple_store_all_def, rb_step_return]
  >- (irule rb_step_bind >> qexists_tac `rb_operand_ok o FST` >> BETA_TAC >>
      reverse conj_tac
      >- (irule rb_compile_get_target_ptr >> gvs[rb_expr_contract_def]) >>
      gen_tac >> strip_tac >>
      rpt (irule rb_bind_return >> BETA_TAC) >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> reverse conj_tac >- gvs[] >>
      Cases_on `is_word_type src_ty` >> simp[]
      >- (Cases_on `is_word_type (case SND (SND x) of SOME (ValPT t) => t | _ => src_ty)` >>
          simp[rb_emit_void] >> irule rb_compile_store_at_loc >>
          gvs[rb_env_ok_def]) >>
      irule rb_compile_assign_value >> gvs[]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> gvs[rb_emit_void]
QED

Theorem rb_compile_tuple_unpack:
  rb_expr_contract /\ rb_env_ok ce /\ rb_operand_ok src ==>
  rb_step (K T) (compile_tuple_unpack ce ty stage targets src)
Proof
  strip_tac >> pure_rewrite_tac[compile_tuple_unpack_def, LET_THM] >>
  BETA_TAC >> IF_CASES_TAC >- simp[rb_emit_inst] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac
  >- (IF_CASES_TAC >> simp[rb_step_return] >>
      irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
      reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
      gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
      irule rb_bind_return >> BETA_TAC >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return]) >>
  gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `EVERY rb_operand_ok` >> BETA_TAC >>
  simp[rb_compile_tuple_load_all, rb_compile_tuple_store_all]
QED

Theorem rb_emit_jmp_if_not_terminated:
  rb_operand_ok (Label l) ==> rb_step (K T) (emit_jmp_if_not_terminated l)
Proof
  strip_tac >> rewrite_tac[emit_jmp_if_not_terminated_def] >>
  irule rb_step_bind >> qexists_tac `K T` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_step_def, comp_get_def] >>
  gen_tac >> strip_tac >> IF_CASES_TAC >> simp[rb_step_return, rb_emit_inst]
QED

Theorem compile_stmts_no_runtime_begin:
  rb_expr_contract ==> rb_stmt_contract
Proof
  strip_tac >> rewrite_tac[rb_stmt_contract_def] >>
  ho_match_mp_tac compile_stmt_ind >> rpt strip_tac >>
  simp[Once compile_stmt_def, rb_step_return, rb_emit_inst,
       rb_loop_ok_def]
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
Resume compile_stmts_no_runtime_begin[expr]:
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (irule rb_step_weaken >> qexists_tac `rb_value_ok` >>
      gvs[rb_expr_contract_def]) >> simp[rb_step_return]
QED
Resume compile_stmts_no_runtime_begin[annassign]:
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_local_alloca] >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- gvs[rb_expr_contract_def] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac
  >- (IF_CASES_TAC >> simp[rb_step_return, rb_unwrap_value]) >>
  gen_tac >> strip_tac >> irule rb_bind_return >> BETA_TAC >>
  Cases_on `FLOOKUP env.ce_vars id` >> simp[rb_emit_void] >>
  rename1 `FLOOKUP _ _ = SOME loc` >>
  `rb_location_ok loc` by metis_tac[rb_env_ok_def] >>
  Cases_on `loc` >> gvs[rb_location_ok_def, rb_emit_void] >>
  IF_CASES_TAC >> simp[rb_emit_void, rb_compile_assign_value]
QED


Resume compile_stmts_no_runtime_begin[assign]:
  IF_CASES_TAC
  >- (irule rb_step_bind >> qexists_tac `rb_operand_ok o FST` >> BETA_TAC >>
      reverse conj_tac
      >- (irule rb_compile_get_target_ptr >> gvs[rb_expr_contract_def]) >>
      gen_tac >> strip_tac >> irule rb_compile_store_at_loc >>
      gvs[rb_env_ok_def]) >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- gvs[rb_expr_contract_def] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac
  >- (IF_CASES_TAC >> simp[rb_compile_snapshot_vv, rb_vv_with_type, rb_step_return]) >>
  gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok o FST` >> BETA_TAC >>
  reverse conj_tac
  >- (irule rb_compile_get_target_ptr >> gvs[rb_expr_contract_def]) >>
  gen_tac >> strip_tac >> rpt (irule rb_bind_return >> BETA_TAC) >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_unwrap_value] >> gen_tac >> strip_tac >>
  rpt (irule rb_bind_return >> BETA_TAC) >>
  rename1 `(rb_operand_ok o FST) result` >>
  Cases_on `FST (SND result)` >> gvs[rb_emit_void, rb_compile_assign_value]
QED
Resume compile_stmts_no_runtime_begin[augassign]:
  irule rb_step_bind >> qexists_tac `rb_operand_ok o FST` >> BETA_TAC >>
  reverse conj_tac
  >- (irule rb_compile_get_target_ptr >> gvs[rb_expr_contract_def]) >>
  gen_tac >> strip_tac >> rpt (irule rb_bind_return >> BETA_TAC) >>
  gvs[] >> Cases_on `FST (SND x)` >> simp[rb_emit_void] >>
  rpt (irule rb_bind_return >> BETA_TAC) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (irule rb_lower_value >> gvs[rb_expr_contract_def]) >>
  gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_binop] >>
  simp[rb_emit_void]
QED

Resume compile_stmts_no_runtime_begin[assert_bare]:
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (irule rb_lower_value >> gvs[rb_expr_contract_def]) >>
  gen_tac >> strip_tac >>
  ntac 2 (irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_new_block, rb_step_return]
QED
Resume compile_stmts_no_runtime_begin[assert_unreachable]:
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (irule rb_lower_value >> gvs[rb_expr_contract_def]) >>
  gen_tac >> strip_tac >>
  ntac 2 (irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_new_block, rb_step_return]
QED
Resume compile_stmts_no_runtime_begin[assert_reason]:
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (irule rb_lower_value >> gvs[rb_expr_contract_def]) >>
  gen_tac >> strip_tac >>
  ntac 2 (irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  rpt (irule rb_bind_return >> BETA_TAC) >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_reason_message] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_compile_revert_with_reason] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_new_block, rb_step_return]
QED
Resume compile_stmts_no_runtime_begin[assert_custom]:
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (irule rb_lower_value >> gvs[rb_expr_contract_def]) >>
  gen_tac >> strip_tac >>
  ntac 2 (irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_compile_revert_with_custom_error] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_new_block, rb_step_return]
QED
Resume compile_stmts_no_runtime_begin[raise_reason]:
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_reason_message] >>
  simp[rb_compile_revert_with_reason]
QED
Resume compile_stmts_no_runtime_begin[raise_custom]:
  simp[rb_compile_revert_with_custom_error]
QED

Resume compile_stmts_no_runtime_begin[tuple]:
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- gvs[rb_expr_contract_def] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_unwrap_value] >> simp[rb_compile_tuple_unpack]
QED
Resume compile_stmts_no_runtime_begin[append]:
  irule rb_step_bind >> qexists_tac `rb_operand_ok o FST` >> BETA_TAC >>
  reverse conj_tac
  >- (irule rb_compile_get_target_ptr >> gvs[rb_expr_contract_def]) >>
  gen_tac >> strip_tac >> simp[] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (irule rb_lower_value >> gvs[rb_expr_contract_def]) >>
  gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac
  >- (IF_CASES_TAC >> simp[rb_step_return] >>
      irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
      reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
      gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_compile_store_memory, rb_step_return]) >>
  gen_tac >> strip_tac >> irule rb_bind_return >> BETA_TAC >>
  irule rb_compile_dynarray_append >> gvs[rb_env_ok_def]
QED
Resume compile_stmts_no_runtime_begin[break]:
  gvs[rb_loop_ok_def, rb_emit_inst, rb_operand_ok_def]
QED
Resume compile_stmts_no_runtime_begin[continue]:
  gvs[rb_loop_ok_def, rb_emit_inst, rb_operand_ok_def]
QED
Resume compile_stmts_no_runtime_begin[catchall1]:
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_inst, rb_step_return]
QED
Resume compile_stmts_no_runtime_begin[catchall2]:
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_inst, rb_step_return]
QED
Resume compile_stmts_no_runtime_begin[stmts]:
  irule rb_step_bind >> qexists_tac `K T` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_step_def, comp_get_def] >>
  gen_tac >> strip_tac >> IF_CASES_TAC >- simp[rb_step_return] >>
  irule rb_step_bind >> qexists_tac `rb_env_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_declare_stmt_local] >>
  gen_tac >> strip_tac >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Resume compile_stmts_no_runtime_begin[if]:
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (irule rb_lower_value >> gvs[rb_expr_contract_def]) >>
  gen_tac >> strip_tac >>
  ntac 3 (irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[] >>
  irule rb_step_bind >> qexists_tac `K T` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_step_def, comp_get_def] >> gen_tac >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_jmp_if_not_terminated] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[] >>
  irule rb_step_bind >> qexists_tac `K T` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_step_def, comp_get_def] >> gen_tac >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_jmp_if_not_terminated] >>
  IF_CASES_TAC >> simp[rb_step_return] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_new_block, rb_step_return]
QED
Resume compile_stmts_no_runtime_begin[return_none]:
  `rb_step (K T)
    (case env.ce_ctor_exit_label of
       SOME l => emit_inst JMP [Label l] []
     | NONE => (\(nr,k,tr,vw). comp_ignore_bind
         (if nr then compile_nonreentrant_unlock k tr vw else comp_return ())
         (emit_inst STOP [] [])) env.ce_nonreentrant)` by
    (Cases_on `env.ce_ctor_exit_label` >> simp[]
     >- (pairarg_tac >> simp[] >>
         irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_inst] >>
         IF_CASES_TAC >> simp[rb_compile_nonreentrant_unlock, rb_step_return]) >>
     gvs[rb_env_ok_def, rb_operand_ok_def, rb_emit_inst]) >>
  Cases_on `env.ce_return_pc` >> simp[] >> rename1 `_ = SOME loc` >>
  `rb_location_ok loc` by gvs[rb_env_ok_def] >>
  Cases_on `loc` >> gvs[rb_location_ok_def] >>
  (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_compile_return_unlock])
  >- (irule rb_bind_emit_op >> simp[rb_emit_inst]) >> simp[rb_emit_inst]
QED

Resume compile_stmts_no_runtime_begin[log]:
  Cases_on `env.ce_event_info (nsid_to_string event_id)` >> simp[rb_emit_inst] >>
  rename1 `_ = SOME info` >> PairCases_on `info` >> simp[] >>
  irule rb_step_bind >> qexists_tac `EVERY (rb_operand_ok o FST)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_log_eval_all] >> gen_tac >> strip_tac >>
  rpt (irule rb_bind_return >> BETA_TAC) >>
  drule rb_split_log_ops >> strip_tac >>
  irule rb_step_bind >> qexists_tac `EVERY rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_log_topic_ops] >> gen_tac >> strip_tac >>
  rpt (irule rb_bind_return >> BETA_TAC) >>
  IF_CASES_TAC >- simp[rb_emit_inst, rich_listTheory.EVERY_REVERSE] >>
  simp[] >> irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_compile_log_store_data] >>
  rpt (irule rb_bind_return >> BETA_TAC) >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[cj 2 rb_abi_encode] >>
  simp[rb_emit_inst, rich_listTheory.EVERY_REVERSE]
QED

Resume compile_stmts_no_runtime_begin[return_some]:
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (irule rb_lower_value >> gvs[rb_expr_contract_def]) >>
  gen_tac >> strip_tac >>
  Cases_on `env.ce_return_pc` >> simp[]
  >- suspend "return_external" >>
  rename1 `_ = SOME loc` >>
  `rb_location_ok loc` by gvs[rb_env_ok_def] >>
  Cases_on `loc` >> gvs[rb_location_ok_def]
  >- (irule rb_bind_emit_op >> simp[rb_compile_internal_return_from_env])
  >- suspend "return_external"
  >- suspend "return_external"
  >- suspend "return_external" >>
  simp[rb_compile_internal_return_from_env]
QED
Resume compile_stmts_no_runtime_begin[return_external]:
  markerLib.RESUME_TAC >> (simp[] >>
   irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
   reverse conj_tac
   >- (IF_CASES_TAC >> simp[rb_step_return] >>
       irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
       reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
       gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
       irule rb_bind_return >> BETA_TAC >>
       irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[cj 1 rb_typed_memory, rb_step_return]) >>
   gen_tac >> strip_tac >> IF_CASES_TAC
   >- (simp[] >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
       >- (IF_CASES_TAC >> simp[rb_compile_nonreentrant_unlock, rb_step_return]) >>
       irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
       reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
       gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
       irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[cj 1 rb_typed_memory, rb_compile_external_return]) >>
   simp[rb_compile_external_return])
QED

Resume compile_stmts_no_runtime_begin[range]:
  ntac 2 (irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
    (reverse conj_tac >- (irule rb_lower_value >> gvs[rb_expr_contract_def])) >>
    gen_tac >> strip_tac) >>
  irule rb_step_bind >> qexists_tac `rb_env_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_declare_local] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_local_alloca] >>
  ntac 5 (irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule rb_bind_fresh_var >> BETA_TAC >> gen_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac
  >- (Cases_on `start_e` >> simp[rb_emit_op, rb_step_return] >>
      Cases_on `end_e` >> simp[rb_emit_op, rb_step_return] >>
      CASE_TAC >> simp[rb_emit_op, rb_step_return] >>
      CASE_TAC >> simp[rb_emit_op, rb_step_return]) >>
  gen_tac >> strip_tac >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (Cases_on `start_e` >> simp[rb_compile_range_bound_checks, rb_step_return] >>
      Cases_on `end_e` >> simp[rb_compile_range_bound_checks, rb_step_return] >>
      CASE_TAC >> simp[rb_compile_range_bound_checks, rb_step_return] >>
      CASE_TAC >> simp[rb_compile_range_bound_checks, rb_step_return]) >>
  suspend "range_tail"
QED

Resume compile_stmts_no_runtime_begin[range_tail]:
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (rename1 `rb_env_ok bce` >>
      Cases_on `FLOOKUP bce.ce_vars id` >> simp[rb_emit_void] >>
      rename1 `_ = SOME loc` >>
      `rb_location_ok loc` by metis_tac[rb_env_ok_def] >>
      Cases_on `loc` >> gvs[rb_location_ok_def, rb_emit_void]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (first_x_assum irule >> simp[rb_loop_ok_def, rb_operand_ok_def]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_jmp_if_not_terminated] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  ntac 2 (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_emit_inst])) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_new_block, rb_step_return]
QED

Resume compile_stmts_no_runtime_begin[iter]:
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- gvs[rb_expr_contract_def] >> gen_tac >> strip_tac >>
  rpt (irule rb_bind_return >> BETA_TAC) >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac
  >- (IF_CASES_TAC >> simp[rb_step_return] >>
      irule rb_compile_ptr_load >>
      gvs[rb_env_ok_def, AllCaseEqs()] >>
      irule rb_value_operand >> first_assum MATCH_ACCEPT_TAC) >>
  gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_env_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_declare_local] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_local_alloca] >>
  ntac 5 (irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule rb_bind_fresh_var >> BETA_TAC >> gen_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (IF_CASES_TAC >> simp[rb_step_return] >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> simp[rb_emit_void]) >>
  suspend "iter_tail"
QED
Resume compile_stmts_no_runtime_begin[iter_tail]:
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (IF_CASES_TAC >> simp[rb_emit_op, rb_step_return]) >>
  gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >>
  reverse conj_tac >- (simp[] >> irule rb_value_operand >> first_assum MATCH_ACCEPT_TAC) >>
  gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (rename1 `rb_env_ok bce` >>
      Cases_on `FLOOKUP bce.ce_vars id` >> simp[rb_emit_void] >>
      rename1 `_ = SOME loc` >>
      `rb_location_ok loc` by metis_tac[rb_env_ok_def] >>
      Cases_on `loc` >> gvs[rb_location_ok_def, rb_emit_void,
        rb_compile_iter_elem_copy]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (first_x_assum irule >> simp[rb_loop_ok_def, rb_operand_ok_def]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_jmp_if_not_terminated] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  ntac 2 (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_emit_inst])) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_new_block, rb_step_return]
QED

Finalise compile_stmts_no_runtime_begin
