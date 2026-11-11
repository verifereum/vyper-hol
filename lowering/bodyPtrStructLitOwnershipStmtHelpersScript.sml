Theory bodyPtrStructLitOwnershipStmtHelpers
Ancestors bodyPtrStructLitOwnershipConsumers bodyPtrStructLitOwnershipLoops
  bodyPtrStructLitOwnershipLiterals bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipSteps bodyPtrStructLitCompilerOwnership
  bodyPtrStructLitOwnershipMemory bodyPtrStructLitOwnershipLocations
  bodyPtrStructLitOwnershipPrimitives bodyPtrStructLitOwnershipTyped
  bodyPtrStructLitOwnershipAbiEncode bodyPtrStructLitOwnershipInterfaces
  context compileEnv stmtLowering loweringShapeDefs loweringShapeRules
  bodyPtrStructLitOwnershipFrame bodyPtrStructLitOwnershipPop
  loweringShapeProps supportedExprTraverse exprLowering

Theorem alloc_run_compile_range_bound_checks:
  alloc_run fresh_outputs
    (compile_range_bound_checks start_op end_op rounds_op bound signed)
    (\u s. fresh_outputs s)
Proof
  simp[compile_range_bound_checks_def, comp_ignore_bind_def] >>
  Cases_on `signed` >> simp[] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh]
QED

Theorem alloc_run_compile_iter_elem_copy:
  alloc_run fresh_outputs
    (compile_iter_elem_copy ce elem item elem_size loc slot target_ty elem_ty)
    (\u s. fresh_outputs s)
Proof
  simp[compile_iter_elem_copy_def, comp_ignore_bind_def] >>
  Cases_on `slot` >> simp[]
  >- (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
      reverse conj_tac >- simp[alloc_run_compile_slot_to_memory] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  Cases_on `loc <> LocMemory` >> simp[]
  >- (Cases_on `elem_size <= 32` >> simp[]
      >- (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
          reverse conj_tac >- simp[alloc_run_compile_ptr_load] >>
          simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh]) >>
      Cases_on `loc` >> simp[alloc_run_emit_void_fresh,
        alloc_run_compile_imm_copy_to_memory, alloc_run_compile_copy_memory]) >>
  Cases_on `is_word_type target_ty` >> simp[alloc_run_compile_store_memory] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac >- simp[alloc_run_emit_op_fresh] >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh]
QED

Theorem alloc_run_compile_log_store_data:
  !ops buf offset.
    alloc_run fresh_outputs (compile_log_store_data ce ops buf offset)
      (\u s. fresh_outputs s)
Proof
  Induct >> simp[compile_log_store_data_def, comp_ignore_bind_def]
  >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  rpt gen_tac >> irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac >- simp[alloc_run_emit_op_fresh] >> gen_tac >> simp[] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac
  >- (Cases_on `is_word_type (SND h)` >>
      Cases_on `is_bytestring_type (SND h)` >>
      simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
        SRULE [SF ETA_ss] alloc_run_compile_store_bytestring]) >>
  first_x_assum (mp_tac o SRULE [SF ETA_ss]) >> simp[SF ETA_ss]
QED

Theorem alloc_run_compile_encode_log_topic:
  alloc_run fresh_outputs (compile_encode_log_topic op bs)
    (\v s. fresh_outputs s)
Proof
  Cases_on `bs` >> simp[compile_encode_log_topic_def]
  >- (rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
        reverse conj_tac >- simp[SF ETA_ss,
          SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >> gen_tac >> simp[]) >>
      simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_log_topic_ops:
  !ops. alloc_run fresh_outputs (compile_log_topic_ops ops)
    (\v s. fresh_outputs s)
Proof
  Induct >> simp[compile_log_topic_ops_def]
  >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  gen_tac >> irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac >- simp[alloc_run_compile_encode_log_topic] >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (first_x_assum (mp_tac o SRULE [SF ETA_ss]) >> simp[SF ETA_ss]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_load_tuple_elements:
  !tys base offset. alloc_run fresh_outputs
    (compile_load_tuple_elements ce base tys offset) (\v s. fresh_outputs s)
Proof
  Induct >> simp[compile_load_tuple_elements_def]
  >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  rpt gen_tac >>
  ntac 2 (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >> gen_tac >> simp[]) >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac
  >- (first_x_assum (mp_tac o SRULE [SF ETA_ss]) >> simp[SF ETA_ss]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_internal_return:
  alloc_run fresh_outputs
    (compile_internal_return ce rv rpc nret ty src tys buf)
    (\u s. fresh_outputs s)
Proof
  simp[compile_internal_return_def, comp_ignore_bind_def] >>
  Cases_on `0 < nret` >> Cases_on `rv` >> Cases_on `buf` >>
  Cases_on `tys = []` >> simp[SF ETA_ss,
    SRULE [SF ETA_ss] (Q.INST [`outs` |-> `[]`] alloc_run_emit_inst_fresh)] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac
  >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_load_tuple_elements,
      SRULE [SF ETA_ss] alloc_run_compile_store_memory] >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] (Q.INST [`outs` |-> `[]`] alloc_run_emit_inst_fresh),
    SRULE [SF ETA_ss] alloc_run_compile_load_tuple_elements,
    SRULE [SF ETA_ss] alloc_run_compile_store_memory]
QED

Theorem alloc_run_compile_internal_return_from_env:
  alloc_run fresh_outputs (compile_internal_return_from_env ce ty src op rpc)
    (\u s. fresh_outputs s)
Proof
  simp[compile_internal_return_from_env_def] >>
  Cases_on `ce.ce_return_buf` >> simp[]
  >- (rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
        reverse conj_tac >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
        gen_tac >> simp[]) >>
      simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_internal_return]) >>
  Cases_on `x` >> simp[comp_bind_assoc] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- (simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
    gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_internal_return] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_dynarray_to_storage:
  alloc_run fresh_outputs
    (compile_dynarray_to_storage src dst ew ems transient)
    (\u s. fresh_outputs s)
Proof
  simp[compile_dynarray_to_storage_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac >- simp[alloc_run_emit_op_fresh] >> gen_tac >> simp[] >>
  ntac 3 (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_fresh_label_fresh] >> gen_tac >> simp[]) >>
  irule alloc_run_bind >>
  qexists `\x s. fresh_outputs s /\ not_fresh_at s x /\ ~alloc_owned s x` >>
  reverse conj_tac >- simp[SF ETA_ss, alloc_run_fresh_var_fresh] >>
  qx_gen_tac `counter` >> simp[comp_ignore_bind_def] >>
  Cases_on `ew = 1` >> Cases_on `transient` >> simp[comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >>
    qexists `\v s. fresh_outputs s /\ not_fresh_at s counter /\
                      ~alloc_owned s counter` >>
    reverse conj_tac
    >- FIRST [simp[alloc_run_assign_reserved] >> NO_TAC,
        ho_match_mp_tac alloc_run_frame_reserved >>
        simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
          SRULE [SF ETA_ss] alloc_run_emit_empty_fresh,
          SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
          SRULE [SF ETA_ss] alloc_run_new_block_fresh,
          SRULE [SF ETA_ss] alloc_run_compile_word_copy_loop] >> NO_TAC] >>
    gen_tac >> simp[comp_ignore_bind_def]) >>
  irule alloc_run_conseq >> irule_at Any alloc_run_emit_void_fresh >> simp[]
QED

Theorem alloc_run_compile_assign_value:
  alloc_run fresh_outputs
    (compile_assign_value ce dst loc src prim src_loc dt st da bytes)
    (\u s. fresh_outputs s)
Proof
  Cases_on `loc` >> Cases_on `prim` >>
  Cases_on `src_loc = SOME LocMemory` >> Cases_on `dt = st` >>
  Cases_on `is_bytestring_type dt` >> Cases_on `is_bytestring_type st` >>
  Cases_on `da` >> simp[compile_assign_value_def, comp_ignore_bind_def,
    comp_bind_assoc] >>
  rpt (pairarg_tac >> simp[]) >>
  rpt IF_CASES_TAC >> simp[comp_ignore_bind_def, comp_bind_assoc] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac
    >- (simp[SF ETA_ss,
        SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
        SRULE [SF ETA_ss] alloc_run_compile_copy_memory,
        SRULE [SF ETA_ss] alloc_run_compile_store_memory_typed,
        SRULE [SF ETA_ss] alloc_run_compile_memory_to_storage,
        SRULE [SF ETA_ss] alloc_run_compile_memory_to_transient,
        SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
        SRULE [SF ETA_ss] alloc_run_emit_empty_fresh] >>
        simp[comp_return_def, alloc_run_def, alloc_frame_refl] >> NO_TAC) >>
    gen_tac >> simp[comp_ignore_bind_def, comp_bind_assoc] >>
    rpt IF_CASES_TAC >> simp[comp_ignore_bind_def, comp_bind_assoc]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_store_memory,
    SRULE [SF ETA_ss] alloc_run_compile_dynarray_to_storage,
    SRULE [SF ETA_ss] alloc_run_compile_imm_store_word,
    SRULE [SF ETA_ss] alloc_run_compile_imm_store_words,
    SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
  TRY (rename1 `alloc_run _ (comp_return _) _` >>
    simp[comp_return_def, alloc_run_def, alloc_frame_refl] >> NO_TAC) >>
  PairCases_on `x` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_dynarray_to_storage]
QED

Theorem alloc_run_compile_tuple_load_all:
  !tys src offset. alloc_run fresh_outputs
    (compile_tuple_load_all ce src tys offset) (\v s. fresh_outputs s)
Proof
  Induct >> simp[compile_tuple_load_all_def]
  >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  rpt gen_tac >>
  ntac 2 (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_compile_load_memory] >> gen_tac >> simp[]) >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac
  >- (first_x_assum (mp_tac o SRULE [SF ETA_ss]) >> simp[SF ETA_ss]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_store_at_loc:
  alloc_run fresh_outputs (compile_store_at_loc imm dst src loc)
    (\u s. fresh_outputs s)
Proof
  Cases_on `loc` >> simp[compile_store_at_loc_def, alloc_run_emit_void_fresh] >>
  Cases_on `x` >> simp[compile_store_at_loc_def, alloc_run_emit_void_fresh,
    alloc_run_compile_imm_store_word]
QED

Theorem alloc_run_compile_revert_with_reason:
  alloc_run fresh_outputs (compile_revert_with_reason ce vv ty bytes)
    (\u s. fresh_outputs s)
Proof
  simp[compile_revert_with_reason_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- (simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
      SRULE [SF ETA_ss] alloc_run_unwrap_value,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >> NO_TAC) >>
    gen_tac >> simp[comp_ignore_bind_def]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_empty_fresh]
QED

Theorem alloc_run_compile_nonreentrant_unlock:
  alloc_run fresh_outputs (compile_nonreentrant_unlock key transient view)
    (\u s. fresh_outputs s)
Proof
  Cases_on `view` >> Cases_on `transient` >>
  simp[compile_nonreentrant_unlock_def, alloc_run_emit_void_fresh] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_external_return:
  alloc_run fresh_outputs
    (compile_external_return rv prim raw info bytes nr key transient view)
    (\u s. fresh_outputs s)
Proof
  simp[compile_external_return_def, comp_ignore_bind_def] >>
  Cases_on `nr` >> simp[] >>
  Cases_on `rv` >> Cases_on `raw` >> Cases_on `prim` >> simp[] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- (simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_compile_nonreentrant_unlock,
      SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
      SRULE [SF ETA_ss] alloc_run_compile_abi_encode_to_buf,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl] >> NO_TAC) >>
    gen_tac >> simp[comp_ignore_bind_def]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_empty_fresh]
QED

Theorem alloc_run_compile_log_eval_all:
  !es. (!e. MEM e es ==>
    shape_step internal compiler_label (\s. cenv_shape_ok s ce)
      (compile_expr ce (expr_type e) e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (compile_expr ce (expr_type e) e) (\v s. T)) ==>
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (compile_log_eval_all ce es)
      (\v s. shape_state s /\ cenv_shape_ok s ce)
Proof
  Induct >> simp[compile_log_eval_all_def]
  >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  gen_tac >> strip_tac >>
  irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >>
      irule_at Any (Q.INST [`R` |-> `\s. T`] alloc_run_lower_value_frame) >>
      simp[shape_stable_def] >> metis_tac[]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce` >>
  reverse conj_tac >- (first_x_assum irule >> metis_tac[]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_reason_message:
  !ce e. alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (compile_expr ce (expr_type e) e) (\v s. fresh_outputs s) ==>
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (compile_reason_message ce e) (\v s. fresh_outputs s)
Proof
  recInduct compile_reason_message_ind >> rpt strip_tac >>
  simp[Once compile_reason_message_def] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >>
      irule_at Any alloc_run_compile_bytelike_literal >>
      simp[shape_state_def, shape_base_fresh_outputs]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_tuple_store_one:
  (!env ty child. supported_target_exists (\e. e = child) bt /\
      ~supported_expr_exists expr_shape_root child ==>
    shape_step internal compiler_label (\s. cenv_shape_ok s env)
      (compile_expr env ty child) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s env)
      (compile_expr env ty child) (\v s. T)) /\
  ~supported_target_exists expr_shape_root bt ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_tuple_store_all ce [src_ty] [BaseTarget bt] [value]) (\u s. T)
Proof
  strip_tac >> simp[compile_tuple_store_all_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >>
      irule_at Any (Q.INST [`R` |-> `\s. T`] alloc_run_target_prefix_frame) >>
      simp[shape_stable_def, shape_state_def, shape_base_fresh_outputs] >>
      metis_tac[]) >>
  gen_tac >> simp[] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- (simp[comp_return_def, alloc_run_def, alloc_frame_refl] >> NO_TAC) >>
    gen_tac >> simp[]) >>
  rpt IF_CASES_TAC >> simp[] >>
  (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
   reverse conj_tac >- simp[SF ETA_ss,
     SRULE [SF ETA_ss] alloc_run_compile_store_at_loc,
     SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
     SRULE [SF ETA_ss] alloc_run_compile_assign_value] >>
   simp[comp_return_def, alloc_run_def, alloc_frame_refl])
QED

Theorem compile_tuple_store_all_cons:
  compile_tuple_store_all ce (ty::tys) (t::ts) (v::vs) =
  comp_ignore_bind (compile_tuple_store_all ce [ty] [t] [v])
    (compile_tuple_store_all ce tys ts vs)
Proof
  Cases_on `t` >> simp[compile_tuple_store_all_def, comp_ignore_bind_def,
    comp_bind_assoc, FUN_EQ_THM, comp_bind_def, comp_return_def]
QED


Theorem alloc_run_compile_dynarray_append:
  store_opc <> ALLOCA ==>
  alloc_run fresh_outputs
    (compile_dynarray_append ce base_op val_op ws es dt st cap prim load_opc store_opc)
    (\u s. fresh_outputs s)
Proof
  strip_tac >> simp[compile_dynarray_append_def, comp_ignore_bind_def,
    comp_bind_assoc] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac
    >- (simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
          SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >> NO_TAC) >>
    gen_tac >> simp[comp_ignore_bind_def, comp_bind_assoc]) >>
  irule alloc_run_bind >> qexists `\u s. fresh_outputs s` >> conj_tac
  >- (gen_tac >> simp[] >> irule alloc_run_bind >>
      qexists `\v s. fresh_outputs s` >>
      simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
        SRULE [SF ETA_ss] alloc_run_emit_void_fresh]) >>
  IF_CASES_TAC >> simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
  IF_CASES_TAC >> simp[comp_ignore_bind_def] >>
  irule alloc_run_bind >> qexists `\u s. fresh_outputs s` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_store_memory,
    SRULE [SF ETA_ss] alloc_run_compile_word_copy_loop] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED
