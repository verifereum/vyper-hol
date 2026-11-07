Theory bodyPtrStructLitOwnershipStmtCases
Ancestors bodyPtrStructLitOwnershipStmtHelpers bodyPtrStructLitOwnershipRecursion
  bodyPtrStructLitOwnershipDeclarationRoute bodyPtrStructLitAssignFrame
  stmtLowering loweringShapeProps supportedExprTraverse compileEnv
  bodyPtrStructLitOwnershipSteps bodyPtrStructLitOwnershipInterfaces
  bodyPtrStructLitCompilerOwnership loweringShapeDefs loweringShapeRules
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipLoops
  bodyPtrStructLitOwnershipStructFrame bodyPtrStructLitTupleFrame
  bodyPtrStructLitOwnershipControlFrame bodyPtrStructLitLoopShapeDynBody
  bodyPtrStructLitOwnershipIfexpFrame context emitHelper unitShapeDefs
  venomInst stackPlanTypes bodyPtrStructLitOwnershipMemory
  bodyPtrStructLitOwnershipTyped bodyPtrStructLitOwnershipPrimitives
  bodyPtrStructLitOwnershipAbiEncode bodyPtrStructLitOwnershipPop
  bodyPtrStructLitEmitterFrame bodyPtrStructLitOwnershipScalar
  bodyPtrStructLitOwnershipStmtLoops bodyPtrStructLitOwnershipConsumers

Theorem alloc_run_stmt_nonannassign_route:
  (!id vt e. s <> AnnAssign id vt e) /\
  alloc_run P (compile_stmt ce lctx ty s) Q ==>
  alloc_run P
    (comp_bind (declare_stmt_local ce s) (\ce'. compile_stmt ce' lctx ty s)) Q
Proof
  strip_tac >> simp[alloc_run_def, comp_bind_def] >> rpt strip_tac >>
  Cases_on `declare_stmt_local ce s st` >> gvs[] >>
  drule_all declare_stmt_local_nonannassign_identity >> strip_tac >> gvs[] >>
  gvs[alloc_run_def] >> metis_tac[]
QED

Theorem alloc_run_stmt_pass:
  alloc_run (\st. T) (compile_stmt ce lctx ty Pass) (\u st. T)
Proof simp[compile_stmt_def, comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_stmt_expr:
  ~supported_expr_exists expr_shape_root e ==>
  alloc_run (\st. shape_state st /\ cenv_shape_ok st ce)
    (compile_stmt ce lctx ty (Expr e)) (\u st. T)
Proof
  strip_tac >> simp[compile_stmt_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >> qexists `\v st. T` >> reverse conj_tac
  >- simp[alloc_run_compile_expr] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_stmt_lower_value:
  ~supported_expr_exists expr_shape_root e ==>
  alloc_run (\st. shape_state st /\ cenv_shape_ok st ce)
    (lower_value compile_expr ce ty e)
    (\v st. shape_state st /\ cenv_shape_ok st ce)
Proof
  strip_tac >> irule alloc_run_conseq >>
  irule_at Any (Q.INST [`R` |-> `\s. T`] alloc_run_lower_value_frame) >>
  simp[shape_stable_def, alloc_run_compile_expr, cj 1 compile_expr_shape]
QED

Theorem alloc_run_stmt_raise_simple:
  alloc_run fresh_outputs (compile_stmt ce lctx ty (Raise RaiseBare))
    (\u st. fresh_outputs st) /\
  alloc_run fresh_outputs (compile_stmt ce lctx ty (Raise RaiseUnreachable))
    (\u st. fresh_outputs st)
Proof
  simp[compile_stmt_def, alloc_run_emit_empty_fresh]
QED


Theorem alloc_run_stmt_expr_fresh:
  ~supported_expr_exists expr_shape_root e ==>
  alloc_run (\st. shape_state st /\ cenv_shape_ok st ce)
    (compile_expr ce ety e) (\v st. fresh_outputs st)
Proof
  strip_tac >> irule alloc_run_conseq >>
  irule_at Any alloc_run_struct_child_frame >>
  qexistsl [`F`, `ce`, `\s. T`] >>
  simp[shape_stable_def, alloc_run_compile_expr, cj 1 compile_expr_shape,
    shape_state_def, shape_base_fresh_outputs]
QED

Theorem alloc_run_stmt_raise_reason:
  ~supported_expr_exists expr_shape_root e ==>
  alloc_run (\st. shape_state st /\ cenv_shape_ok st ce)
    (compile_stmt ce lctx ty (Raise (RaiseReason e)))
    (\u st. fresh_outputs st)
Proof
  strip_tac >> simp[compile_stmt_def] >> irule alloc_run_bind >>
  qexists `\v st. fresh_outputs st` >> reverse conj_tac
  >- (irule alloc_run_compile_reason_message >> simp[alloc_run_stmt_expr_fresh]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_revert_with_reason]
QED

Theorem alloc_run_stmt_assert_tail:
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce) failure
    (\(u:unit) s. fresh_outputs s) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s cond_op)
    (comp_bind (fresh_label "assert_ok") (\ok.
      comp_bind (fresh_label "assert_fail") (\fail.
        comp_ignore_bind (emit_inst JNZ [cond_op; Label ok; Label fail] [])
          (comp_ignore_bind (new_block fail)
            (comp_ignore_bind failure
              (comp_ignore_bind (new_block ok) (comp_return ())))))))
    (\u s. fresh_outputs s)
Proof
  strip_tac >> simp[comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\l s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s cond_op /\
    compiler_label l /\ label_sfx "assert_ok" l` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_fresh_label_frame >>
      qexists `\s. cenv_shape_ok s ce /\ plain_operand s cond_op` >>
      simp[shape_stable_conj, cenv_shape_ok_stable,
        SRULE [] (Q.SPEC `[cond_op]` shape_stable_plain_operands)]) >>
  qx_gen_tac `ok` >> simp[] >> irule alloc_run_bind >>
  qexists `\l s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s cond_op /\
    compiler_label ok /\ label_sfx "assert_ok" ok /\ compiler_label l /\
    label_sfx "assert_fail" l` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_fresh_label_frame >>
      qexists `\s. cenv_shape_ok s ce /\ plain_operand s cond_op /\
        compiler_label ok /\ label_sfx "assert_ok" ok` >>
      simp[shape_stable_conj, cenv_shape_ok_stable, shape_stable_def,
        SRULE [] (Q.SPEC `[cond_op]` shape_stable_plain_operands)]) >>
  qx_gen_tac `bad` >> simp[] >> suspend "branch"
QED

Resume alloc_run_stmt_assert_tail[branch]:
  reverse (Cases_on `compiler_label ok`) >- simp[alloc_run_def] >>
  reverse (Cases_on `compiler_label bad`) >- simp[alloc_run_def] >>
  reverse (Cases_on `label_sfx "assert_ok" ok`) >- simp[alloc_run_def] >>
  reverse (Cases_on `label_sfx "assert_fail" bad`) >- simp[alloc_run_def] >>
  irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ cenv_shape_ok s ce` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_jnz_frame >>
      qexists `\s. cenv_shape_ok s ce` >>
      simp[cenv_shape_ok_stable, plain_operand_def] >>
      metis_tac[SRULE [] (Q.INST [`s1` |-> `"assert_ok"`,
        `s2` |-> `"assert_fail"`] label_sfx_distinct)]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ cenv_shape_ok s ce` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_new_block_frame >>
      qexists `\s. cenv_shape_ok s ce` >> simp[cenv_shape_ok_stable]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. fresh_outputs s` >> reverse conj_tac >- simp[] >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. fresh_outputs s` >> reverse conj_tac
  >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_new_block_fresh] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED
Finalise alloc_run_stmt_assert_tail

Theorem alloc_run_stmt_assert_reason:
  ~supported_expr_exists expr_shape_root cond /\
  ~supported_expr_exists expr_shape_root reason ==>
  alloc_run (\st. shape_state st /\ cenv_shape_ok st ce)
    (compile_stmt ce lctx ty (Assert cond (AssertReason reason)))
    (\u st. fresh_outputs st)
Proof
  strip_tac >> simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >>
  qexists `\op s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s op` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`F`, `\s. T`] >>
      simp[shape_stable_def, cj 1 compile_expr_shape, alloc_run_compile_expr]) >>
  gen_tac >> simp[loop_comp_return_bind, SF ETA_ss] >>
  ho_match_mp_tac (SRULE [compile_stmt_def, LET_THM, comp_ignore_bind_def, comp_bind_assoc,
    loop_comp_return_bind, SF ETA_ss] (Q.INST
      [`failure` |-> `compile_stmt ce lctx ty (Raise (RaiseReason reason))`]
      alloc_run_stmt_assert_tail)) >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_compile_reason_message >> simp[alloc_run_stmt_expr_fresh]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_revert_with_reason]
QED

Theorem alloc_run_stmt_assert_simple:
  ~supported_expr_exists expr_shape_root cond ==>
  alloc_run (\st. shape_state st /\ cenv_shape_ok st ce)
    (compile_stmt ce lctx ty (Assert cond AssertBare)) (\u st. fresh_outputs st) /\
  alloc_run (\st. shape_state st /\ cenv_shape_ok st ce)
    (compile_stmt ce lctx ty (Assert cond AssertUnreachable)) (\u st. fresh_outputs st)
Proof
  strip_tac >> conj_tac >>
  (simp[Once compile_stmt_def, comp_ignore_bind_def] >> irule alloc_run_bind >>
   qexists `\op s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s op` >>
   reverse conj_tac
   >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
       qexistsl [`F`, `\s. T`] >>
       simp[shape_stable_def, cj 1 compile_expr_shape, alloc_run_compile_expr]) >>
   gen_tac >> simp[SF ETA_ss] >>
   ho_match_mp_tac (SRULE [comp_ignore_bind_def, comp_bind_assoc,
     SF ETA_ss] alloc_run_stmt_assert_tail) >>
   irule alloc_run_conseq >> irule_at Any alloc_run_emit_empty_fresh >>
   simp[shape_state_def, shape_base_fresh_outputs])
QED

Theorem alloc_run_stmt_return_exit:
  alloc_run fresh_outputs
    (case ce.ce_ctor_exit_label of
       SOME l => emit_inst JMP [Label l] []
     | NONE => (\(nr,key,tr,view).
         comp_ignore_bind
           (if nr then compile_nonreentrant_unlock key tr view else comp_return ())
           (emit_inst STOP [] [])) ce.ce_nonreentrant)
    (\u s. fresh_outputs s)
Proof
  Cases_on `ce.ce_ctor_exit_label` >> simp[alloc_run_emit_empty_fresh] >>
  pairarg_tac >> simp[comp_ignore_bind_def] >>
  irule alloc_run_bind >> qexists `\u s. fresh_outputs s` >>
  reverse conj_tac
  >- (IF_CASES_TAC >> simp[alloc_run_compile_nonreentrant_unlock] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_empty_fresh]
QED

Theorem alloc_run_stmt_return_none:
  alloc_run fresh_outputs (compile_stmt ce lctx ty (Return NONE))
    (\u s. fresh_outputs s)
Proof
  simp[compile_stmt_def] >> Cases_on `ce.ce_return_pc` >>
  simp[alloc_run_stmt_return_exit] >>
  Cases_on `x` >> simp[alloc_run_emit_empty_fresh, alloc_run_stmt_return_exit] >>
  simp[comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\u s. fresh_outputs s` >> reverse conj_tac
  >- simp[alloc_run_emit_op_fresh] >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_empty_fresh]
QED

Theorem alloc_run_stmt_return_external_value:
  alloc_run fresh_outputs
    (comp_bind
      (if normalize then
         comp_bind (compile_alloc_buffer (type_memory_bytes ce ty)) (\buf.
           comp_bind (comp_return buf.buf_operand) (\ptr.
             comp_ignore_bind (compile_store_memory_typed ce ptr ty op src)
               (comp_return ptr)))
       else comp_return op)
      (\ret. compile_external_return (SOME ret) (is_word_type ty) ce.ce_raw_return
        ce.ce_ret_enc_info ce.ce_max_return_size (FST ce.ce_nonreentrant)
        (FST (SND ce.ce_nonreentrant)) (FST (SND (SND ce.ce_nonreentrant)))
        (SND (SND (SND ce.ce_nonreentrant)))))
    (\u s. fresh_outputs s)
Proof
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[]
      >- (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
          reverse conj_tac >- simp[alloc_run_compile_alloc_buffer] >>
          gen_tac >> simp[loop_comp_return_bind, comp_ignore_bind_def] >>
          irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
          reverse conj_tac
          >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_store_memory_typed] >>
          simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_external_return]
QED

Theorem alloc_run_stmt_return_some:
  ~supported_expr_exists expr_shape_root e ==>
  alloc_run (\st. shape_state st /\ cenv_shape_ok st ce)
    (compile_stmt ce lctx ty (Return (SOME e))) (\u st. fresh_outputs st)
Proof
  strip_tac >> simp[Once compile_stmt_def] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_stmt_lower_value >>
      simp[shape_state_def, shape_base_fresh_outputs]) >>
  gen_tac >> simp[SF ETA_ss] >> Cases_on `ce.ce_return_pc` >>
  simp[LET_THM, SF ETA_ss, SRULE [SF ETA_ss] alloc_run_stmt_return_external_value] >>
  Cases_on `x` >> simp[LET_THM, SF ETA_ss,
    SRULE [SF ETA_ss] alloc_run_compile_internal_return_from_env,
    SRULE [SF ETA_ss] alloc_run_stmt_return_external_value] >>
  simp[comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- simp[alloc_run_emit_op_fresh] >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_internal_return_from_env]
QED

Theorem alloc_run_stmt_log:
  (!e. MEM e args ==> ~supported_expr_exists expr_shape_root e) ==>
  alloc_run (\st. shape_state st /\ cenv_shape_ok st ce)
    (compile_stmt ce lctx ty (Log event_id args)) (\u st. fresh_outputs st)
Proof
  strip_tac >> simp[Once compile_stmt_def] >>
  Cases_on `ce.ce_event_info (nsid_to_string event_id)` >> simp[]
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_emit_empty_fresh >>
      simp[shape_state_def, shape_base_fresh_outputs]) >>
  PairCases_on `x` >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_compile_log_eval_all >>
      qexists `F` >> simp[cj 1 compile_expr_shape, alloc_run_compile_expr,
        shape_state_def, shape_base_fresh_outputs]) >>
  gen_tac >> simp[loop_comp_return_bind, comp_ignore_bind_def] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_log_topic_ops] >>
  gen_tac >> simp[loop_comp_return_bind] >> IF_CASES_TAC >> simp[]
  >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_empty_fresh] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac
    >- (simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
        SRULE [SF ETA_ss] alloc_run_compile_log_store_data,
        SRULE [SF ETA_ss] alloc_run_compile_abi_encode_to_buf] >> NO_TAC) >>
    gen_tac >> simp[loop_comp_return_bind, comp_ignore_bind_def]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_empty_fresh]
QED

Theorem alloc_run_stmt_assign_tuple:
  ~supported_expr_exists expr_shape_root e /\
  ~supported_assignments_exists expr_shape_root bts ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_stmt ce lctx ty (Assign (TupleTarget bts) e))
    (\u s. shape_state s /\ cenv_shape_ok s ce)
Proof
  strip_tac >> simp[compile_stmt_def] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ value_shape_ok s v` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_struct_child_frame >>
      qexistsl [`F`, `ce`, `\s. T`] >>
      simp[shape_stable_def, alloc_run_compile_expr, cj 1 compile_expr_shape]) >>
  qx_gen_tac `vv` >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s v` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_unwrap_value_frame >>
      qexists `\s. cenv_shape_ok s ce` >> simp[cenv_shape_ok_stable]) >>
  gen_tac >> simp[] >> irule alloc_run_conseq >>
  irule_at Any alloc_run_compile_tuple_unpack_frame >>
  qexistsl [`F`, `\s. T`] >>
  simp[shape_stable_def, alloc_run_compile_expr, cj 1 compile_expr_shape] >>
  metis_tac[assignments_exclude_base_target]
QED

Theorem alloc_run_stmt_assign_base:
  ~supported_expr_exists expr_shape_root e /\
  ~supported_target_exists expr_shape_root bt ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_stmt ce lctx ty (Assign (BaseTarget bt) e))
    (\u s. fresh_outputs s)
Proof
  strip_tac >> simp[compile_stmt_def] >> IF_CASES_TAC
  >- (irule alloc_run_bind >> qexists `\r s. fresh_outputs s` >>
      reverse conj_tac
      >- (irule alloc_run_conseq >> irule_at Any alloc_run_target_prefix_frame >>
          qexistsl [`F`, `\s. T`] >>
          simp[shape_stable_def, alloc_run_compile_expr, cj 1 compile_expr_shape,
            shape_state_def, shape_base_fresh_outputs]) >>
      simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_store_at_loc]) >>
  irule alloc_run_bind >>
  qexists `\vv s. shape_state s /\ cenv_shape_ok s ce /\ value_shape_ok s vv` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_struct_child_frame >>
      qexistsl [`F`, `ce`, `\s. T`] >>
      simp[shape_stable_def, alloc_run_compile_expr, cj 1 compile_expr_shape]) >>
  qx_gen_tac `vv` >> simp[] >> irule alloc_run_bind >>
  qexists `\r s. shape_state s /\ cenv_shape_ok s ce /\ value_shape_ok s vv` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_target_prefix_frame >>
      qexistsl [`F`, `\s. value_shape_ok s vv`] >>
      simp[value_shape_ok_stable, alloc_run_compile_expr, cj 1 compile_expr_shape]) >>
  qx_gen_tac `r` >> simp[loop_comp_return_bind] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_unwrap_value_frame >>
      qexists `\s. T` >> simp[shape_stable_def, shape_state_def,
        shape_base_fresh_outputs]) >>
  gen_tac >> simp[] >> Cases_on `FST (SND r)` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_assign_value,
    SRULE [SF ETA_ss] alloc_run_emit_void_fresh]
QED

Theorem alloc_run_stmt_augassign:
  ~supported_expr_exists expr_shape_root e /\
  ~supported_target_exists expr_shape_root bt ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_stmt ce lctx ty (AugAssign ety bt bop e))
    (\u s. fresh_outputs s)
Proof
  strip_tac >> simp[compile_stmt_def] >> irule alloc_run_bind >>
  qexists `\r s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s (FST r)` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_target_prefix_frame >>
      qexistsl [`F`, `\s. T`] >>
      simp[shape_stable_def, alloc_run_compile_expr, cj 1 compile_expr_shape]) >>
  qx_gen_tac `r` >> simp[loop_comp_return_bind] >> Cases_on `FST (SND r)`
  >- (simp[] >> irule alloc_run_conseq >>
      irule_at Any alloc_run_emit_void_fresh >>
      simp[shape_state_def, shape_base_fresh_outputs]) >>
  simp[loop_comp_return_bind] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_op_frame >>
      qexists `\s. cenv_shape_ok s ce` >>
      simp[cenv_shape_ok_stable] >> Cases_on `x` >>
      simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
        inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
        label_positions_ok_def, is_terminator_def, plain_operand_def]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_stmt_lower_value >>
      simp[shape_state_def, shape_base_fresh_outputs]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_binop,
    SRULE [SF ETA_ss] alloc_run_emit_void_fresh]
QED

Theorem alloc_run_stmt_loop_exit:
  alloc_run fresh_outputs (compile_stmt ce lctx ty Break)
    (\u s. fresh_outputs s) /\
  alloc_run fresh_outputs (compile_stmt ce lctx ty Continue)
    (\u s. fresh_outputs s)
Proof
  Cases_on `lctx` >>
  simp[compile_stmt_def, comp_ignore_bind_def] >>
  rpt conj_tac >>
  TRY (irule alloc_run_bind >> qexists `\u s. fresh_outputs s` >>
    conj_tac >- simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  simp[SF ETA_ss, alloc_run_emit_empty_fresh]
QED

Theorem alloc_run_stmt_annassign_initializer:
  ~supported_expr_exists expr_shape_root e ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (do src_vv <- compile_expr ce (expr_type e) e;
        val_op <- (if has_length_word vt /\ is_empty_value_expr e then return (Lit 0w)
                   else unwrap_value ce src_vv);
        (case FLOOKUP ce.ce_vars id of
          SOME (MemLoc off _) =>
            if has_length_word vt /\ is_empty_value_expr e then
              emit_void MSTORE [Lit (n2w off); Lit 0w]
            else compile_assign_value ce (Lit (n2w off)) LocMemory val_op
              (is_word_type vt) (vv_location src_vv) vt (lowered_value_type ce e)
              (case vt of ArrayT et (Dynamic _) =>
                SOME ((type_memory_bytes ce et + 31) DIV 32, type_memory_bytes ce et)
               | _ => NONE) (type_memory_bytes ce vt)
        | SOME (PtrVar p _) =>
            if has_length_word vt /\ is_empty_value_expr e then
              emit_void MSTORE [p; Lit 0w]
            else compile_assign_value ce p LocMemory val_op
              (is_word_type vt) (vv_location src_vv) vt (lowered_value_type ce e)
              (case vt of ArrayT et (Dynamic _) =>
                SOME ((type_memory_bytes ce et + 31) DIV 32, type_memory_bytes ce et)
               | _ => NONE) (type_memory_bytes ce vt)
        | _ => emit_void INVALID []) od)
    (\u s. fresh_outputs s)
Proof
  strip_tac >> irule alloc_run_bind >>
  qexists `\vv s. shape_state s /\ cenv_shape_ok s ce /\ value_shape_ok s vv` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_struct_child_frame >>
      qexistsl [`F`, `ce`, `\s. T`] >>
      simp[shape_stable_def, alloc_run_compile_expr, cj 1 compile_expr_shape]) >>
  qx_gen_tac `vv` >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (IF_CASES_TAC
      >- simp[comp_return_def, alloc_run_def, alloc_frame_refl, shape_state_def,
           shape_base_fresh_outputs] >>
      irule alloc_run_conseq >> irule_at Any alloc_run_unwrap_value_frame >>
      qexists `\s. T` >> simp[shape_stable_def, shape_state_def,
        shape_base_fresh_outputs]) >>
  gen_tac >> simp[] >> Cases_on `FLOOKUP ce.ce_vars id` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
  Cases_on `x` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >> IF_CASES_TAC >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
    SRULE [SF ETA_ss] alloc_run_compile_assign_value]
QED

Theorem alloc_run_stmt_annassign_route:
  ce.ce_alloca_locals /\ ~supported_expr_exists expr_shape_root e ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (comp_bind (declare_stmt_local ce (AnnAssign id vt e))
      (\env. compile_stmt env lctx ty (AnnAssign id vt e)))
    (\u s. fresh_outputs s)
Proof
  strip_tac >> simp[declare_stmt_local_def, compile_stmt_def,
    comp_ignore_bind_def, loop_comp_return_bind] >>
  ho_match_mp_tac (SRULE [comp_ignore_bind_def, comp_bind_assoc,
    loop_comp_return_bind] (Q.INST [`R` |-> `\s. T`]
      alloc_run_declare_local_commit_then)) >>
  simp[shape_stable_def] >>
  rpt strip_tac >>
  irule (SRULE [loop_comp_return_bind] alloc_run_stmt_annassign_initializer) >>
  simp[]
QED

Theorem alloc_run_stmt_append:
  ~supported_expr_exists expr_shape_root e ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_stmt ce lctx ty (Append bt e)) (\u s. fresh_outputs s)
Proof
  strip_tac >> simp[compile_stmt_def] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_stmt_lower_value >>
      simp[shape_state_def, shape_base_fresh_outputs]) >>
  gen_tac >> simp[loop_comp_return_bind] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (IF_CASES_TAC
      >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
      simp[comp_ignore_bind_def] >>
      rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
        reverse conj_tac
        >- (simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
              SRULE [SF ETA_ss] alloc_run_compile_store_memory] >> NO_TAC) >>
        gen_tac >> simp[]) >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  gen_tac >> simp[loop_comp_return_bind, SF ETA_ss] >>
  irule (SRULE [SF ETA_ss] alloc_run_compile_dynarray_append) >>
  Cases_on `infer_array_location ce (target_to_expr bt)` >>
  simp[store_opc_for_def]
QED
