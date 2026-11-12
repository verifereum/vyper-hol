(* Representation dispatch for a typed string reason at an expression endpoint. *)
Theory reasonDispatchPtr
Ancestors
  reasonFragmentPtr reasonMemoryConsumerPtr reasonStorageConsumerPtr
  reasonCodeConsumerPtr reasonLiteralConsumerPtr reasonEndpointResourcesPtr
  loweringPosts exprLoweringProps exprSimProps compileEnv context
  bodyPtrDefs ptrDiscipline arithmetic list reasonTypingProps exprSimSource
  reasonCompilerProps reasonSourceProps gasSummaryComposePtr gasSummary
  gasExemptCert gasCount stmtSimDefs stmtSimProps exprSimDefs vyperAST
  vyperInterpreter vyperState exprLowering stmtLowering fragGasPathPtr fragExec

Theorem compile_revert_string_endpoint_ptr:
  compile_expr cenv (expr_type r) r sa = (vv,sm) /\
  expr_type r = BaseT (StringT max) /\
  evaluate_type (get_tenv cx) (BaseT (StringT max)) = SOME (BaseTV (StringT max)) /\
  type_alloc_ok cenv (BaseT (StringT max)) /\
  val_wf (BaseTV (StringT max)) (StringV str) /\
  compile_revert_with_reason cenv vv (expr_type r)
    (type_memory_bytes cenv (expr_type r)) sm = ((),sb) /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  vv_post ctx fn cenv cx r es sa sm s0 ee tv vv t /\
  ptr_vv_ok cx (expr_type r) tv vv ee G tn t /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  read_result cx tv ee = (INL (StringV str),ee) ==>
  ?z Gf tnf. gas_path_ptr D 0 ctx fn PG G tn t 0 Gf tnf (Abort Revert_abort z)
Proof
  strip_tac >>
  `copy_old_operand sm (vv_operand vv)` by metis_tac[compile_expr_old_operand] >>
  `sa.cs_next_var <= sm.cs_next_var` by metis_tac[cj 1 compile_expr_grows] >>
  `!k. k < 3 ==> not_local_ptr cenv ee.scopes
    (STRING #"%" (toString (sm.cs_next_var+k)))` by
    (rpt strip_tac >> irule local_ptrs_reserved_fresh >>
     goal_assum (drule_at Any) >> decide_tac) >>
  `post_value_type cenv r = expr_type r` by
    (irule loweringPostsTheory.post_value_type_bytestring >>
     fs[compileEnvTheory.is_bytestring_type_def]) >>
  qpat_x_assum `post_value_type _ _ = _` (fn th => fs[vv_post_def, th]) >>
  gvs[] >> Cases_on `vv`
  >- (irule (INST_TYPE [alpha |-> ``:type``] compile_revert_memory_string_endpoint_ptr) >> simp[] >>
      goal_assum (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
      simp[vv_operand_def, ADD_COMM] >>
      qexistsl [`BaseT (StringT max) : type`,`sb`] >> fs[vv_operand_def]) >>
  rename1 `LocatedValue vty p` >>
  Cases_on `p.ptr_location`
  >- suspend "memory"
  >- suspend "storage"
  >- suspend "transient"
  >- suspend "code"
  >> fs[vv_holds_def]
QED

Resume compile_revert_string_endpoint_ptr[memory]:
  `is_bytestring_type vty` by
    (fs[vv_holds_def] >> metis_tac[is_bytestring_type_def]) >>
  `~is_word_type vty` by
    (Cases_on `vty` >> gvs[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> gvs[is_bytestring_type_def, is_word_type_def]) >>
  irule (INST_TYPE [alpha |-> ``:type``] compile_revert_memory_string_endpoint_ptr) >>
  simp[] >> goal_assum (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
  simp[is_word_type_def, ADD_COMM] >>
  qexistsl [`BaseT (StringT max) : type`,`sb`] >> fs[vv_operand_def]
QED

Resume compile_revert_string_endpoint_ptr[storage]:
  `vty = BaseT (StringT max)` by fs[vv_holds_def] >> gvs[] >>
  irule (INST_TYPE [alpha |-> ``:type``] compile_revert_storage_string_endpoint_ptr) >>
  simp[] >> goal_assum (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >>
  qexists `BaseT (StringT max) : type` >> qexists `sm` >>
  qexistsl [`sb`,`str`,`F`] >>
  fs[vv_operand_def, ADD_COMM]
QED

Resume compile_revert_string_endpoint_ptr[transient]:
  `vty = BaseT (StringT max)` by fs[vv_holds_def] >> gvs[] >>
  irule (INST_TYPE [alpha |-> ``:type``] compile_revert_storage_string_endpoint_ptr) >>
  simp[] >> goal_assum (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >>
  qexists `BaseT (StringT max) : type` >> qexists `sm` >>
  qexistsl [`sb`,`str`,`T`] >>
  fs[vv_operand_def, ADD_COMM]
QED

Resume compile_revert_string_endpoint_ptr[code]:
  `vty = BaseT (StringT max)` by fs[vv_holds_def] >> gvs[] >>
  irule (INST_TYPE [alpha |-> ``:type``] compile_revert_code_string_endpoint_ptr) >>
  simp[] >> goal_assum (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >>
  qexists `BaseT (StringT max) : type` >> qexists `sm` >>
  qexistsl [`sb`,`str`] >>
  fs[vv_operand_def, ADD_COMM]
QED

Finalise compile_revert_string_endpoint_ptr

Theorem compile_raise_typed_reason_frag_ptr:
  (!mx str. r <> Literal (BaseT (StringT mx)) (StringL str)) /\
  expr_body_pre cenv cx env r es /\
  expr_vv_sim_ptr d ctx PG fn cenv cx (expr_type r) r es ==>
  stmt_frag_ptr d ctx PG fn cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Raise (RaiseReason r)))
    (eval_stmt cx (Raise (RaiseReason r))) es
Proof
  strip_tac >> irule compile_raise_reason_path_frag_ptr >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env r (es with gas_obs := gs)` by simp[] >>
  drule_all reason_string_source_typing >> strip_tac >>
  `post_value_type cenv r = expr_type r` by
    (irule loweringPostsTheory.post_value_type_bytestring >>
     fs[compileEnvTheory.is_bytestring_type_def]) >>
  qpat_x_assum `post_value_type cenv r = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  irule compile_revert_string_endpoint_ptr >> simp[] >>
  goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  simp[] >> metis_tac[]
QED

Theorem compile_raise_literal_reason_frag_ptr:
  expr_body_pre cenv cx env (Literal (BaseT (StringT mx)) (StringL str)) es ==>
  stmt_frag_ptr d ctx PG fn cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Raise (RaiseReason (Literal (BaseT (StringT mx)) (StringL str)))))
    (eval_stmt cx (Raise (RaiseReason (Literal (BaseT (StringT mx)) (StringL str))))) es
Proof
  strip_tac >> drule literal_reason_source_resources >> strip_tac >>
  simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule compile_raise_reason_parts >> strip_tac >>
  drule_all raise_reason_compiler_code >> strip_tac >>
  qpat_x_assum `compile_reason_message _ _ _ = _` mp_tac >>
  simp[compile_reason_message_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[expr_type_def] >>
  rename1 `compile_bytelike_literal _ _ sa = (buf,sm)` >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qspec_then `sa` mp_tac
       (Q.SPECL [`MAP (n2w o ORD) str`,`mx`] ci_mono_compile_bytelike_literal) >>
     gvs[ci_mono_def]) >>
  `!k. k < 3 ==> not_local_ptr cenv es.scopes
    (STRING #"%" (toString (sm.cs_next_var+k)))` by
    (rpt strip_tac >> irule local_ptrs_reserved_fresh >>
     goal_assum (drule_at Any) >> decide_tac) >>
  `?z Gf tnf. gas_path_ptr (cx_dead cx) 0 ctx fn PG G0 tn0 s0 0 Gf tnf
    (Abort Revert_abort z)` by
    (irule (INST_TYPE [alpha |-> ``:type``] compile_literal_revert_path_ptr) >>
     simp[] >> goal_assum (drule_at (Pat `compile_bytelike_literal _ _ _ = _`)) >>
     simp[] >> goal_assum (drule_at (Pat `compile_revert_with_reason _ _ _ _ _ = _`)) >>
     simp[is_word_type_def, ADD_COMM] >>
     qexistsl [`cx`,`es`] >> simp[] >> rpt strip_tac >>
     qpat_x_assum `!k. k < 3 ==> not_local_ptr _ _ _` (qspec_then `k` mp_tac) >>
     simp[ADD_COMM]) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def, eval_raise_string_literal_reason] >>
  qexistsl [`INR (AssertException str)`,`es`,`Gf`,`tnf`,`Abort Revert_abort z`] >>
  simp[exit_result_def, stmt_exit_ptr_def, expr_exit_def]
QED
