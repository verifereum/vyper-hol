(* Pointer-safe statement wrappers, shared with reason-bearing assertion clients. *)
Theory reasonRaisePtr
Ancestors
  reasonCodeEncoderPtr reasonStorageEncoderPtr reasonMemorySuccessPtr
  reasonLiteralPtr reasonRaiseContinuationPtr
  bodyPtrDefs loweringPosts exprSimHyps exprSimHypsDefs storageUnwrapSizingPtr
  exprLoweringProps exprOperandVar allocLimits exprSimProps vyperTypeSystem
  vyperValue supportedStmts context compileEnv venomState ptrDiscipline words
  reasonResourcesPtr exprReasonOperand supportedExprs supportedExprTraverse

Theorem reason_code_success_path_ptr:
  expr_body_pre cenv cx env r es /\
  supported_string_reason tops r /\ supported_expr tops r /\
  compile_expr cenv (expr_type r) r sa = (LocatedValue ann p,sm) /\
  compile_revert_with_reason cenv (LocatedValue ann p) (expr_type r)
    (type_memory_bytes cenv (expr_type r)) sm = ((),sb) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\ fn_inst_ids_distinct func /\
  vv_post ctx func cenv cx r es sa sm s0 ee tv (LocatedValue ann p) t /\
  ptr_vv_ok cx (expr_type r) tv (LocatedValue ann p) ee G tn t /\
  read_result cx tv ee = (INL (StringV str),ee) /\ p.ptr_location = LocCode /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?Gf tnf u. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn t 0 Gf tnf
    (Abort Revert_abort u)
Proof
  strip_tac >>
  `well_typed_expr env r /\ alloc_limits_expr cenv r` by fs[expr_body_pre_def] >>
  drule_all reason_supported_string_type >> strip_tac >>
  `evaluate_type (get_tenv cx) (expr_type r) = SOME (BaseTV (StringT cap)) /\
   ~is_word_type (expr_type r)` by
    (conj_tac
     >- (drule expr_body_pre_type_evaluates >> simp[evaluate_type_def] >>
         rpt strip_tac >> gvs[]) >>
     gvs[is_word_type_def]) >>
  `post_value_type cenv r = expr_type r` by
    (irule loweringPostsTheory.post_value_type_bytestring >>
     fs[compileEnvTheory.is_bytestring_type_def]) >>
  `vv_holds cenv cx (expr_type r) tv (LocatedValue ann p) ee t /\
   stmt_state_rel ctx func cenv cx ee t` by fs[vv_post_def] >>
  `p.ptr_location <> LocMemory` by fs[] >>
  drule_all located_unwrap_copy_sizing >> strip_tac >>
  `type_alloc_ok cenv (BaseT (StringT cap))` by
    metis_tac[alloc_limits_expr_type_alloc_ok] >>
  `64+type_memory_bytes cenv (expr_type r) < dimword(:256)` by
    metis_tac[reason_encoder_allocation_limit] >>
  drule (cj 1 compile_expr_grows) >> strip_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    (drule (cj 1 compiler_compile_var) >> simp[vv_operand_def]) >>
  `?a. eval_operand p.ptr_operand t = SOME a /\
       immutable_holds cenv cx (expr_type r) tv a ee t` by
    (qpat_x_assum `vv_holds _ _ _ _ _ _ _` mp_tac >>
     simp[vv_holds_def] >> rpt strip_tac >> gvs[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `32*type_slot_size (BaseTV (StringT cap)) < dimword(:256)` by
    (qpat_x_assum `64+type_memory_bytes cenv (expr_type r) < _` mp_tac >>
     qpat_x_assum `type_memory_bytes cenv ann = 32*_` mp_tac >>
     qpat_x_assum `ann = expr_type r` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >> decide_tac) >>
  drule_at (Pat `compile_revert_with_reason _ _ _ _ _ = _`)
    compile_revert_code_reason_path_ptr >>
  disch_then (drule_at (Pat `immutable_holds _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  simp[] >> gvs[ptr_vv_ok_def] >> metis_tac[]
QED

Theorem compile_raise_code_reason_shared_frag_ptr:
  (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
  expr_body_pre cenv cx env r es /\
  supported_string_reason tops r /\ supported_expr tops r /\
  expr_vv_sim_ptr d ctx PG func cenv cx (expr_type r) r es /\
  (!sa vv sm. compile_expr cenv (expr_type r) r sa = (vv,sm) ==>
    reason_code_vv vv) ==>
  stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Raise (RaiseReason r)))
    (eval_stmt cx (Raise (RaiseReason r))) es
Proof
  strip_tac >> irule compile_raise_reason_path_frag_ptr >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  `reason_code_vv vv` by metis_tac[] >>
  gvs[reason_code_vv_def] >>
  `well_typed_expr env r /\ alloc_limits_expr cenv r` by fs[expr_body_pre_def] >>
  drule_all reason_supported_string_type >> strip_tac >>
  `post_value_type cenv r = expr_type r` by
    (irule loweringPostsTheory.post_value_type_bytestring >>
     fs[compileEnvTheory.is_bytestring_type_def]) >>
  qpat_x_assum `post_value_type cenv r = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  irule reason_code_success_path_ptr >> metis_tac[]
QED

Theorem reason_supported_expression:
  supported_string_reason tops e ==>
  supported_expr tops e /\ ~supported_expr_exists expr_internal_call_root e
Proof
  strip_tac >>
  `supported_pure_expr tops e` by
    (Cases_on `e` >> gvs[supported_string_reason_def] >>
     rename1 `Literal ty lit` >> Cases_on `lit` >>
     gvs[supported_string_reason_def, supported_pure_expr_def]) >>
  conj_tac
  >- simp[supported_expr_def] >>
  metis_tac[supported_pure_no_internal_call, expr_has_internal_call_def]
QED
