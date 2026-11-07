(* Checked storage/transient reason encoder; also used by failed assertions. *)
Theory reasonStorageEncoderPtr
Ancestors
  reasonStorageNormalizationPtr reasonEncoderLayoutPtr reasonNormalizedSuffixPtr
  bodyPtrDefs loweringPosts exprSimProps stmtLowering exprLowering context
  compileEnv venomState venomInst ptrDiscipline fragGasPathPtr arithmetic words
  finite_map reasonMemorySuccessPtr storageUnwrapSizingPtr exprSimHyps
  exprOperandVar exprLoweringProps allocLimits reasonResourcesPtr
  vyperTypeSystem vyperValue supportedStmts exprSimHypsDefs reasonRaiseContinuationPtr

Theorem compile_revert_storage_reason_path_ptr:
  compile_revert_with_reason cenv (LocatedValue ann p) ty m cc = ((),se) /\
  fn_has_code cc se func /\ stmt_state_rel ctx func cenv cx es s /\
  ~ctx_has_dalloca ctx /\ fn_inst_ids_distinct func /\
  s.vs_current_bb = cc.cs_current_bb /\
  s.vs_inst_idx = LENGTH cc.cs_current_insts /\ ~s.vs_halted /\
  local_ptrs_reserved cenv cc /\ 64+m < dimword(:256) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at cc x) /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  ptr_vv_ok cx ty tv (LocatedValue ann p) es G tn s /\
  vv_holds cenv cx ty tv (LocatedValue ann p) es0 s0 /\ ~is_word_type ty /\
  type_memory_bytes cenv ann = 32*n /\
  (type_memory_bytes cenv ann+31) DIV 32 = n /\
  32*n < dimword(:256) /\ n < dimword(:256) /\ 32*n <= m /\
  eval_operand p.ptr_operand s = SOME a /\ storage_holds cx tr ty tv a es s /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (StringT max)) /\
  read_result cx tv es = (INL (StringV str),es) /\
  n = type_slot_size (BaseTV (StringT max)) ==>
  ?Gf tnf sf. gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (Abort Revert_abort sf)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all reason_encoder_layout_ptr >> strip_tac >>
  drule_all reason_storage_prefix_normalized_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qpat_x_assum `msg = Var root` SUBST_ALL_TAC >>
  `c3.cs_next_id < sm.cs_next_id /\ bt < dimword(:256)` by decide_tac >>
  `?G2 tn2 sf. gas_path_ptr D 0 ctx func PG Gf tnf z 0 G2 tn2
       (Abort Revert_abort sf)` by suspend "suffix" >>
  qexistsl_tac [`G2`, `tn2`, `sf`] >>
  metis_tac[gas_path_ptr_then, ADD_CLAUSES]
QED

Resume compile_revert_storage_reason_path_ptr[suffix]:
  gvs[] >>
  drule_at (Pat `reason_encode_finish _ _ _ _ _ = _`)
    reason_normalized_suffix_path_ptr >>
  disch_then (drule_at (Pat `ptr_mem_ok _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `emit_op MLOAD _ _ = _`)) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts _)`)) >>
  simp[mk_inst_def] >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED

Finalise compile_revert_storage_reason_path_ptr

Theorem reason_storage_success_path_ptr:
  expr_body_pre cenv cx env r es /\
  supported_string_reason tops r /\ supported_expr tops r /\
  compile_expr cenv (expr_type r) r sa = (LocatedValue ann p,sm) /\
  compile_revert_with_reason cenv (LocatedValue ann p) (expr_type r)
    (type_memory_bytes cenv (expr_type r)) sm = ((),sb) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ fn_inst_ids_distinct func /\
  vv_post ctx func cenv cx r es sa sm s0 ee tv (LocatedValue ann p) t /\
  ptr_vv_ok cx (expr_type r) tv (LocatedValue ann p) ee G tn t /\
  read_result cx tv ee = (INL (StringV str),ee) /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
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
  `vv_holds cenv cx (expr_type r) tv (LocatedValue ann p) ee t /\
   stmt_state_rel ctx func cenv cx ee t` by fs[vv_post_def] >>
  drule_all located_unwrap_copy_sizing >> strip_tac >>
  `type_alloc_ok cenv (BaseT (StringT cap))` by
    metis_tac[alloc_limits_expr_type_alloc_ok] >>
  `64+type_memory_bytes cenv (expr_type r) < dimword(:256)` by
    metis_tac[reason_encoder_allocation_limit] >>
  drule (cj 1 compile_expr_grows) >> strip_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by suspend "fresh" >>
  `?a. eval_operand p.ptr_operand t = SOME a /\
       storage_holds cx tr (expr_type r) tv a ee t` by suspend "source" >>
  `32*type_slot_size (BaseTV (StringT cap)) < dimword(:256) /\
   type_slot_size (BaseTV (StringT cap)) < dimword(:256)` by
    (qpat_x_assum `64+type_memory_bytes cenv (expr_type r) < _` mp_tac >>
     qpat_x_assum `type_memory_bytes cenv ann = 32*_` mp_tac >>
     qpat_x_assum `ann = expr_type r` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >> decide_tac) >>
  gvs[valueEncodingPropsTheory.type_memory_size_slots] >>
  drule_at (Pat `compile_revert_with_reason _ _ _ _ _ = _`)
    compile_revert_storage_reason_path_ptr >>
  disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >>
  simp[] >>
  disch_then (drule_at (Pat `storage_holds _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >> simp[]
QED

Resume reason_storage_success_path_ptr[fresh]:
  drule (cj 1 compiler_compile_var) >> simp[vv_operand_def]
QED

Resume reason_storage_success_path_ptr[source]:
  qpat_x_assum `vv_holds _ _ _ _ _ _ _` mp_tac >>
  Cases_on `tr` >> simp[vv_holds_def] >> rpt strip_tac >>
  gvs[] >> goal_assum (drule_at Any) >> simp[]
QED

Finalise reason_storage_success_path_ptr

Theorem compile_raise_storage_reason_frag_ptr:
  (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
  expr_body_pre cenv cx env r es /\
  supported_string_reason tops r /\ supported_expr tops r /\
  expr_vv_sim_ptr d ctx PG func cenv cx (expr_type r) r es /\
  (!sa vv sm. compile_expr cenv (expr_type r) r sa = (vv,sm) ==>
    ?ann p tr. vv = LocatedValue ann p /\
      p.ptr_location = (if tr then LocTransient else LocStorage)) ==>
  stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Raise (RaiseReason r)))
    (eval_stmt cx (Raise (RaiseReason r))) es
Proof
  strip_tac >> irule compile_raise_reason_path_frag_ptr >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  `?ann p tr. vv = LocatedValue ann p /\
    p.ptr_location = (if tr then LocTransient else LocStorage)` by metis_tac[] >>
  gvs[] >> irule reason_storage_success_path_ptr >> metis_tac[]
QED
