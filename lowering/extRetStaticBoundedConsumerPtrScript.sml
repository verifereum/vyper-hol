Theory extRetStaticBoundedConsumerPtr
Ancestors
  extRetStaticCapacityPtr extRetStaticReservedPtr extRetCopyInputsPtr
  extRetStaticFrameMetadataPtr extRetStaticStmtPtr
  representationCleanPtr stmtSimReturn exprOperandVar extRetNormalEvidencePtr
  extRetSomeComposePtr bodyPtrDefs typedCopyPtr loweringPosts
  exprLowering exprLoweringProps gasSummaryComposePtr exprSimTypedAlloc

Theorem compile_external_return_static_copy_equal_gas_path_ptr:
  !cx ctx fn PG G tn s op m n nkey ut iv st x st' cenv es ty sa sb v tv w.
    compile_external_return (SOME op) F F (AbiCopy m) n F nkey ut iv st = (x,st') /\
    (!p. op = Var p ==> not_fresh_at st p) /\
    fn_has_code st st' fn /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    stmt_state_rel ctx fn cenv cx es s /\
    expr_val_at cenv cx ty sa sb es v op s /\
    ptr_val_ok cx ty v op G tn s /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
    ~is_dynamic (vyper_to_abi_type (get_tenv cx) ty) /\ value_has_type tv v /\
    m = type_memory_size tv /\ m = n /\
    eval_operand op s = SOME w /\ op_taint tn op = {} /\
    stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx ==>
    ?G' tn' t. gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G' tn' (Halt t)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all expr_val_at_bound >> strip_tac >>
  drule_all static_val_footprint >> strip_tac >>
  `m <= n /\ n < dimword (:256)` by decide_tac >>
  drule_all compile_external_return_static_copy_gas_path_ptr >> simp[]
QED

Theorem external_frame_equal_static_copy_stmt_frag_ptr_bounded:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, nr, rr, name, args, defaults, ret, fbody)) =
    (lbl, cenv0, pos, cds, payable, nr', key, ut', view, fbody', rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv, sa) /\
  same_frame cenv next /\ source_typing_ok tops am tx /\
  assignable_type (type_env tops) ret /\ ret <> NoneT /\
  next.ce_ret_enc_info = AbiCopy m /\
  get_tenv cx = type_env tops /\ expr_type e = ret /\
  lowered_value_type next e = ret /\ ~is_word_type ret /\
  next.ce_return_pc = NONE /\ ~next.ce_raw_return /\
  next.ce_nonreentrant = (F,nkey,ut,iv) /\
  expr_sim_inv next cx env es /\ well_typed_expr env e /\
  call_evaluation_safe cx (int_calls_expr e) /\
  expr_sim_ptr d ctx PG func next cx ret e es ==>
  stmt_frag_ptr d ctx PG func cx lctx (\v es gt r. T) next
    (stmt_env next lctx ret (Return (SOME e)))
    (eval_stmt cx (Return (SOME e))) es
Proof
  strip_tac >>
  drule_all external_frame_abicopy_capacity >> strip_tac >>
  drule_all external_frame_abicopy_layout >> strip_tac >>
  rw[stmt_frag_ptr_def] >>
  drule external_return_static_copy_stmt_parts >> simp[] >>
  disch_then drule_all >> strip_tac >>
  drule_at (Pat `lower_value _ _ _ _ _ = _`) compile_lower_value_var >>
  simp[] >> disch_then assume_tac >>
  drule return_forced_admissible >> strip_tac >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_sim_ptr_def] >>
  disch_then (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  dxrule gas_outcome_ptr_normal_evidence >> strip_tac >>
  drule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _`)
    external_return_some_outcome_ptr >>
  disch_then irule >> rpt gen_tac >> strip_tac >> gvs[] >>
  `ptr_val_ok cx (expr_type e) v op G1 tn1 t` by fs[] >>
  drule_all expr_post_ptr_return_inputs >> strip_tac >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME tv` by fs[] >>
  drule_all external_return_forced_value_typed >> strip_tac >>
  `expr_val_at next cx (expr_type e) sa' sm ee v op t` by fs[expr_post_def] >>
  drule_at (Pat `compile_external_return _ _ _ _ _ _ _ _ _ _ = _`)
    compile_external_return_static_copy_equal_gas_path_ptr >>
  simp[] >> disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> disch_then drule_all >> simp[]
QED
