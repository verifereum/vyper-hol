(* Join operand simulation with decoder paths and whole-expression origins. *)
Theory abiDecodePtrExprComplete
Ancestors
  loweringStateRelDefs exprSimHashBoundary exprSimWordArgs
  abiDecodePtrExpr abiDecodePtrUnaryOrigin abiDecodePtrResultPost
  abiDecodePtrRejectOutcome abiDecodePtrCallerMetadata
  abiDecodePtrCallbackMetadata abiDecodePtrSuccessPost
  bodyPtrHashBuiltinsGhostCompose fragGasPathPtr
  abiDecoderCoherence abiDecoderMemberInfos loweringPosts exprLoweringProps
  abiDecodePtrSupportedTarget abiDecodePtrTarget abiDecoderAppend
  exprPtrUnwrap bodyPtrDefs bodyPtrPreds bodySim exprSimHypsDefs
  exprLowering builtinAbi context fragExec emitHelper compileEnv
  exprSimExtract32Source exprSimSource exprSimHash bodyPtrHashBuiltinsCases
  vyperState vyperInterpreter vyperAST vyperContext vyperABI list

Theorem cs_appends_lower_abi_decode:
  cs_appends (lower_abi_decode data info mn mx cap)
Proof
  rewrite_tac[lower_abi_decode_def] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >> gen_tac >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >> gen_tac >>
  ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >>
      rpt (ho_match_mp_tac cs_appends_bind >> conj_tac
        >- simp[cs_appends_emit_helpers] >> gen_tac) >>
      simp[cs_appends_emit_helpers]) >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_abi_alloc_buffer] >> gen_tac >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_return] >> gen_tac >>
  ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- simp[cs_appends_abi_decode_mutual] >>
  simp[cs_appends_return]
QED

Theorem abi_decode_normal_callback:
  body_inv decls ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin (TupleT tys) (AbiDecode b) (TupleT tys) [e]) es /\
  expr_body_pre cenv cx env e es /\
  EVERY supported_scalar_type tys /\ 2 <= LENGTH tys /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  as_ptr_val (TupleT tys) LocMemory
    (lower_abi_decode x (type_to_abi_dec_info cenv.ce_struct_fields cenv (TupleT tys))
      (abi_static_size cenv.ce_struct_fields (TupleT tys))
      (abi_size_bound cenv.ce_struct_fields (TupleT tys))
      (type_memory_bytes cenv (TupleT tys)) sm) = (vv,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  ee.gas_obs = [] /\ expr_post H ctx func cenv cx e es sa sm s0 ee v x s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ghost_inv H d cenv cx ee G tn s /\ ptr_val_ok cx (expr_type e) v x G tn s /\
  (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e x G s) /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  stmt_state_rel H ctx func cenv cx es s0 ==>
  (?marks. gas_summary_ptr_at (cx_dead H cx) (ctx,func) PG marks
    (bind (lift_sum (evaluate_type_builtin cx (AbiDecode b) (TupleT tys) [expr_type e] [v]))
      (\w. return (Value w))) (ee,s,G,tn)
    (\res ef G' tn' t. ?tv. res = INL tv /\
      vv_post H ctx func cenv cx (TypeBuiltin (TupleT tys) (AbiDecode b) (TupleT tys) [e])
        es sa sb s0 ef tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv H d cenv cx ef G' tn' t /\
      ptr_vv_ok cx (expr_type (TypeBuiltin (TupleT tys) (AbiDecode b) (TupleT tys) [e]))
        tv vv ef G' tn' t /\
      (!t' op. vv = StackValue t' op /\
        ~is_word_type (expr_type (TypeBuiltin (TupleT tys) (AbiDecode b) (TupleT tys) [e])) ==>
        ptr_buf_ok cenv (TypeBuiltin (TupleT tys) (AbiDecode b) (TupleT tys) [e]) op G' t) /\
      (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv (TypeBuiltin (TupleT tys) (AbiDecode b) (TupleT tys) [e])
          p.ptr_operand G' t) /\ ghost_kept cenv es sa G0 tn0 s0 G' tn')
    (\res ef gt r. expr_exit res r)) \/
  (evaluate_type_builtin cx (AbiDecode b) (TupleT tys) [expr_type e] [v] =
     INR (RuntimeError "abi_decode invalid") /\
   ?target_ty. occurs_abi_decode_target target_ty (cx_tops cx) /\
     is_dynamic (vyper_to_abi_type (type_env (cx_tops cx)) target_ty))
Proof
  strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  `?bs. v = BytesV bs /\ LENGTH bs <= cap` by
    metis_tac[extract32_source_value] >> gvs[] >>
  `evaluate_type (get_tenv cx) (expr_type e) =
    SOME (BaseTV (BytesT (Dynamic cap)))` by
    (drule exprSimHypsTheory.expr_body_pre_type_evaluates >>
     simp[vyperValueTheory.evaluate_type_def] >> rpt IF_CASES_TAC >> gvs[]) >>
  drule_all hash_dynamic_post_view >> strip_tac >>
  `~is_word_type (expr_type e)` by simp[is_word_type_def] >>
  gvs[] >> drule_all hash_dynamic_bytes_operand >> strip_tac >> gvs[] >>
  drule_all abi_decode_body_machine_bounds >> strip_tac >>
  drule_all abi_decode_body_tuple_coherence >> strip_tac >>
  drule_all abi_decode_located_compile_view >> strip_tac >>
  drule_all abi_decode_operand_compile_freshness >> strip_tac >>
  fs[abi_decoder_tuple_infos] >>
  `type_memory_bytes cenv (TupleT tys) = SUM (MAP (type_memory_bytes cenv) tys)` by
    metis_tac[type_memory_bytes_def] >>
  `wb_frame cenv es ee sa s0 s` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule (REWRITE_RULE [ETA_THM] exprBopSimPropsTheory.bop_value_scopes_dom) >> simp[]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    (drule (CONJUNCT2 compile_expr_grows) >> simp[]) >>
  gvs[] >>
  Cases_on `abi_static_size cenv.ce_struct_fields (TupleT tys) <= LENGTH bs /\
    LENGTH bs <= abi_size_bound cenv.ce_struct_fields (TupleT tys)`
  >- (Cases_on `evaluate_abi_decode (get_tenv cx) (TupleT tys) bs`
      >- suspend "success" >> suspend "reject") >>
  suspend "header"
QED

Resume abi_decode_normal_callback[success]:
  drule_all vyperTypeABITheory.evaluate_abi_decode_well_typed >>
  strip_tac >>
  `?vs. x = ArrayV (TupleV vs)` by
    (Cases_on `x` >> gvs[vyperTypingTheory.value_has_type_def] >>
     rename1 `value_has_type (TupleTV tvs) (ArrayV av)` >>
     Cases_on `av` >> gvs[vyperTypingTheory.value_has_type_def]) >> gvs[] >>
  `value_has_type (TupleTV tvs) (ArrayV (TupleV vs))` by first_assum ACCEPT_TAC >>
  drule (cj 1 valueEncodingTypingTheory.value_has_type_val_wf) >> strip_tac >>
  `LIST_REL value_has_type tvs vs` by
    fs[vyperTypingTheory.value_has_type_def,
       vyperTypeDefaultsTheory.values_have_types_LIST_REL] >>
  `LIST_REL val_wf tvs vs` by
    (irule LIST_REL_mono >> qexists_tac `value_has_type` >> simp[] >>
     metis_tac[cj 1 valueEncodingTypingTheory.value_has_type_val_wf]) >>
  `evaluate_type_builtin cx (AbiDecode F) (TupleT tys) [expr_type e] [BytesV bs] =
     INL (ArrayV (TupleV vs))` by
    (irule abiDecodeUnwrapCaseTheory.abi_decode_source_wrapping_success >>
     simp[needs_external_call_wrap_def]) >>
  `SUM (MAP (type_memory_bytes cenv) tys) =
    SUM (MAP (type_memory_bytes cenv) tys)` by simp[] >>
  qpat_assum `expr_type e = _`
    (fn th => drule_all (REWRITE_RULE [th] abi_decode_operand_success_posts)) >>
  disch_then (qspecl_then [`PG`, `cx_dead H cx`] strip_assume_tac) >>
  `vv_post H ctx func cenv cx
     (TypeBuiltin (TupleT tys) (AbiDecode b) (TupleT tys) [e])
     es sa sb s0 ee (Value (ArrayV (TupleV vs)))
     (LocatedValue (TupleT tys) (mk_ptr (Var dst) LocMemory)) v /\
   ptr_vv_ok cx (TupleT tys) (Value (ArrayV (TupleV vs)))
     (LocatedValue (TupleT tys) (mk_ptr (Var dst) LocMemory)) ee HG tf v /\
   ptr_buf_ok cenv (TypeBuiltin (TupleT tys) (AbiDecode b) (TupleT tys) [e]) (Var dst) HG v` by
    (`~expr_has_effect e ==> pure_frame cenv func es sa s0 v` by
       (strip_tac >>
        qpat_x_assum `pure_frame _ _ _ _ _ _ ==> pure_frame _ _ _ _ _ _` irule >>
        metis_tac[expr_post_pure_frame]) >>
     irule abi_decode_tuple_result_posts >>
     simp[expr_type_def, lowered_value_type_def] >>
     qexistsl_tac [`sh.cs_next_id`, `tvs`] >> simp[] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `local_ptrs_rel func cenv es.scopes s0` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `!z. not_fresh_at sa z ==> not_fresh_at sm z` by
    (simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  drule_all hash_expr_post_ghost_kept_compose >> strip_tac >>
  `evaluate_type_builtin cx (AbiDecode b) (TupleT tys) [expr_type e] [BytesV bs] =
     INL (ArrayV (TupleV vs))` by
    (irule abiDecodeUnwrapCaseTheory.abi_decode_source_wrapping_success >>
     simp[needs_external_call_wrap_def]) >>
  disj1_tac >>
  qexists_tac `REPLICATE (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb))) F` >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (Value (ArrayV (TupleV vs)))`, `ee`, `HG`, `tf`, `OK v`] >>
  `ee with gas_obs := [] = ee` by
    simp[evaluation_state_component_equality] >>
  qpat_assum `expr_type e = _` (fn th => fs[th]) >>
  simp[expr_type_def, vyperStateTheory.lift_sum_def,
    vyperStateTheory.bind_def, vyperStateTheory.return_def] >>
  simp[mk_ptr_def]
QED
Resume abi_decode_normal_callback[reject]:
  `SUM (MAP (type_memory_bytes cenv) tys) = SUM (MAP (type_memory_bytes cenv) tys)` by simp[] >>
  `LENGTH bs <= vyper_abi_size_bound (get_tenv cx) (TupleT tys)` by
    metis_tac[abi_decode_flat_source_bound] >>
  gvs[] >>
  `SUM (MAP (type_memory_bytes cenv) tys) = SUM (MAP (type_memory_bytes cenv) tys)` by simp[] >>
  qpat_assum `expr_type e = _`
    (fn th => drule_all (REWRITE_RULE [th] abiDecodePtrOutcomeTheory.abi_decode_operand_actual_reject_or_exempt)) >>
  disch_then (qspecl_then [`PG`, `cx_dead H cx`] mp_tac) >>
  `evaluate_type_builtin cx (AbiDecode b) (TupleT tys) [expr_type e] [BytesV bs] =
    INR (RuntimeError y)` by
    (irule abiWrappedDecodePropsTheory.evaluate_type_builtin_abi_decode_unwrapped_error >>
     simp[needs_external_call_wrap_def]) >>
  disch_then DISJ_CASES_TAC
  >- (disj2_tac >> gvs[] >> qexists_tac `TupleT tys` >>
      conj_tac >- metis_tac[abi_decode_body_target_occurs] >>
      `is_dynamic (vyper_to_abi_type (get_tenv cx) (TupleT tys))` by
        (qpat_x_assum `EXISTS _ tys` mp_tac >>
         simp[vyper_to_abi_type_def, contractABITheory.is_dynamic_def,
           contractABITheory.any_dynamic_EXISTS,
           abiDecoderMembersTheory.vyper_to_abi_types_MAP, EXISTS_MAP,
           EVERY_NOT_EXISTS, combinTheory.o_DEF]) >>
      metis_tac[expr_body_pre_def]) >>
  disj1_tac >>
  irule_at Any type_builtin_runtime_error_abort_summary >>
  metis_tac[]
QED
Resume abi_decode_normal_callback[header]:
  `abi_static_size cenv.ce_struct_fields (TupleT tys) <=
     abi_size_bound cenv.ce_struct_fields (TupleT tys)` by
    (POP_ASSUM_LIST (K all_tac) >>
     simp[Once abi_static_size_def, Once abi_size_bound_def,
       abi_embedded_static_size_def] >>
     Induct_on `tys` >> simp[] >> gen_tac >> rpt IF_CASES_TAC >> simp[] >> decide_tac) >>
  `abi_static_size cenv.ce_struct_fields (TupleT tys) < dimword (:256)` by decide_tac >>
  `?v K tk n j. gas_path_ptr (cx_dead H cx) 0 ctx func PG G tn s n K tk
     (Abort Revert_abort (v with vs_inst_idx := j))` by
    (irule abiDecodePtrOutcomeTheory.abi_decode_operand_header_reject >>
     asm_rewrite_tac[] >>
     goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `abi_builtin_decode_header _ _ _ _ = _`)) >>
     simp[] >> decide_tac) >>
  `~vyper_valid_enc (get_tenv cx) (TupleT tys) bs` by
    (strip_tac >>
     `abi_size_bound cenv.ce_struct_fields (TupleT tys) =
      vyper_abi_size_bound (get_tenv cx) (TupleT tys)` by
       metis_tac[abi_decode_flat_source_bound] >>
     `EVERY (abiCallerAbiShape$abi_caller_abi_shape cenv.ce_struct_fields (get_tenv cx)) tys` by
       (qpat_x_assum `EVERY supported_scalar_type tys` mp_tac >>
        simp[EVERY_MEM] >> rpt strip_tac >>
        rename1 `abiCallerAbiShape$abi_caller_abi_shape _ _ elem` >>
        `supported_scalar_type elem` by metis_tac[] >>
        qpat_x_assum `supported_scalar_type elem` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        Cases_on `elem` >> gvs[supportedTypesTheory.supported_scalar_type_def,
          supportedTypesTheory.supported_word_type_def,
          supportedTypesTheory.supported_string_type_def, abiCallerAbiShapeTheory.abi_caller_abi_shape_base]) >>
     drule abiCallerBuiltinInputTheory.abi_caller_members_head >> strip_tac >>
     `vyper_decode_valid_enc (contractABI$Tuple (vyper_to_abi_types (get_tenv cx) tys)) bs` by
       fs[vyper_valid_enc_def, Once vyper_to_abi_type_def] >>
     drule abiValidMembersTheory.abi_valid_tuple_view >> strip_tac >>
     fs[vyperABIValidTheory.vyper_valid_enc_window,
        Once abi_static_size_def, abi_decode_flat_source_bound]) >>
  `evaluate_type_builtin cx (AbiDecode b) (TupleT tys) [expr_type e] [BytesV bs] =
    INR (RuntimeError "abi_decode invalid")` by
    (irule abiWrappedDecodePropsTheory.evaluate_type_builtin_abi_decode_unwrapped_error >>
     simp[needs_external_call_wrap_def, evaluate_abi_decode_def]) >>
  disj1_tac >> irule_at Any type_builtin_runtime_error_abort_summary >> metis_tac[]
QED
Finalise abi_decode_normal_callback

Theorem abi_decode_unary_vv_sim_ptr:
  body_inv decls ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin ann (AbiDecode b) typ [e]) es /\
  expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty (TypeBuiltin ann (AbiDecode b) typ [e]) es
Proof
  strip_tac >> drule_all abi_decode_body_target_metadata >> strip_tac >> gvs[] >>
  drule abi_decode_body_pre_shape >> strip_tac >> gvs[] >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_bytestring >> fs[is_bytestring_type_def]) >>
  irule type_builtin_unary_vv_sim_ptr_origin >>
  asm_rewrite_tac[] >> simp[type_builtin_args_length_ok_def] >>
  reverse conj_tac >- (qexists_tac `env` >> simp[]) >>
  qexists_tac `\x sm. as_ptr_val (TupleT tys) LocMemory
    (lower_abi_decode x
      (type_to_abi_dec_info cenv.ce_struct_fields cenv (TupleT tys))
      (abi_static_size cenv.ce_struct_fields (TupleT tys))
      (abi_size_bound cenv.ce_struct_fields (TupleT tys))
      (type_memory_bytes cenv (TupleT tys)) sm)` >>
  reverse conj_tac
  >- (conj_tac
      >- (rpt gen_tac >>
          simp[compile_abi_decode_stages, needs_external_call_wrap_def] >>
          pairarg_tac >> simp[] >> strip_tac >>
          goal_assum (drule_at Any) >> simp[]) >>
      gen_tac >> rewrite_tac[cs_appends_def] >> rpt gen_tac >>
      Cases_on `lower_abi_decode x
        (type_to_abi_dec_info cenv.ce_struct_fields cenv (TupleT tys))
        (abi_static_size cenv.ce_struct_fields (TupleT tys))
        (abi_size_bound cenv.ce_struct_fields (TupleT tys))
        (type_memory_bytes cenv (TupleT tys)) st` >>
      simp[as_ptr_val_def] >> strip_tac >> gvs[] >>
      mp_tac (GEN_ALL cs_appends_lower_abi_decode) >>
      simp[cs_appends_def] >> disch_then drule >> simp[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_assum `expr_type e = _`
    (fn th => drule_all (REWRITE_RULE [th] abi_decode_normal_callback)) >> simp[]
QED

Theorem abi_decode_unary_sim_ptr:
  body_inv decls ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin ann (AbiDecode b) typ [e]) es /\
  expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es ==>
  expr_sim_ptr d ctx PG func cenv cx ty (TypeBuiltin ann (AbiDecode b) typ [e]) es
Proof
  strip_tac >> irule expr_sim_ptr_of_vv >>
  conj_tac >- metis_tac[] >>
  irule abi_decode_unary_vv_sim_ptr >> metis_tac[]
QED
