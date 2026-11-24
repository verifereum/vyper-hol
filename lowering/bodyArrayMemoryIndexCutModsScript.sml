(* Common linked memory-index cut projection for non-reading array subscripts. *)
Theory bodyArrayMemoryIndexCutMods
Ancestors
  bodyArrayNoCopyCutsMods bodyArrayNoCopySourceMods bodySubscriptArrayRouteDefsMods
  bodyFullPostsMods bodySimStmtFacts bodyAssignNameLinkedSetup
  exprSimHypsDefs exprBodyPreProps exprOperandVar exprSimProps exprSimWordArgs wordArgsPtr
  exprSimSubscriptArrayOrigin exprReasonOperand exprBopSimProps exprSimArith
  arithmeticProps valueEncoding loweringPosts bodyPtrDefs compileEnv context ptrDiscipline
  vyperEvalExprPreservesScopesDom vyperTypeEvalCaseProofs vyperTypeConstantFold
  vyperTypeValues vyperTypeExprSoundness vyperTypeSystem vyperTyping vyperValue
  vyperInterpreter vyperState vyperAST vyperStorageFootprint words integer finite_map pair

Theorem memory_index_word[local]:
  is_int_type (expr_type idx) /\
  evaluate_type (get_tenv cx) (expr_type idx) = SOME tv /\ value_has_type tv key /\
  expr_post H ctx func cenv cx idx mid sm st2 s fin key iop it ==>
  ?i iw. key = IntV i /\ eval_operand iop it = SOME iw /\
    i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw))
Proof
  strip_tac >> qspec_then `expr_type idx` mp_tac math_val_i2w >>
  Cases_on `expr_type idx` >> gvs[is_int_type_def] >>
  rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
  gvs[is_int_type_def, evaluate_type_def, AllCaseEqs(), well_formed_type_def] >>
  Cases_on `key` >>
  gvs[value_has_type_def, expr_post_def, expr_val_rel_def, is_word_type_def,
      evaluate_type_def, typed_val_to_w256_def, val_to_w256_def, AllCaseEqs(),
      math_val_def, is_signed_type_def, type_bits_def, within_int_bound_def] >>
  disch_then (qspec_then `i` mp_tac) >> simp[]
QED

Theorem memory_index_types[local]:
  expr_body_pre_mods mods cenv cx env (Subscript ann obj idx) es /\
  well_typed_expr env obj /\ expr_type obj = ArrayT et bd /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type obj)) ==>
  ann = et /\ is_int_type (expr_type idx) /\ is_word_type (expr_type idx) /\
  ?etv. evaluate_type (get_tenv cx) et = SOME etv /\
    evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd)
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_well_typed >>
  `ann = et /\ is_int_type (expr_type idx)` by
    (drule_all constant_subscript_type_ok >> simp[subscript_type_ok_def]) >>
  `is_word_type (expr_type idx)` by
    (qpat_assum `is_int_type (expr_type idx)` mp_tac >>
     Cases_on `expr_type idx` >> gvs[is_int_type_def] >>
     rename1 `is_word_type (BaseT bt)` >> Cases_on `bt` >>
     gvs[is_int_type_def, is_word_type_def]) >>
  qpat_x_assum `IS_SOME (evaluate_type _ _)` mp_tac >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  drule_then strip_assume_tac evaluate_type_ArrayT_cases >> simp[]
QED

Theorem memory_index_typed_result[local]:
  expr_body_pre_mods mods cenv cx env idx start /\
  bind (eval_expr cx idx) (read_result cx) start = (INL key,fin) ==>
  ?tv. evaluate_type (get_tenv cx) (expr_type idx) = SOME tv /\ value_has_type tv key
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  drule_all_then strip_assume_tac (REWRITE_RULE [ETA_AX] expr_body_pre_eval_mods) >>
  fs[value_runtime_typed_def] >> qexists `tv` >>
  qpat_assum `env.type_defs = get_tenv cx` (SUBST1_TAC o SYM) >> simp[]
QED

Theorem memory_index_base_view[local]:
  vv_post_mods H ctx func cenv cx obj es sa sm s0 mid
    (PlaceR (MemoryPlace id path)) (LocatedValue (ArrayT et bd) p) s ==>
  wb_frame cenv es mid sa s0 s /\
  (~expr_has_effect obj ==> pure_frame cenv func es sa s0 s) /\
  ?w. eval_operand p.ptr_operand s = SOME w
Proof
  simp[vv_post_mods_def, wb_frame_def, vv_place_ptr_mods_def, vv_place_ptr_def] >>
  strip_tac >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  goal_assum (drule_at (Pat `eval_operand _ _ = _`))
QED

Theorem array_memory_index_cut_mods:
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et bd /\
  ~subscript_reads_base cx obj idx /\
  expr_body_pre_mods mods cenv cx env obj (es with gas_obs := gs1) /\
  expr_body_pre_mods mods cenv cx env idx (mid with gas_obs := gs2) /\
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty obj idx et bd st0
    (es,s0,G0,tn0) (sa,sm,st2,sb,bvv,iop,dst,loc)
    (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
    (gs1,mid,raw,s,G1,tn1) (gs2,fin,key,it,Gi,tni) /\
  raw = PlaceR (MemoryPlace id path) /\
  bvv = LocatedValue (ArrayT et bd) p /\
  p.ptr_location = LocMemory ==>
  ?etv tv i iw w.
    ann = et /\
    evaluate_type (get_tenv cx) et = SOME etv /\
    evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
    evaluate_type (get_tenv cx) (expr_type idx) = SOME tv /\
    key = IntV i /\ value_has_type tv key /\
    type_memory_bytes cenv et = type_memory_size etv /\
    eval_operand iop it = SOME iw /\
    i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\
    is_word_type (expr_type idx) /\
    op_taint tni iop = {} /\ op_prov Gi iop = NONE /\
    eval_operand p.ptr_operand s = SOME w /\
    eval_operand p.ptr_operand it = SOME w /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x /\ not_fresh_at st2 x) /\
    (!l. p.ptr_operand <> Label l) /\
    (!x. iop = Var x ==> not_fresh_at st2 x) /\
    (!l. iop <> Label l) /\
    wb_frame cenv es fin sa s0 it /\
    (~expr_has_effect (Subscript ann obj idx) ==> pure_frame cenv func es sa s0 it) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 Gi tni /\
    (!H. valid_horizon cx st0 H fin.storage_trace ==>
       expr_post H ctx func cenv cx idx mid sm st2 s fin key iop it /\
       stmt_state_rel H ctx func cenv cx fin it /\
       immutable_frame_mods func cenv cx fin it /\
       storage_well_formed_on cx fin (FST H) /\
       ghost_inv_at_mods (DF H) lo d cenv cx fin Gi tni it)
Proof
  strip_tac >> drule_all_then strip_assume_tac array_nocopy_base_inputs_mods >>
  qhdtm_x_assum `linked_subscript_array_context_mods`
    (strip_assume_tac o REWRITE_RULE [linked_subscript_array_context_mods_def]) >>
  drule_all_then strip_assume_tac memory_index_types >>
  `type_memory_bytes cenv et = type_memory_size etv` by
    (irule assign_name_memory_bytes_mods >>
     goal_assum (drule_at (Pat `evaluate_type _ _ = _`)) >>
     goal_assum (drule_at (Pat `expr_sim_inv_mods _ _ _ _ _`)) >> simp[]) >>
  qhdtm_assum `array_nocopy_cut_mods`
    (strip_assume_tac o REWRITE_RULE [array_nocopy_cut_mods_def]) >>
  qabbrev_tac `H0 = storage_trace_horizon fin.storage_trace` >>
  `valid_horizon cx st0 H0 fin.storage_trace` by
    fs[Abbr `H0`, storage_trace_domain_def] >>
  drule_all_then strip_assume_tac array_nocopy_cut_posts_mods >>
  qpat_x_assum `raw = PlaceR _` SUBST_ALL_TAC >>
  qpat_x_assum `bvv = LocatedValue _ _` SUBST_ALL_TAC >>
  drule_then strip_assume_tac memory_index_base_view >>
  qpat_assum `expr_post_mods H0 _ _ _ _ idx _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  `expr_body_pre_mods mods cenv cx env idx (mid with gas_obs := gs2)` by simp[] >>
  drule_all_then strip_assume_tac memory_index_typed_result >>
  drule_all_then strip_assume_tac memory_index_word >>
  `op_taint tni iop = {} /\ op_prov Gi iop = NONE` by
    ((qpat_assum `ptr_val_ok _ _ _ _ _ _ _` mp_tac >>
     simp[ptr_val_ok_def, post_value_type_word] >> (gvs[ptr_val_ok_def, post_value_type_word]))) >>
  suspend "operands"
QED

Resume array_memory_index_cut_mods[operands]:
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    (qpat_assum `compile_expr cenv ty obj sa = _`
      (mp_then Any mp_tac (cj 1 compiler_compile_var)) >> simp[vv_operand_def]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at st2 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `sm` >> simp[]) >>
  `!l. p.ptr_operand <> Label l` by
    (irule compile_array_pointer_not_label >> simp[] >>
     qpat_assum `compile_expr cenv ty obj sa = _` (irule_at Any) >>
     goal_assum (drule_at (Pat `expr_type _ = ArrayT _ _`)) >> qexists `env` >>
     qpat_assum `expr_sim_inv_mods _ _ _ _ es`
       (mp_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >> simp[]) >>
  `!x. iop = Var x ==> not_fresh_at st2 x` by
    (qpat_assum `lower_value compile_expr cenv ty idx sm = _`
      (mp_then Any mp_tac compile_lower_value_var) >> simp[]) >>
  `!l. iop <> Label l` by
    (irule lower_compile_expr_not_label >>
     qpat_assum `lower_value compile_expr cenv ty idx sm = _` (irule_at Any) >>
     qexists `env` >>
     qpat_assum `expr_body_pre_mods _ _ _ _ idx _`
       (mp_then Any strip_assume_tac expr_body_pre_mods_well_typed) >>
     qpat_assum `expr_sim_inv_mods _ _ _ _ es`
       (mp_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >> simp[]) >>
  drule_then assume_tac expr_post_frame >>
  `eval_operand p.ptr_operand it = SOME w` by
    (irule eval_operand_frame >> simp[] >> qexistsl [`sm`,`s`] >> fs[wb_frame_def]) >>
  suspend "frames"
QED

Resume array_memory_index_cut_mods[frames]:
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `eval_expr cx obj _ = _`
      (mp_then Any mp_tac eval_expr_preserves_scopes_dom) >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> valid_horizon _ _ H mid.storage_trace /\ _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  `wb_frame cenv es fin sa s0 it` by
    (drule_all wb_frame_trans >> simp[]) >>
  `~expr_has_effect (Subscript ann obj idx) ==> pure_frame cenv func es sa s0 it` by
    (simp[expr_has_effect_thm] >> strip_tac >>
     `pure_frame cenv func es sa s0 s` by simp[] >>
     `pure_frame cenv func mid sm s it` by (drule_all expr_post_pure_frame >> simp[]) >>
     irule pure_frame_trans >> simp[] >> qexistsl [`mid`,`sm`,`s`] >> fs[wb_frame_def]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gi tni` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx es s0`
      (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule ghost_kept_at_wb_trans) >>
     simp[] >> qexistsl [`G1`,`mid`,`mid`,`s`,`sm`,`tn1`] >> simp[]) >>
  qexistsl [`etv`,`tv`,`i`,`iw`,`w`] >> simp[] >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  fs[expr_post_mods_def] >>
  qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  asm_rewrite_tac[]
QED

Finalise array_memory_index_cut_mods
