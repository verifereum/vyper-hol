(* Operand facts for a storage-array slot after the non-reading base and key. *)
Theory bodyArraySlotReachedOperandsMods
Ancestors
  bodyArrayNoCopySourceMods bodyArrayNoCopyCutsMods bodySubscriptArrayRouteDefsMods
  bodyArraySlotOperandFrameMods bodyFullPostsMods bodyPtrDefs bodySimStmtFacts
  exprSimSubscriptArrayOrigin exprSimWordArgs exprBodyPreProps exprSimHypsDefs
  exprOperandVar exprSimArith exprLowering loweringPosts placeStoreSlots
  vyperTypeConstantFold vyperTypeEvalCaseProofs vyperTypeExprResult
  vyperTypeExprSoundness vyperTypeSystem vyperAST vyperValue vyperTyping
  valueEncoding arithmeticProps compileEnv context venomState
  vyperStorageFootprint ptrDiscipline words integer finite_map

Theorem slot_key_word[local]:
  is_int_type (expr_type idx) /\
  evaluate_type (get_tenv cx) (expr_type idx) = SOME tv /\ value_has_type tv key /\
  expr_post_mods H ctx func cenv cx idx mid sm st2 s fin key iop it ==>
  ?i iw. key = IntV i /\ eval_operand iop it = SOME iw /\
    i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw))
Proof
  strip_tac >>
  Cases_on `expr_type idx` >> gvs[is_int_type_def] >>
  rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
  gvs[is_int_type_def, evaluate_type_def, value_has_type_def, well_formed_type_def] >>
  Cases_on `key` >> gvs[value_has_type_def] >>
  fs[expr_post_mods_def, expr_post_def, expr_val_rel_def, evaluate_type_def,
     AllCaseEqs(), is_word_type_def, typed_val_to_w256_def, val_to_w256_def] >>
  mp_tac math_val_i2w >>
  disch_then (qspec_then `expr_type idx` (qspec_then `i` mp_tac)) >>
  gvs[math_val_def, is_signed_type_def, type_bits_def, within_int_bound_def]
QED

Theorem slot_key_runtime_type[local]:
  expr_body_pre_mods mods cenv cx env idx es /\
  bind (eval_expr cx idx) (read_result cx) es = (INL key,fin) ==>
  ?tv. evaluate_type (get_tenv cx) (expr_type idx) = SOME tv /\ value_has_type tv key
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  drule_all_then strip_assume_tac (REWRITE_RULE [ETA_AX] expr_body_pre_eval_mods) >>
  fs[value_runtime_typed_def] >> qexists `tv` >>
  qpat_assum `env.type_defs = get_tenv cx` (SUBST1_TAC o SYM) >> simp[]
QED

Theorem slot_key_scalar[local]:
  is_int_type (expr_type idx) /\ ptr_val_ok cx (post_value_type cenv idx) key iop Gi tni it ==>
  op_taint tni iop = {} /\ op_prov Gi iop = NONE
Proof
  `is_int_type (expr_type idx) ==> is_word_type (expr_type idx)` by
    (Cases_on `expr_type idx` >> simp[is_int_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_int_type_def, is_word_type_def]) >>
  strip_tac >> fs[ptr_val_ok_def]
QED

Theorem slot_operand_clean[local]:
  ghost_kept_at lo cenv mid sm G1 tn1 s Gi tni /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ op_taint tn1 op = {} ==>
  op_taint tni op = {}
Proof
  Cases_on `op` >> simp[op_taint_def, ghost_kept_at_def] >> metis_tac[]
QED

Theorem array_slot_reached_operands_mods:
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et bd /\
  ~subscript_reads_base cx obj idx /\
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty obj idx et bd st0
    (es,s0,G0,tn0) (sa,sm,st2,sb,bvv,iop,dst,loc)
    (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
    (gs1,mid,raw,s,G1,tn1) (gs2,fin,key,it,Gi,tni) /\
  raw = PlaceR (StoragePlace tr slot vt) ==>
  loc = slot_loc tr /\
  ?p i iw. bvv = LocatedValue (ArrayT et bd) p /\
    p.ptr_location = slot_loc tr /\
    eval_operand (vv_operand bvv) it = SOME slot /\
    op_taint tni (vv_operand bvv) = {} /\
    (!x. vv_operand bvv = Var x ==> not_fresh_at sm x) /\
    key = IntV i /\
    eval_operand iop it = SOME iw /\
    i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\
    op_taint tni iop = {} /\
    op_prov Gi iop = NONE /\
    (!x. iop = Var x ==> not_fresh_at st2 x)
Proof
  strip_tac >>
  drule_all_then strip_assume_tac array_nocopy_base_inputs_mods >>
  qhdtm_assum `linked_subscript_array_context_mods`
    (strip_assume_tac o REWRITE_RULE [linked_subscript_array_context_mods_def]) >>
  qhdtm_assum `array_nocopy_cut_mods`
    (strip_assume_tac o REWRITE_RULE [array_nocopy_cut_mods_def]) >>
  `is_int_type (expr_type idx)` by
    (drule_then assume_tac expr_body_pre_mods_well_typed >>
     drule_all constant_subscript_type_ok >> simp[subscript_type_ok_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  drule_all_then strip_assume_tac array_nocopy_cut_posts_mods >>
  drule_all_then strip_assume_tac array_nocopy_index_inputs_mods >>
  `expr_body_pre_mods mods cenv cx env idx (mid with gas_obs := gs2)` by simp[] >>
  drule_all_then strip_assume_tac slot_key_runtime_type >>
  drule_all_then strip_assume_tac slot_key_word >>
  drule_all_then strip_assume_tac slot_key_scalar >>
  `!x. iop = Var x ==> not_fresh_at st2 x` by
    (qpat_assum `lower_value compile_expr cenv ty idx sm = _`
       (mp_then Any mp_tac compile_lower_value_var) >> simp[]) >>
  `wb_frame cenv mid fin sm s it` by
    (qhdtm_assum `expr_post_mods` (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
     drule_then ACCEPT_TAC expr_post_frame) >>
  qhdtm_assum `vv_post_mods`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  qhdtm_assum `vv_place_ptr_mods`
    (strip_assume_tac o REWRITE_RULE [vv_place_ptr_mods_def]) >>
  Cases_on `bvv`
  >- gvs[vv_holds_mods_def, vv_holds_def, vv_at_def, vv_place_ptr_mods_def,
         vv_place_ptr_def, vv_location_def, is_word_type_def] >>
  gvs[vv_holds_mods_def, vv_holds_def, vv_at_def, vv_place_ptr_mods_def,
      vv_place_ptr_def, vv_location_def, is_word_type_def, is_bytestring_type_def,
      vv_operand_def] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    (qpat_assum `compile_expr cenv ty obj sa = _`
       (mp_then Any mp_tac (cj 1 compiler_compile_var)) >> simp[vv_operand_def]) >>
  `eval_operand p.ptr_operand it = SOME slot` by
    (qpat_assum `compile_expr cenv ty obj sa = (LocatedValue t p,sm)`
       (mp_then (Pat `compile_expr _ _ _ _ = _`) mp_tac array_slot_operand_frame_mods) >>
     simp[] >>
     disch_then irule >> conj_tac
     >- (qexists `env` >> fs[expr_sim_inv_mods_def]) >>
     qexistsl [`fin`,`mid`,`s`] >> simp[]) >>
  `op_taint tn1 p.ptr_operand = {}` by fs[ptr_vv_ok_def] >>
  drule_all_then assume_tac slot_operand_clean >>
  `t = ArrayT et bd` by (Cases_on `tr` >> fs[slot_loc_def]) >>
  simp[]
QED
