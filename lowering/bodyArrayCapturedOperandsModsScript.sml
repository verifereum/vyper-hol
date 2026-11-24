(* Operand facts at the base and key cuts of a captured fixed Pop. *)
Theory bodyArrayCapturedOperandsMods
Ancestors
  bodyArrayNoCopySourceMods bodyArrayNoCopyCutsMods bodySubscriptArrayRouteDefsMods
  bodyAssignNameLinkedSetup bodySimStmtFacts bodyFullPostsMods bodyPtrDefs
  exprSimSubscriptArrayOrigin exprSimSubscriptArraySource exprBodyPreProps
  exprSimHypsDefs exprOperandVar exprSimArith exprLowering allocLimits
  loweringPosts placeStoreSlots vyperTypeConstantFold vyperTypeEvalCaseProofs
  vyperTypeExprResult vyperTypeExprSoundness vyperTypeSystem vyperAST vyperValue vyperTyping
  vyperStorageFootprint valueEncoding arithmeticProps compileEnv context
  venomState ptrDiscipline words integer finite_map

Theorem captured_pop_lowered_type[local]:
  base_from_pop obj ==> lowered_value_type cenv obj = expr_type obj
Proof
  Cases_on `obj` >> simp[base_from_pop_def, lowered_value_type_def]
QED

Theorem captured_base_located[local]:
  vv_post_mods H ctx func cenv cx obj es sa sm s0 mid
    (PlaceR (MemoryPlace id path)) bvv s /\
  post_value_type cenv obj = ArrayT et bd ==>
  ?t p. bvv = LocatedValue t p /\ p.ptr_location = LocMemory
Proof
  Cases_on `bvv` >> simp[vv_post_mods_def] >> strip_tac
  >- gvs[vv_at_def, is_word_type_def] >>
  gvs[vv_place_ptr_mods_def, vv_place_ptr_def]
QED

Theorem captured_base_operand[local]:
  compile_expr cenv ty obj sa = (LocatedValue t p,sm) /\
  local_ptrs_reserved cenv sa /\ expr_type obj = ArrayT et bd /\
  p.ptr_location = LocMemory /\ expr_body_pre_mods mods cenv cx env obj es ==>
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  (!l. p.ptr_operand <> Label l)
Proof
  strip_tac >> conj_tac
  >- (drule (cj 1 compiler_compile_var) >> simp[vv_operand_def]) >>
  irule compile_array_pointer_not_label >> simp[] >>
  goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  simp[] >> qexists `env` >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  fs[expr_sim_inv_mods_def]
QED

Theorem captured_key_word[local]:
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

Theorem captured_key_runtime_type[local]:
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

Theorem captured_key_scalar[local]:
  is_int_type (expr_type idx) /\ ptr_val_ok cx (post_value_type cenv idx) key iop Gi tni it ==>
  op_taint tni iop = {} /\ op_prov Gi iop = NONE
Proof
  `is_int_type (expr_type idx) ==> is_word_type (expr_type idx)` by
    (Cases_on `expr_type idx` >> simp[is_int_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_int_type_def, is_word_type_def]) >>
  strip_tac >> fs[ptr_val_ok_def]
QED

Theorem array_captured_operands_mods:
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et (Fixed n) /\
  ~subscript_reads_base cx obj idx /\
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty obj idx et (Fixed n) st0
    (es,s0,G0,tn0) (sa,sm,st2,sb,bvv,iop,dst,loc)
    (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
    (gs1,mid,raw,s,G1,tn1) (gs2,fin,key,it,Gi,tni) /\
  raw = PlaceR (MemoryPlace id path) /\ base_from_pop obj /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) ==>
  ann = et /\ post_value_type cenv obj = expr_type obj /\
  lowered_value_type cenv obj = expr_type obj /\ loc = LocMemory /\ n < dimword (:256) /\
  type_memory_bytes cenv et = type_memory_size etv /\
  type_memory_bytes cenv (ArrayT et (Fixed n)) = type_memory_size (ArrayTV etv (Fixed n)) /\
  ?t p i iw. bvv = LocatedValue t p /\ p.ptr_location = LocMemory /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\ (!l. p.ptr_operand <> Label l) /\
    key = IntV i /\ eval_operand iop it = SOME iw /\
    i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\
    op_taint tni iop = {} /\ op_prov Gi iop = NONE /\
    (!x. iop = Var x ==> not_fresh_at st2 x)
Proof
  strip_tac >>
  drule_all_then strip_assume_tac array_nocopy_base_inputs_mods >>
  drule_then assume_tac base_from_pop_not_array_slot_base >>
  qhdtm_assum `linked_subscript_array_context_mods`
    (strip_assume_tac o REWRITE_RULE [linked_subscript_array_context_mods_def]) >>
  qhdtm_assum `array_nocopy_cut_mods`
    (strip_assume_tac o REWRITE_RULE [array_nocopy_cut_mods_def]) >>
  `ann = et /\ is_int_type (expr_type idx)` by
    (drule_then assume_tac expr_body_pre_mods_well_typed >>
     drule_all constant_subscript_type_ok >> simp[subscript_type_ok_def]) >>
  `post_value_type cenv obj = ArrayT et (Fixed n)` by simp[] >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  drule_all_then strip_assume_tac array_nocopy_cut_posts_mods >>
  drule_all_then strip_assume_tac array_nocopy_index_inputs_mods >>
  `expr_body_pre_mods mods cenv cx env idx (mid with gas_obs := gs2)` by simp[] >>
  `expr_body_pre_mods mods cenv cx env obj es` by simp[] >>
  qpat_x_assum `raw = PlaceR _` SUBST_ALL_TAC >>
  drule_all_then strip_assume_tac captured_base_located >>
  drule_all_then strip_assume_tac captured_key_runtime_type >>
  drule_all_then strip_assume_tac captured_key_word >>
  drule_all_then strip_assume_tac captured_key_scalar >>
  `!x. iop = Var x ==> not_fresh_at st2 x` by
    (qpat_assum `lower_value compile_expr cenv ty idx sm = _`
       (mp_then Any mp_tac compile_lower_value_var) >> simp[]) >>
  drule_then assume_tac captured_pop_lowered_type >>
  drule_then assume_tac store_slots_fixed_count_bound >>
  `type_memory_bytes cenv et = type_memory_size etv` by
    (irule assign_name_memory_bytes_mods >> simp[] >>
     goal_assum (drule_at (Pat `expr_sim_inv_mods _ _ _ _ _`)) >> simp[]) >>
  `type_memory_bytes cenv (ArrayT et (Fixed n)) = type_memory_size (ArrayTV etv (Fixed n))` by
    (irule assign_name_memory_bytes_mods >> simp[] >>
     goal_assum (drule_at (Pat `expr_sim_inv_mods _ _ _ _ _`)) >> simp[]) >>
  gvs[vv_location_def] >> drule_all_then strip_assume_tac captured_base_operand >> simp[]
QED
