Theory bodyPtrPopTargetSimArraySuffix
Ancestors
  bodyPtrPopTargetSimFixedMemory bodyPtrPopTargetSimFixedSlot
  bodyPtrPopTargetSimDynamicMemory bodyPtrPopTargetSimDynamicSlot
  bodyPtrPopTargetSimArrayGas bodyPtrPopTargetSimIndexSource
  bodyPtrPopTargetSimIndexFrame bodyPtrPopTargetSimCoverage
  bodyPtrPopTargetSimPost exprSimHypsDefs exprSimSource exprSimProps
  exprLoweringProps exprLowering emitHelperProps stmtLoweringMono
  targetPlaceSim targetPlaceSimDefs loweringPosts bodyPtrDefs
  bodyPtrPopTargetDefs vyperInterpreter vyperState vyperTypeSystem
  compileEnv loweringStateRelDefs ptrDiscipline freshWrites fragExec pair list
  vyperEvalExprPreservesScopesDom wordOperandsPtr stmtFragPtr
  bodySimStmtCases vyperTypeExprSoundness vyperTypeInvariants vyperValue
  exprSimHyps vyperTyping assignTuplePtrBodyReady valueEncoding
  exprWordOperand exprSafeOperand exprSimCopy exprSimArrayIndex
  bodyPtrPopTargetSimArrayCase stmtReasonLitFragMemory emitHelper rich_list context venomState
  targetPlaceLive vyperStorageLayoutSafety exprPtrUnwrapTypedSize
  bodyPtrPopTargetSimStorageHeader

Theorem target_array_normal_suffix_ptr:
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  type_place_target env bt = SOME (Type (ArrayT et bd)) /\
  well_typed_expr env e /\ is_int_type (expr_type e) /\
  (!id. target_root bt = NameTarget id ==>
    local_target_live cx id (SubscriptTarget bt e)) /\
  (!src id. target_root bt = TopLevelNameTarget (src,id) ==>
    EVERY pure_expr (target_indices (SubscriptTarget bt e))) /\
  compile_get_target_ptr compile_expr cenv bt sa = ((bop,loc,SOME (ValPT (ArrayT et bd))),sm) /\
  lower_value compile_expr cenv (expr_type e) e sm = (idx,sn) /\
  compile_array_subscript bop idx (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0)
    (word_scale (case loc of SOME l => l | NONE => LocMemory))
    (elem_size_in_location cenv (case loc of SOME l => l | NONE => LocMemory) et)
    (is_signed_type (expr_type e))
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
      (case loc of SOME l => l | NONE => LocMemory)) sn = (dst,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb /\
  stmt_state_rel ctx func cenv cx es s0 /\
  target_post ctx func cenv cx es sa sm s0 ee pv (Type (ArrayT et bd))
    (bop,loc,SOME (ValPT (ArrayT et bd))) t /\
  target_ptr_ok cenv pv (bop,loc,SOME (ValPT (ArrayT et bd))) G tn t /\
  ghost_inv d cenv cx ee G tn t /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
  ee = em with gas_obs := [] /\
  source_start = es with gas_obs := gs /\
  eval_base_place cx bt source_start = (INL pv,em) /\
  bind (eval_expr cx e) (read_result cx) em = (INL v,ef) /\
  expr_body_pre cenv cx env e em /\ expr_sim_inv cenv cx env em /\
  expr_sim_inv cenv cx env ef /\ ef.gas_obs = [] /\
  expr_post ctx func cenv cx e ee sm sn t ef v idx u /\
  ghost_inv d cenv cx ef H un u /\
  ptr_val_ok cx (post_value_type cenv e) v idx H un u /\
  ghost_kept cenv ee sm G tn t H un /\
  u.vs_current_bb = sn.cs_current_bb /\
  u.vs_inst_idx = LENGTH sn.cs_current_insts /\ ~u.vs_halted ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (extend_place cx pv (ValueSubscript v)) (ef,u,H,un)
    (\res ef' H' un' q. ?pv'. res = INL pv' /\
      target_post ctx func cenv cx es sa sb s0 ef' pv' (Type et)
        (dst,loc,SOME (ValPT et)) q /\
      q.vs_current_bb = sb.cs_current_bb /\
      q.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ef' H' un' q /\
      target_ptr_ok cenv pv' (dst,loc,SOME (ValPT et)) H' un' q /\
      ghost_kept cenv es sa G0 tn0 s0 H' un')
    (\res ef' gt r. expr_exit res r)
Proof
  strip_tac >> suspend "common"
QED

Resume target_array_normal_suffix_ptr[common]:
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule eval_base_place_preserves_scopes_dom >>
     simp[] >> gvs[]) >>
  gvs[] >>
  `wb_frame cenv es sa s0 u` by
    (drule target_post_index_frame >> simp[] >>
     disch_then irule >> fs[ci_mono_def] >> metis_tac[]) >>
  `ghost_kept cenv es sa G0 tn0 s0 H un` by
    (qpat_assum `ghost_kept cenv es sa _ _ _ _ _`
       (mp_then Any mp_tac wordOperandsPtrTheory.ghost_kept_trans) >>
     disch_then irule >> simp[] >>
     conj_tac
     >- (qexists_tac `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl_tac [`em with gas_obs := []`, `t`, `sm`] >>
     fs[target_post_wb_frame, ci_mono_def, stmt_state_rel_def, state_rel_def]) >>
  suspend "typed"
QED

Resume target_array_normal_suffix_ptr[typed]:
  `?itv. evaluate_type (get_tenv cx) (expr_type e) = SOME itv /\
         value_has_type itv v` by
    (fs[vyperStateTheory.bind_def] >>
     drule_all (SRULE [vyperStateTheory.bind_def] bodySimStmtCasesTheory.expr_body_pre_eval) >>
     disch_then (CONJUNCTS_THEN2 kall_tac (qspec_then `v` mp_tac)) >>
     simp[value_runtime_typed_def] >> rpt strip_tac >>
     `env.type_defs = get_tenv cx` by
       (qpat_x_assum `expr_sim_inv cenv cx env em` mp_tac >>
        simp[expr_sim_inv_def, env_consistent_def, env_context_consistent_def]) >>
     metis_tac[]) >>
  `?i. v = IntV i` by
    (Cases_on `expr_type e` >> fs[is_int_type_def] >>
     Cases_on `b` >> gvs[is_int_type_def, evaluate_type_def, AllCaseEqs(), value_has_type_def] >>
     Cases_on `v` >> fs[value_has_type_def]) >> gvs[] >>
  suspend "scalar"
QED

Resume target_array_normal_suffix_ptr[scalar]:
  `is_word_type (expr_type e)` by
    (Cases_on `expr_type e` >> fs[is_int_type_def] >>
     Cases_on `b` >> fs[is_int_type_def, is_word_type_def]) >>
  `op_prov H idx = NONE /\ op_taint un idx = {}` by
    fs[ptr_val_ok_def] >>
  `stmt_state_rel ctx func cenv cx ef u /\
   eval_operand idx u = SOME (val_to_w256 (IntV i))` by
    (fs[expr_post_def, expr_val_rel_def] >>
     Cases_on `itv` >> simp[typed_val_to_w256_def] >>
     Cases_on `b` >> simp[typed_val_to_w256_def]) >>
  `!id ty. FLOOKUP env.var_types id = SOME ty ==>
    well_formed_type env.type_defs ty` by
    (drule expr_body_pre_var_types_well_formed >> simp[]) >>
  `safe_operand sn idx` by (irule lower_value_word_safe_operand >> metis_tac[]) >>
  `copy_old_operand sn idx` by fs[safe_operand_def, copy_old_operand_def] >>
  `copy_old_operand sn bop` by
    (fs[target_post_def, copy_old_operand_def, ci_mono_def, not_fresh_at_def] >>
     metis_tac[]) >>
  `local_ptrs_reserved cenv sn` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  `sa.cs_next_var <= sn.cs_next_var /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x)` by
    (fs[ci_mono_def, not_fresh_at_def] >> metis_tac[]) >>
  `fn_has_code sn sb func` by
    (irule (cj 2 fn_has_code_split) >> conj_tac
     >- fs[ci_mono_def] >>
     qexists_tac `sa` >> fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  suspend "classify"
QED

Resume target_array_normal_suffix_ptr[classify]:
  `?b. eval_operand bop t = SOME b /\
    place_ptr_rel cenv cx t pv b loc (Type (ArrayT et bd))` by
    (fs[target_post_def] >> metis_tac[]) >>
  `(?id path. pv = PlaceR (MemoryPlace id path)) \/
   (?tr slot tv. pv = PlaceR (StoragePlace tr slot tv))` by
    (Cases_on `pv` >> fs[place_ptr_rel_def] >>
     Cases_on `p` >> fs[place_ptr_rel_def]) >>
  gvs[] >- suspend "memory" >> suspend "storage"
QED

Resume target_array_normal_suffix_ptr[memory]:
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  drule_all target_memory_index_frame_ptr >> simp[] >> strip_tac >>
  `place_readable cx em (PlaceR (MemoryPlace id path))` by
    (qhdtm_x_assum `target_post` mp_tac >>
     simp[Once target_post_def] >> strip_tac >>
     qpat_x_assum `place_readable _ _ _` mp_tac >>
     simp[place_readable_def, read_place_def, get_scopes_def] >>
     Cases_on `lookup_scopes id em.scopes` >>
     simp[vyperStateTheory.bind_def, return_def, raise_def, lift_sum_def,
       get_scopes_def, lift_option_type_def, AllCaseEqs()] >>
     Cases_on `read_memory_path x path` >> simp[return_def, raise_def]) >>
  drule_all (SRULE [target_root_def] target_index_local_source_ptr) >> simp[] >> strip_tac >>
  suspend "memory_typed"
QED

Resume target_array_normal_suffix_ptr[memory_typed]:
  qpat_x_assum `evaluate_type _ (ArrayT _ _) = SOME _` mp_tac >>
  simp[Once evaluate_type_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  Cases_on `bd` >> gvs[]
  >- suspend "memory_fixed"
  >> suspend "memory_dynamic"
QED

Resume target_array_normal_suffix_ptr[memory_fixed]:
  `?av. cv = ArrayV av` by (Cases_on `cv` >> fs[value_has_type_def]) >> gvs[] >>
  `loc = SOME LocMemory` by fs[place_ptr_rel_def] >> gvs[] >>
  `type_memory_bytes cenv et = type_memory_size tv'` by
    (irule expr_sim_inv_memory_size >> metis_tac[]) >>
  `evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV tv' (Fixed n))` by
    simp[evaluate_type_def] >>
  fs[elem_size_in_location_def, is_slot_addressed_def] >>
  `cs_extends sn sb` by fs[ci_mono_def] >>
  qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[NoAsms, compile_array_subscript_split, comp_bind_def,
       comp_return_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >> rename1 `array_bounds_check _ _ _ sn = (uu,sg)` >>
  Cases_on `uu` >>
  drule bodyPtrPopTargetSimArrayCaseTheory.target_array_guard_layout >> strip_tac >>
  drule bodyPtrPopTargetSimArrayCaseTheory.target_array_elem_layout >> strip_tac >>
  `sb.cs_current_bb = sn.cs_current_bb /\
   sb.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sb` by
    (fs[same_blocks_def] >>
     `sb.cs_current_insts = sn.cs_current_insts ++
       (emitted_insts sn sg ++ emitted_insts sg sb)` by fs[APPEND_ASSOC] >>
     metis_tac[emitted_insts_def, DROP_LENGTH_APPEND]) >>
  drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >> strip_tac >>
  suspend "memory_fixed_code"
QED

Resume target_array_normal_suffix_ptr[memory_fixed_code]:
  `lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sn sb) (DROP u.vs_inst_idx bb.bb_instructions)` by
    metis_tac[] >>
  `op_taint un bop = {}` by
    (Cases_on `bop` >> fs[target_ptr_ok_def, op_taint_def]) >>
  drule_all target_fixed_memory_array_continue_ptr >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  irule target_array_suffix_outcome_ptr >> simp[] >>
  qexists_tac `sn` >> simp[] >>
  `LENGTH sn.cs_current_insts + LENGTH (emitted_insts sn sb) =
   LENGTH sb.cs_current_insts` by metis_tac[LENGTH_APPEND] >>
  metis_tac[]
QED

Resume target_array_normal_suffix_ptr[memory_dynamic]:
  `evaluate_type (get_tenv cx) (ArrayT et (Dynamic n)) = SOME (ArrayTV tv' (Dynamic n))` by
    simp[evaluate_type_def] >>
  `?ty en. FLOOKUP env.var_types id = SOME ty /\
    lookup_scopes id em.scopes = SOME en /\
    evaluate_type (get_tenv cx) ty = SOME en.type` by
    (irule target_readable_local_type_ptr >> metis_tac[]) >>
  `!en. lookup_scopes id ef.scopes = SOME en ==>
    ISL (evaluate_subscripts en.type en.value path)` by
    (rpt strip_tac >> irule target_current_local_resolution_ptr >>
     fs[target_root_def] >> metis_tac[]) >>
  drule_all target_index_dynamic_header_ptr >> simp[] >> strip_tac >>
  suspend "memory_dynamic_header"
QED

Resume target_array_normal_suffix_ptr[memory_dynamic_header]:
  gvs[] >>
  `loc = SOME LocMemory` by fs[place_ptr_rel_def] >> gvs[] >>
  `type_memory_bytes cenv et = type_memory_size tv'` by
    (irule expr_sim_inv_memory_size >> metis_tac[]) >>
  gvs[] >> fs[elem_size_in_location_def, is_slot_addressed_def, word_scale_def] >>
  suspend "memory_dynamic_layout"
QED

Resume target_array_normal_suffix_ptr[memory_dynamic_layout]:
  qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[NoAsms, compile_array_subscript_split, compile_ptr_load_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `emit_op MLOAD [Var src] sn = (ln,sl)` >>
  rename1 `array_bounds_check _ _ _ sl = (uu,sg)` >> Cases_on `uu` >>
  `?out. ln = Var out` by (drule emitted_insts_emit_op >> simp[] >> metis_tac[]) >> gvs[] >>
  drule emit_op_extends >> strip_tac >>
  drule target_array_guard_layout >> strip_tac >>
  drule target_array_elem_layout >> strip_tac >>
  `cs_extends sn sl /\ cs_extends sl sg /\ cs_extends sg sb` by
    (simp[cs_extends_def, same_blocks_def] >>
     fs[same_blocks_def] >> metis_tac[IS_PREFIX_APPEND]) >>
  suspend "memory_dynamic_cuts"
QED

Resume target_array_normal_suffix_ptr[memory_dynamic_cuts]:
  `cs_extends sl sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sn sl func /\ fn_has_code sl sb func /\ fn_has_code sl sg func` by
    metis_tac[fn_has_code_split] >>
  `not_fresh_at sn src /\ 32 <= (32:num) /\ op_taint un (Var src) = {} /\
   w = a` by fs[copy_old_operand_def, target_ptr_ok_def, eval_operand_def] >>
  qpat_x_assum `w = a` SUBST_ALL_TAC >> `32 <= (32:num)` by simp[] >>
  drule_all target_live_dynamic_memory_array_continue_ptr >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  `sb.cs_current_bb = sn.cs_current_bb` by fs[same_blocks_def] >>
  `sb.cs_current_insts = sn.cs_current_insts ++
    (emitted_insts sn sl ++ emitted_insts sl sg ++ emitted_insts sg sb)` by fs[APPEND_ASSOC] >>
  `sb.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sb` by
    metis_tac[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `LENGTH sn.cs_current_insts + LENGTH (emitted_insts sn sb) =
   LENGTH sb.cs_current_insts` by metis_tac[LENGTH_APPEND] >>
  (irule target_array_suffix_outcome_ptr >>
   conj_tac >- first_assum ACCEPT_TAC >>
   conj_tac >- metis_tac[] >>
   reverse conj_tac
   >- (disj1_tac >> qexistsl_tac [`id`, `path`] >> REFL_TAC) >>
   qexists_tac `sn` >> metis_tac[])
QED

Resume target_array_normal_suffix_ptr[storage]:
  `(?id. target_root bt = NameTarget id) \/
   (?src id. target_root bt = TopLevelNameTarget (src,id))` by
    (`(!x:expr. T) /\ !bt. (?id. target_root bt = NameTarget id) \/
       (?src id. target_root bt = TopLevelNameTarget (src,id))`
       suffices_by metis_tac[] >>
     ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
     rw[target_root_def] >> Cases_on `p` >> simp[])
  >- (drule_all stmtSimAugAssignPlaceTheory.aug_place_name_root_base >> simp[]) >>
  `!lbl. bop <> Label lbl` by
    (drule_all target_toplevel_compiled_not_label_ptr >> simp[]) >>
  drule target_storage_index_frame_ptr >> simp[] >>
  disch_then drule >> disch_then drule >> simp[] >> strip_tac >>
  suspend "storage_frame"
QED

Resume target_array_normal_suffix_ptr[storage_frame]:
  first_x_assum drule >> strip_tac >>
  `?etv. evaluate_type (get_tenv cx) et = SOME etv /\
     tv = ArrayTV etv bd /\ loc = SOME (slot_loc tr)` by
    (fs[place_ptr_rel_def, Once evaluate_type_def, AllCaseEqs()] >> metis_tac[]) >>
  gvs[] >> suspend "storage_source"
QED

Resume target_array_normal_suffix_ptr[storage_source]:
  `EVERY pure_expr (target_indices bt) /\ pure_expr e` by
    fs[target_indices_def, EVERY_APPEND] >>
  `em = es with gas_obs := gs` by
    metis_tac[nested_pop_eval_base_pure_state] >>
  `contract_storage_well_formed cx (es with gas_obs := gs)` by
    (qpat_x_assum `expr_sim_inv _ _ _ em` mp_tac >>
     simp[Once expr_sim_inv_def] >> metis_tac[]) >>
  drule_all target_index_pure_storage_source_ptr >> strip_tac >>
  `op_taint un bop = {}` by (Cases_on `bop` >> fs[target_ptr_ok_def, op_taint_def]) >>
  `evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd)` by
    fs[place_ptr_rel_def] >>
  `elem_size_in_location cenv (slot_loc tr) et = type_slot_size etv /\
   word_scale (slot_loc tr) = 1` by
    (Cases_on `tr` >> simp[elem_size_in_location_def, slot_loc_def,
       word_scale_def, is_slot_addressed_def] >>
     irule unwrap_typed_buffer_count >>
     irule expr_sim_inv_memory_size >> metis_tac[]) >>
  Cases_on `bd` >> fs[] >- suspend "storage_fixed" >> suspend "storage_dynamic"
QED

Resume target_array_normal_suffix_ptr[storage_fixed]:
  gvs[] >>
  `cs_extends sn sb` by fs[ci_mono_def] >>
  qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[NoAsms, compile_array_subscript_split, comp_bind_def,
       comp_return_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >> rename1 `array_bounds_check _ _ _ sn = (uu,sg)` >>
  Cases_on `uu` >>
  drule target_array_guard_layout >> strip_tac >>
  drule target_array_elem_layout >> strip_tac >>
  `sb.cs_current_bb = sn.cs_current_bb /\
   sb.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sb` by
    (fs[same_blocks_def] >>
     `sb.cs_current_insts = sn.cs_current_insts ++
       (emitted_insts sn sg ++ emitted_insts sg sb)` by fs[APPEND_ASSOC] >>
     metis_tac[emitted_insts_def, DROP_LENGTH_APPEND]) >>
  drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >> strip_tac >>
  `lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sn sb) (DROP u.vs_inst_idx bb.bb_instructions)` by
    metis_tac[] >>
  suspend "storage_fixed_code"
QED

Resume target_array_normal_suffix_ptr[storage_fixed_code]:
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) u` by simp[] >>
  drule_all target_fixed_slot_array_continue_ptr >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  (irule target_array_suffix_outcome_ptr >> simp[] >>
   qexists_tac `sn` >>
   `LENGTH sn.cs_current_insts + LENGTH (emitted_insts sn sb) =
    LENGTH sb.cs_current_insts` by metis_tac[LENGTH_APPEND] >> metis_tac[])
QED

Resume target_array_normal_suffix_ptr[storage_dynamic]:
  gvs[] >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) u` by simp[] >>
  `stor_taint_ok cx un u` by fs[ghost_inv_def] >>
  `0 < type_slot_size (ArrayTV etv (Dynamic n))` by simp[type_slot_size_def] >>
  `key_taint (if tr then un.t_trans else un.t_stor) slot = {}` by
    (drule_all target_storage_header_clean_ptr >> simp[]) >>
  `op_prov H bop = NONE` by fs[target_ptr_ok_def] >>
  qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  `compile_ptr_load F cenv.ce_imm_alloca (slot_loc tr) =
     emit_op (if tr then TLOAD else SLOAD) o (\x. [x])` by
    (Cases_on `tr` >> simp[FUN_EQ_THM, compile_ptr_load_def, slot_loc_def]) >>
  simp[NoAsms, compile_array_subscript_split, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  suspend "storage_dynamic_layout"
QED

Resume target_array_normal_suffix_ptr[storage_dynamic_layout]:
  qpat_x_assum `compile_ptr_load _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `compile_ptr_load _ _ _ = _` (fn th => rewrite_tac[th]) >>
  simp[] >> strip_tac >>
  rename1 `emit_op _ [bop] sn = (ln,sl)` >>
  rename1 `array_bounds_check _ _ _ sl = (uu,sg)` >> Cases_on `uu` >>
  `?out. ln = Var out` by (drule emitted_insts_emit_op >> simp[] >> metis_tac[]) >> gvs[] >>
  drule emit_op_extends >> strip_tac >>
  drule target_array_guard_layout >> strip_tac >>
  drule target_array_elem_layout >> strip_tac >>
  `cs_extends sn sl /\ cs_extends sl sg /\ cs_extends sg sb` by
    (simp[cs_extends_def, same_blocks_def] >>
     fs[same_blocks_def] >> metis_tac[IS_PREFIX_APPEND]) >>
  `cs_extends sl sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sn sl func /\ fn_has_code sl sb func /\ fn_has_code sl sg func` by
    metis_tac[fn_has_code_split] >>
  suspend "storage_dynamic_code"
QED

Resume target_array_normal_suffix_ptr[storage_dynamic_code]:
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) u` by simp[] >>
  drule_all target_live_dynamic_slot_array_continue_ptr >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  `sb.cs_current_bb = sn.cs_current_bb` by fs[same_blocks_def] >>
  `sb.cs_current_insts = sn.cs_current_insts ++
    (emitted_insts sn sl ++ emitted_insts sl sg ++ emitted_insts sg sb)` by fs[APPEND_ASSOC] >>
  `sb.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sb` by
    metis_tac[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `LENGTH sn.cs_current_insts + LENGTH (emitted_insts sn sb) =
   LENGTH sb.cs_current_insts` by metis_tac[LENGTH_APPEND] >>
  (irule target_array_suffix_outcome_ptr >>
   conj_tac >- simp[NoAsms] >>
   conj_tac >- metis_tac[] >>
   reverse conj_tac
   >- (disj2_tac >> qexistsl_tac [`tr`, `slot`, `etv`, `Dynamic n`, `i`] >> simp[NoAsms]) >>
   qexists_tac `sn` >> metis_tac[])
QED

Finalise target_array_normal_suffix_ptr
