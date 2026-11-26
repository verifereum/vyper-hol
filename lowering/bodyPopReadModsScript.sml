(* Read the place denoted by the Pop result at the reached VV cursor. *)
Theory bodyPopReadMods
Ancestors
  bodyPopReadBindMods bodyPopWordLoadMods bodyPopWordFrameMods
  bodyPopReadMemoryBufferMods bodyPopReadSlotBufferMods
  bodyAugPlaceTarget exprSimPopNestedBase compilerInstructionSuffix exprSimCopy
  exprBodyPreTypingProps exprBodyPreCallSafetyProps vyperTypeEvalSoundness
  vyperTypeEvalCaseProofs vyperPlaceMutationSoundness vyperStatePreservation
  bodyFullPostsMods exprSimMemorySource gasOutcomeFullPostMods freshWrites
  exprLoweringProps ptrDiscipline
  vyperStorageFootprint venomState
  loweringPosts context compileEnv vyperAST vyperInterpreter vyperState
  typedMemoryCopy vyperTypeInvariants vyperTypeSystem exprLowering vyperTypeExprSoundness
Libs monadsyntax

Theorem pop_read_result_place[local]:
  ~immutable_root cx bt /\ eval_expr cx (Pop ann bt) es = (INL tv,ee) ==>
  (?id path. tv = PlaceR (MemoryPlace id path)) \/
  (?tr slot rt. tv = PlaceR (StoragePlace tr slot rt))
Proof
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `eval_target_place _ _ _ = (INL pl,_)` >>
  Cases_on `pl`
  >- (rename1 `StoragePlace tr slot rt` >>
      Cases_on `rt` >> gvs[pop_place_def, raise_def] >>
      rename1 `ArrayTV rt bd` >> Cases_on `bd` >>
      gvs[pop_place_def, raise_def, bind_def, ignore_bind_def,
          return_def, AllCaseEqs()])
  >- (drule pop_memory_place_success >> strip_tac >> simp[]) >>
  qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> rename1 `get_place pv _ = _` >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  drule aug_place_base_immutable_origin >> simp[]
QED

Theorem pop_result_operand_old[local]:
  compile_dynarray_pop hdr scale esz ctor imm loc a = (op,b) ==>
  copy_old_operand b op
Proof
  simp[compile_dynarray_pop_def, comp_ignore_bind_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >>
  strip_tac >> simp[copy_old_operand_def] >>
  drule_then ACCEPT_TAC typed_copy_emit_op_fresh
QED

Theorem pop_read_compile_result[local]:
  compile_expr ce ty (Pop ann bt) sa = (vv,sm) ==>
  ?p. vv = LocatedValue ann p /\ copy_old_operand sm p.ptr_operand
Proof
  simp[Once nested_pop_compile_eq] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[mk_ptr_def] >>
  drule pop_result_operand_old >> simp[]
QED

Theorem pop_read_typed[local]:
  expr_body_pre_mods mods ce cx env (Pop ann bt) es /\
  eval_expr cx (Pop ann bt) (es with gas_obs := gs) = (INL tv,ee) /\
  read_result cx tv ee = (INL v,ee) ==>
  ?rt. evaluate_type (get_tenv cx) ann = SOME rt /\ value_has_type rt v
Proof
  strip_tac >>
  drule expr_body_pre_mods_runtime_typing >> simp[runtime_consistent_def] >> strip_tac >>
  drule expr_body_pre_mods_call_evaluation_safe >> strip_tac >>
  `bind (eval_expr cx (Pop ann bt)) (read_result cx) (es with gas_obs := gs) = (INL v,ee)` by
    simp[vyperStateTheory.bind_def] >>
  qpat_assum `bind _ _ _ = _`
    (mp_then (Pat `bind _ _ _ = _`) (qspec_then `env` mp_tac)
       (REWRITE_RULE [ETA_AX] eval_expr_read_type_sound)) >>
  simp[] >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    metis_tac[env_consistent_type_defs_get_tenv] >>
  fs[value_runtime_typed_def, expr_type_def]
QED

Theorem pop_read_locations[local]:
  vv_post_mods H ctx func ce cx (Pop ann bt) es sa sm s0 ee tv
    (LocatedValue ann p) s /\
  ((?id path. tv = PlaceR (MemoryPlace id path)) \/
   (?tr slot rt. tv = PlaceR (StoragePlace tr slot rt))) ==>
  ((?id path. tv = PlaceR (MemoryPlace id path)) /\ p.ptr_location = LocMemory) \/
  (?tr. p.ptr_location = slot_loc tr)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >> gvs[] >>
  qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_post_mods_def, vv_place_ptr_mods_def, vv_place_ptr_def] >> metis_tac[]
QED

Theorem pop_value_from_vv_mods:
  expr_body_pre_mods mods ce cx env (Pop ann bt) es /\
  ~immutable_root cx bt /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (Pop ann bt) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (Pop ann bt) es
Proof
  strip_tac >> irule pop_read_bind_mods >> simp[] >>
  qx_genl_tac [`st0`,`sa`,`sm`,`sb`,`op`,`s0`,`G0`,`tn0`,`marks`,`ee`,`tv`,`vv`,`v`,`s`,`G`,`tn`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then (qx_choose_then `p` strip_assume_tac) pop_read_compile_result >>
  qpat_x_assum `vv = LocatedValue _ _` SUBST_ALL_TAC >>
  drule_all_then assume_tac pop_read_result_place >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `vv_store_bound cx ann (lowered_value_type ce (Pop ann bt)) ee tv
    (LocatedValue ann p) s /\ ptr_vv_ok cx ann tv (LocatedValue ann p) ee G tn s` by
    fs[expr_type_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx (Pop ann bt) es sa sm s0 ee tv (LocatedValue ann p) s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s` by
    (gen_tac >> disch_tac >> first_x_assum drule >> simp[]) >>
  irule gas_outcome_full_mods_pure >> simp[read_result_gas_obs] >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  Cases_on `is_word_type ann`
  >- suspend "word" >>
  drule_all_then strip_assume_tac pop_read_locations
  >- suspend "memory" >>
  suspend "slot"
QED

Resume pop_value_from_vv_mods[word]:
  `compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca p.ptr_location p.ptr_operand sm = (op,sb)` by
    fs[unwrap_value_def] >>
  `local_ptrs_reserved ce sm` by (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  drule_all_then (qx_choose_then `rt` strip_assume_tac) pop_read_typed >>
  `!w. read_result cx tv ee = (INL w,ee) ==> value_has_type rt w` by simp[] >>
  `post_value_type ce (Pop ann bt) = ann` by simp[expr_type_def] >>
  `p.ptr_location <> LocCode` by
    (drule_all pop_read_locations >> strip_tac >> simp[] >>
     Cases_on `tr` >> gvs[slot_loc_def]) >>
  `ce.ce_is_ctor /\ p.ptr_location = LocCode ==>
    ?val. read_result cx tv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) ann = SOME rt /\
             eval_operand p.ptr_operand s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
               val_in_memory rt val (w2n w) mem)` by simp[] >>
  drule_all pop_word_load_mods >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`rv`,`u`,`Gf`,`tf`] (map_every assume_tac o CONJUNCTS))) >>
  `rv = v` by fs[] >> qpat_x_assum `rv = v` SUBST_ALL_TAC >>
  qexistsl [`Gf`,`ee`,`INL v`,`u`,`tf`] >> simp[read_result_gas_obs,expr_type_def] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\
    ghost_inv_at_mods _ _ _ _ _ _ _ _ _` (drule_then strip_assume_tac) >>
  drule_all pop_word_read_frame_mods >>
  disch_then (qspec_then `sb` strip_assume_tac) >>
  `allocas_below_fmp u = allocas_below_fmp s /\ u.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
      (fn th => pure_once_rewrite_tac [th] >> simp[allocas_below_fmp_def])) >>
  simp[]
QED
Resume pop_value_from_vv_mods[memory]:
  qpat_x_assum `tv = PlaceR (MemoryPlace _ _)` SUBST_ALL_TAC >>
  `ptr_buf_ok ce (Pop ann bt) p.ptr_operand G s` by simp[] >>
  drule_all (REWRITE_RULE [post_value_type_def,expr_type_def] pop_nonword_memory_read_mods) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`u`,`Gf`,`tf`] assume_tac)) >>
  qexistsl [`Gf`,`ee`,`INL v`,`u`,`tf`] >> simp[read_result_gas_obs,expr_type_def] >>
  gen_tac >> disch_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> simp[]
QED
Resume pop_value_from_vv_mods[slot]:
  drule_all (REWRITE_RULE [post_value_type_def,expr_type_def] pop_nonword_slot_read_mods) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`u`,`Gf`,`tf`,`rt`,`w`] (map_every assume_tac o CONJUNCTS))) >>
  qexistsl [`Gf`,`ee`,`INL v`,`u`,`tf`] >> simp[read_result_gas_obs,expr_type_def]
QED
Finalise pop_value_from_vv_mods
