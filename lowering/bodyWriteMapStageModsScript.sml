(* Counted extension of an already reached mapping reference. *)
Theory bodyWriteMapStageMods
Ancestors
  bodyWriteTargetStageMods bodyFullTargetMappingFacts
  targetSubscriptMapping targetSubscriptSplit gasOutcomeFullPostMods
  bodyFullHashKeccakFixed[qualified,ignore_grammar] bodyFullShadowBodyInv
  bodyInvSplit bodyMemoryDefs loweringStateRelDefs vyperStorageTrace
  vyperStorageFootprint vyperStorage gasSummary vyperTypeEnv vyperTypeSystem
  vyperInterpreter vyperState gasOutcome targetPlaceSimCasesBase compileEnv
  bodyFullPostsMods bodyPtrDefs loweringPosts venomState allocaHistory
  gasContext targetPlaceSimDefs exprLoweringProps bodyFullTargetDefs vyperStorageBackend
  bodyWriteMapCompileCutsMods bodyWriteMapBindCutsMods bodyWriteMapReachedKeyMods
  bodyWriteMapSuffixMods bodyFullTargetMappingRun bodyFullIfExpReach
  exprOperandVar exprSimWordArgs fragExec venomInst finite_map list freshWrites

Theorem write_map_index_types_mods:
  type_place_target env bt = SOME (HashMapT kt vt) /\
  type_place_target env (SubscriptTarget bt e) = SOME et ==>
  et = vt /\ expr_type e = kt /\ hashmap_key_type kt
Proof
  simp[type_place_target_SubscriptTarget] >> strip_tac >>
  gvs[subscript_vtype_def, AllCaseEqs()]
QED

Theorem mapping_extension_trace_frame[local]:
  (immutable_frame_mods func cenv cx (mid with storage_trace := st) t <=>
   immutable_frame_mods func cenv cx mid t) /\
  (storage_well_formed_on cx (mid with storage_trace := st) rs <=>
   storage_well_formed_on cx mid rs) /\
  (wb_frame cenv es (mid with storage_trace := st) sa s0 t <=>
   wb_frame cenv es mid sa s0 t) /\
  (ghost_inv_at_mods D lo d cenv cx (mid with storage_trace := st) G tn t <=>
   ghost_inv_at_mods D lo d cenv cx mid G tn t)
Proof
  simp[immutable_frame_mods_def, immutables_rel_mods_def,
       immutable_alloca_sep_mods_def, immutables_rel_def,
       immutable_alloca_sep_def, storage_well_formed_on_def,
       wb_frame_def, locals_kept_def, popped_kept_def,
       get_storage_def, immutable_decl_sep_alt, ghost_inv_at_mods_def]
QED

Theorem mapping_extension_linked_outcome[local]:
  extend_place cx (HashMapRef tr base_slot kt vt) (ValueSubscript v) mid = (res,ee) /\
  gas_admissible (extend_place cx (HashMapRef tr base_slot kt vt) (ValueSubscript v))
    target_res_ok mid /\ ~s.vs_halted /\ mid.gas_obs = [] /\
  eval_operand slot t = SOME (hashmap_slot base_slot (encode_hashmap_key kt v)) /\
  op_taint tn slot = {} /\ op_prov G slot = NONE /\
  (!x. slot = Var x ==> not_fresh_at sb x) /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  wb_frame cenv es mid sa s0 t /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid t /\
    storage_well_formed_on cx mid (FST H) /\
    immutable_frame_mods func cenv cx mid t /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G tn t /\
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s,G2,tn2) [] (OK t,G,tn)) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (extend_place cx (HashMapRef tr base_slot kt vt) (ValueSubscript v))
    (mid,s,G2,tn2)
    (\H res ee G tn t. ?pv. res = INL pv /\
      write_target_post_mods H (DF H) lo d ctx func cenv cx (SubscriptTarget bt e)
        es sa sb s0 ee pv vt (slot,SOME (slot_loc tr),SOME (value_type_place vt))
        G0 tn0 G tn t) R
Proof
  strip_tac >>
  `!tail. extend_place cx (HashMapRef tr base_slot kt vt) (ValueSubscript v)
      (mid with gas_obs := tail) = (res,ee with gas_obs := tail)` by
    simp[target_subscript_extend_gas_obs] >>
  Cases_on `storage_trace_domain cx st0 ee.storage_trace`
  >- suspend "normal" >>
  irule gas_outcome_full_mods_bad_nil >> simp[]
QED

Resume mapping_extension_linked_outcome[normal]:
  `?pv. res = INL pv` by
    (Cases_on `vt`
     >- (rename1 `Type ty` >> Cases_on `evaluate_type (get_tenv cx) ty` >>
         gvs[extend_place_def, lift_option_type_def, bind_def, ignore_bind_def,
             return_def, raise_def, record_storage_event_def,
             gas_admissible_def, target_res_ok_def]) >>
     gvs[extend_place_nested_mapping]) >>
  gvs[] >> drule target_mapping_extend_place >> strip_tac >>
  irule gas_outcome_full_mods_pure >>
  simp[] >> qexistsl_tac [`G`,`ee`,`INL pv`,`t`,`tn`] >> simp[] >>
  gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
  qpat_assum `!s'' cenv. _ /\ _ /\ _` (qspecl_then [`t`,`cenv`] strip_assume_tac) >>
  `ee.gas_obs = []` by (qpat_assum `ee = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  simp[write_target_post_mods_def] >>
  suspend "post"
QED

Resume mapping_extension_linked_outcome[post]:
  drule_then assume_tac bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >>
  qpat_assum `ee = _` (fn th => once_rewrite_tac[th]) >>
  simp[mapping_extension_trace_frame] >>
  qpat_assum `ee = _` (fn th => once_rewrite_tac[GSYM th]) >>
  Cases_on `pv` >> gvs[place_ptr_rel_def, target_ptr_ok_def, write_target_location_mods_def] >>
  rename1 `PlaceR p` >> Cases_on `p` >>
  gvs[place_ptr_rel_def, target_ptr_ok_def, write_target_location_mods_def] >>
  Cases_on `tr` >> gvs[slot_loc_def]
QED

Finalise mapping_extension_linked_outcome

Theorem write_map_index_stage_mods:
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  expr_sim_inv_mods mods cenv cx env es /\
  body_const_cells_agree_mods mods cx env es /\
  type_place_target env bt = SOME (HashMapT kt vt) /\
  (!i s. MEM i (target_indices (SubscriptTarget bt e)) /\
         expr_sim_inv_mods mods cenv cx env s ==>
         expr_body_pre_mods mods cenv cx env i s) /\
  body_base_target_full_ok_mods mods exps cx (SubscriptTarget bt e) /\
  write_base_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx env bt es ==>
  write_base_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env (SubscriptTarget bt e) es
Proof
  strip_tac >> simp[write_base_sim_mods_def] >> rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac write_map_index_types_mods >> gvs[] >>
  drule_then strip_assume_tac write_map_compile_cuts_mods >>
  `MEM func ctx.ctx_functions` by fs[write_target_entry_mods_def] >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> drule_all body_inv_no_phi_mods >> simp[]) >>
  irule write_map_bind_cuts_mods >> asm_rewrite_tac[] >>
  qexistsl_tac [`env`,`iop`,`expr_type e`,`rb`,`shadow_func`,`shadow_sa`,`shadow_sb`,
                `shadow_sm`,`shadow_sn`,`sm`,`sn`] >>
  asm_rewrite_tac[] >> conj_tac
  >- (rpt strip_tac >> drule_all write_map_reached_key_mods >> simp[]) >>
  suspend "suffix"
QED

Resume write_map_index_stage_mods[suffix]:
  qx_genl_tac [`base_gas`,`pv`,`mid1`,`t1`,`G1`,`tn1`,`key_gas`,`v`,`mid2`,`t2`,`G2`,`tn2`] >>
  strip_tac >>
  `mid1 with gas_obs := [] = mid1` by simp[evaluation_state_component_equality] >>
  `mid2 with gas_obs := [] = mid2` by simp[evaluation_state_component_equality] >>
  `eval_base_place cx bt (es with gas_obs := base_gas) = (INL pv,mid1)` by
    (qpat_assum `!tail. eval_base_place _ _ _ = _` (qspec_then `[]` mp_tac) >>
     rewrite_tac[APPEND_NIL] >>
     qpat_assum `mid1 with gas_obs := [] = mid1` (fn th => rewrite_tac[th])) >>
  `bind (eval_expr cx e) (read_result cx) (mid1 with gas_obs := key_gas) = (INL v,mid2)` by
    (qpat_assum `!tail. bind (eval_expr _ _) _ _ = _` (qspec_then `[]` mp_tac) >>
     rewrite_tac[APPEND_NIL] >>
     qpat_assum `mid2 with gas_obs := [] = mid2` (fn th => rewrite_tac[th])) >>
  drule_all write_map_reached_key_mods >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  `expr_type e = expr_type e` by simp[] >>
  `valid_horizon cx st0 (storage_trace_horizon mid2.storage_trace) mid2.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac write_map_key_input_mods >> rpt BasicProvers.VAR_EQ_TAC >>
  drule_all_then strip_assume_tac target_mapping_compile_cut >> rpt BasicProvers.VAR_EQ_TAC >>
  suspend "machine"
QED

Resume write_map_index_stage_mods[machine]:
  qpat_assum `write_target_entry_mods _ _ _ (SubscriptTarget bt e) _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [write_target_entry_mods_def]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
   sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id` by
    fs[ci_mono_def,cs_extends_def] >>
  `sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id` by decide_tac >>
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sn` by
    (conj_tac >> irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!x. iop = Var x \/ bop = Var x ==> not_fresh_at sn x` by
    (rpt strip_tac >- (drule_all compile_lower_value_var >> simp[]) >>
     irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `allocas_from lo t2 /\ lo <= t2.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
       (drule_then strip_assume_tac) >> fs[ghost_inv_at_mods_def]) >>
  `!H. valid_horizon cx st0 H mid2.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid2 t2 /\
     immutable_frame_mods func cenv cx mid2 t2 /\
     ghost_inv_at_mods (DF H) lo d cenv cx mid2 G2 tn2 t2` by
    (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
       (drule_then strip_assume_tac) >> fs[expr_post_mods_def,expr_post_def]) >>
  drule_all (BETA_RULE (Q.INST
    [`P` |-> `\H. valid_horizon cx st0 H mid2.storage_trace`]
    (INST_TYPE [Type.alpha |-> ``:256``] mapping_suffix_run_mods))) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`t`,`G`,`tn`] strip_assume_tac)) >>
  suspend "frames"
QED

Resume write_map_index_stage_mods[frames]:
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,storage_trace_frame_read_result] >>
  `valid_horizon cx st0 (storage_trace_horizon mid2.storage_trace) mid1.storage_trace` by
    (qpat_assum `bind (eval_expr _ _) _ _ = _` (mp_then (Pat `_ = _`) mp_tac valid_horizon_frame) >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid2.storage_trace) es.storage_trace` by
    (qpat_assum `eval_base_place _ _ _ = _` (mp_then (Pat `_ = _`) mp_tac valid_horizon_frame) >>
     simp[evaluate_storage_trace_frame]) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  drule_then strip_assume_tac write_target_post_view_mods >>
  `wb_frame cenv mid1 mid2 sm t1 t2` by
    (qpat_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ t2`
       (mp_tac o REWRITE_RULE [expr_post_mods_def]) >>
     strip_tac >> drule_then ACCEPT_TAC expr_post_frame) >>
  `MAP FDOM es.scopes = MAP FDOM mid1.scopes /\
   MAP FDOM es.scopes = MAP FDOM mid2.scopes /\
   MAP FDOM mid2.scopes = MAP FDOM mid1.scopes` by
    (qpat_assum `wb_frame cenv es mid1 sa s0 t1` mp_tac >>
     qpat_assum `wb_frame cenv mid1 mid2 sm t1 t2` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[wb_frame_def,locals_kept_def] >> metis_tac[]) >>
  `wb_frame cenv es mid2 sa s0 t2 /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2` by
    (irule (INST_TYPE [Type.beta |-> ``:256``] mapping_suffix_frames_join) >> simp[] >>
     conj_tac >- (qexistsl_tac [`storage_trace_horizon mid2.storage_trace`,`ctx`,`cx`,`func`] >> simp[]) >>
     qexistsl_tac [`G1`,`mid1`,`t1`,`sm`,`tn1`] >> simp[]) >>
  `wb_frame cenv es mid2 sa s0 t /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn` by
    (irule (INST_TYPE [Type.beta |-> ``:256``] mapping_suffix_frames_join) >> simp[] >>
     conj_tac >- (qexistsl_tac [`storage_trace_horizon mid2.storage_trace`,`ctx`,`cx`,`func`] >> simp[]) >>
     qexistsl_tac [`G2`,`mid2`,`t2`,`sn`,`tn2`] >> simp[]) >>
  `s0.vs_alloca_next <= t.vs_alloca_next` by decide_tac >>
  suspend "extend"
QED

Resume write_map_index_stage_mods[extend]:
  Cases_on `extend_place cx (HashMapRef tr base_slot (expr_type e) vt) (ValueSubscript v) mid2` >>
  rename1 `_ = (res,ee)` >>
  irule mapping_extension_linked_outcome >> asm_rewrite_tac[] >>
  qexistsl_tac [`G`,`ee`,`res`,`t`,`tn`] >> asm_rewrite_tac[] >>
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 H mid2.storage_trace` by
    (qpat_assum `extend_place _ _ _ _ = _` (mp_then (Pat `_ = _`) mp_tac valid_horizon_frame) >>
     simp[storage_trace_frame_extend_place]) >>
  qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==>
      write_target_post_mods H _ _ _ ctx func cenv cx bt es sa sm s0 mid1
        _ _ _ G0 tn0 G1 tn1 t1 /\ _`
    (drule_then strip_assume_tac) >> fs[expr_post_mods_def,expr_post_def]
QED

Finalise write_map_index_stage_mods
