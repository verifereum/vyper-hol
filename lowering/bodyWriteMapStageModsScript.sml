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
