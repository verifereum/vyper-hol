Theory bodyFullTargetMappingOutcome
Ancestors
  bodyFullTargetDefs gasOutcomeFull fragGasOriginPtr targetSubscriptMapping
  targetSubscriptSplit bodyPtrDefs gasContext targetPlaceSimDefs
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState
  loweringPosts exprLoweringProps vyperStorage compileEnv gasSummary

Theorem mapping_extension_full_outcome:
  extend_place cx (HashMapRef tr base_slot kt vt) (ValueSubscript v) mid2 = (res,ee) /\
  gas_admissible (extend_place cx (HashMapRef tr base_slot kt vt) (ValueSubscript v))
    target_res_ok mid2 /\
  storage_trace_domain cx st0 mid2.storage_trace /\ mid2.gas_obs = [] /\
  ~t2.vs_halted /\
  eval_operand slot t = SOME (hashmap_slot base_slot (encode_hashmap_key kt v)) /\
  op_taint tn slot = {} /\ op_prov G slot = NONE /\
  (!x. slot = Var x ==> not_fresh_at sb x) /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  wb_frame cenv es mid2 sa s0 t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid2 t /\
    storage_well_formed_on cx mid2 (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid2 G tn t /\
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (t2,G2,tn2) [] (OK t,G,tn)) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (extend_place cx (HashMapRef tr base_slot kt vt) (ValueSubscript v))
    (mid2,t2,G2,tn2)
    (\H res ee G tn t. ?pv'. res = INL pv' /\
      target_post H ctx func cenv cx es sa sb s0 ee pv' vt
        (slot,SOME (slot_loc tr),SOME (value_type_place vt)) t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      target_ptr_ok cenv pv'
        (slot,SOME (slot_loc tr),SOME (value_type_place vt)) G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
    (\H res ee gt q. expr_exit res q)
Proof
  strip_tac >>
  `!tail. extend_place cx (HashMapRef tr base_slot kt vt) (ValueSubscript v)
      (mid2 with gas_obs := tail) = (res,ee with gas_obs := tail)` by
    simp[target_subscript_extend_gas_obs] >>
  Cases_on `storage_trace_domain cx st0 ee.storage_trace`
  >- (`?pv'. res = INL pv'` by
        (Cases_on `vt`
         >- (rename1 `Type typ` >> Cases_on `evaluate_type (get_tenv cx) typ` >>
             gvs[extend_place_def, lift_option_type_def,
                 bind_def, ignore_bind_def, return_def, raise_def,
                 record_storage_event_def, gas_admissible_def, target_res_ok_def]) >>
         gvs[extend_place_nested_mapping]) >>
      gvs[] >>
      `ee = mid2 with storage_trace := ee.storage_trace` by
        metis_tac[target_mapping_extend_place] >>
      `ee.gas_obs = []` by
        (qpat_assum `ee = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
      `ee with gas_obs := [] = ee` by
        (qpat_assum `ee.gas_obs = []` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
      simp[gas_outcome_full_def] >> qexists_tac `[]` >>
      disj2_tac >> disj1_tac >>
      qexistsl_tac [`INL pv'`, `ee`, `OK t`, `G`, `tn`] >>
      simp[gas_explicit_def] >> gen_tac >> disch_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _` drule >>
      strip_tac >> simp[] >>
      conj_tac
      >- (irule target_mapping_post >> simp[] >>
          qexistsl_tac [`mid2`, `v`, `kt`, `base_slot`] >> simp[]) >>
      conj_tac
      >- metis_tac[ghost_inv_at_storage_trace] >>
      `place_ptr_rel cenv cx t pv'
         (hashmap_slot base_slot (encode_hashmap_key kt v))
         (SOME (slot_loc tr)) vt` by metis_tac[target_mapping_extend_place] >>
      Cases_on `pv'` >> gvs[target_ptr_ok_def] >>
      rename1 `PlaceR p` >> Cases_on `p` >>
      gvs[target_ptr_ok_def, place_ptr_rel_def, slot_loc_def] >>
      Cases_on `tr` >> gvs[]) >>
  simp[gas_outcome_full_def] >> qexists_tac `[]` >> disj1_tac >>
  conj_tac
  >- (irule gas_bad_storage_at_endpoint >>
      qexistsl_tac [`ee`, `res`] >> simp[gas_explicit_def]) >>
  qexistsl_tac [`storage_trace_horizon mid2.storage_trace`,
    `func`, `PG`, `G2`, `tn2`, `t2`] >>
  simp[gas_origin_ptr_focus_nil] >> gvs[storage_trace_domain_def]
QED
