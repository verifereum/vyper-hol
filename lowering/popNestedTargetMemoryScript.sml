(* Memory-safe index handoff after a reachable target prefix. *)
Theory popNestedTargetMemory
Ancestors
  bodyMemoryPreds targetPlaceSimMem targetSubscriptSplit
  targetPlaceSim targetPlaceSimCasesBase
  exprSimMemDefs popNestedTargetRootsMemory popNestedTargetAttributeMemory
  popNestedTargetIndexMemory popNestedTargetSuffixMemory
  popNestedStorageIndexReadiness popNestedLocalReadinessMemory
  popNestedSubscriptConstructorMemory popNestedSubscriptContinuationMemory
  exprSimPopNestedBase exprSimPopNestedStorageFrame loweringPosts
  targetPlaceSimDefs vyperInterpreter vyperState exprSimHypsDefs targetPlaceLive

Theorem pop_nested_subscript_index_mem:
  body_inv tops ctx cenv cx /\
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  body_base_target_mem_ok cx (SubscriptTarget bt e) /\
  gas_marked_exec T (ctx,func) (eval_base_place cx bt)
    (es,s0) marks (INL pv) mid (OK t) ==>
  expr_sim_mem ctx func cenv cx ty e (mid with gas_obs := []) /\
  expr_vv_sim_mem ctx func cenv cx ty e (mid with gas_obs := [])
Proof
  strip_tac >>
  `target_pre cenv cx env bt es` by metis_tac[target_pre_sub] >>
  `expr_sim_inv cenv cx env (mid with gas_obs := [])` by
    metis_tac[target_subscript_marked_base_inv] >>
  `expr_body_pre cenv cx env e (mid with gas_obs := [])` by
    fs[target_pre_def, target_indices_pre_def] >>
  `body_expr_mem_ok cx e` by
    (fs[body_base_target_mem_ok_def] >>
     first_x_assum irule >>
     drule target_subscript_marked_base_source >>
     disch_then (qspec_then `[]` assume_tac) >> metis_tac[]) >>
  fs[body_expr_mem_ok_def] >> first_x_assum irule >>
  conj_tac >- metis_tac[] >> qexists_tac `env` >> simp[]
QED

Theorem pop_nested_storage_target_mem:
  !bt. !ctx func cenv cx env es src id ts d.
    body_inv (cx_tops cx) ctx cenv cx /\
    target_pre cenv cx env bt es /\ body_base_target_mem_ok cx bt /\
    target_root bt = TopLevelNameTarget (src,id) /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d /\
    EVERY (storage_frame_expr cx) (target_indices bt) ==>
    target_sim_mem ctx func cenv cx env bt es
Proof
  recInduct base_assignment_target_induct >> rpt conj_tac >> rpt gen_tac
  >- simp[target_root_def]
  >- (rpt strip_tac >> irule pop_nested_target_toplevel_mem >>
      fs[target_pre_def])
  >- suspend "subscript"
  >> strip_tac >> rpt gen_tac >> strip_tac >>
  irule pop_nested_target_attr_mem >> simp[] >> first_x_assum irule >>
  gvs[target_root_def, body_base_target_mem_ok_def, target_indices_def] >>
  metis_tac[target_pre_sub]
QED

Resume pop_nested_storage_target_mem[subscript]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  irule pop_nested_subscript_constructor_mem >> simp[] >> reverse conj_tac
  >- (first_x_assum irule >>
      gvs[target_root_def, body_base_target_mem_ok_def, target_indices_def] >>
      metis_tac[target_pre_sub, listTheory.EVERY_APPEND]) >>
  rpt gen_tac >> strip_tac >>
  `expr_sim_mem ctx func cenv cx (expr_type e) e (mid with gas_obs := [])` by
    (drule_all pop_nested_subscript_index_mem >> simp[]) >>
  irule pop_nested_subscript_continuation_mem >> simp[] >>
  suspend "ready"
QED

Resume pop_nested_storage_target_mem[ready]:
  reverse conj_tac
  >- (goal_assum (drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >> simp[] >>
      qexists `env` >> simp[]) >>
  rpt gen_tac >> disch_tac >>
  drule target_subscript_marked_base_source >>
  disch_then (qspec_then `gs` assume_tac) >>
  `target_root bt = TopLevelNameTarget (src,id)` by fs[target_root_def] >>
  drule_all nested_pop_eval_base_storage_class >> strip_tac >> gvs[] >>
  simp[place_readable_def] >>
  `storage_layout_safe cx /\ contract_storage_well_formed cx
     (es with gas_obs := gas_explicit left s0.vs_gas_readings ++ gs) /\
   EVERY (storage_frame_expr cx) (target_indices bt) /\ storage_frame_expr cx e` by
    (fs[target_pre_def, expr_sim_inv_def, target_indices_def, listTheory.EVERY_APPEND] >>
     irule vyperStorageLayoutSafetyTheory.contract_storage_well_formed_storage_frame >>
     qexists `es` >> simp[] >> Cases >> simp[vyperStorageBackendTheory.get_storage_def]) >>
  drule_all pop_nested_storage_index_ready >> simp[]
QED

Finalise pop_nested_storage_target_mem
