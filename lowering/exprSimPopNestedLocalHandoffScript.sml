Theory exprSimPopNestedLocalHandoff
Ancestors
  exprSimPopNestedLocalSource exprSimSource gasSummary targetPlaceSim
  stmtSimForArrayFrame vyperReadOnlyTargets vyperTypeContract vyperTypeSystem
  loweringPosts vyperState exprSimProps exprLoweringProps compileEnv loweringStateRelDefs
  exprSimAttributeFields valueEncoding finite_map words exprSimHypsDefs
  vyperTypeInvariants memoryValueEncoding

(* Compiler local types stay aligned with source entries across target effects. *)
Theorem pop_target_entry_compile_type:
  expr_body_pre cenv cx env (Pop ann bt) es /\
  eval_target_place cx bt es = (INL p,t) /\
  lookup_scopes id t.scopes = SOME entry ==>
  ?root_ty. cenv.ce_var_type id = SOME root_ty /\
    evaluate_type (get_tenv cx) root_ty = SOME entry.type
Proof
  strip_tac >> drule_all pop_target_source_facts >> strip_tac >>
  `env_scopes_consistent env cx t` by fs[env_consistent_def] >>
  `?root_ty. FLOOKUP env.var_types id = SOME root_ty /\
     evaluate_type (get_tenv cx) root_ty = SOME entry.type` by
    (fs[env_scopes_consistent_def] >>
     `IS_SOME (FLOOKUP env.var_types id)` by
       (qpat_x_assum `!id entry. _` drule >> simp[]) >>
     Cases_on `FLOOKUP env.var_types id` >> gvs[] >>
     qpat_x_assum `!id ty entry. _` drule_all >> simp[]) >>
  qexists_tac `root_ty` >> simp[] >>
  fs[expr_body_pre_def, expr_sim_inv_def]
QED

Theorem place_access_target_root:
  !bt attrs. FST (place_access bt attrs) = target_root bt
Proof
  completeInduct_on `base_assignment_target_size bt` >>
  Cases_on `bt` >> simp[place_access_def, target_root_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem toplevel_target_root:
  !bt. toplevel_target bt = toplevel_target (target_root bt)
Proof
  completeInduct_on `base_assignment_target_size bt` >>
  Cases_on `bt` >> simp[toplevel_target_def, target_root_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem eval_target_place_named_root:
  target_root bt = NameTarget id /\
  eval_target_place cx bt s = (INL p,t) ==>
  ?path. p = MemoryPlace id path
Proof
  strip_tac >>
  `~toplevel_target bt` by (once_rewrite_tac[toplevel_target_root] >> simp[toplevel_target_def]) >>
  drule_all eval_target_place_local >> strip_tac >> gvs[] >>
  drule eval_target_place_memory_root >>
  simp[place_access_target_root] >> strip_tac >> gvs[]
QED

Theorem pop_counted_source_handoff:
  expr_body_pre cenv cx env (Pop ann bt) es /\
  target_root bt = NameTarget id /\
  (!path entry err.
     p = MemoryPlace id path /\
     lookup_scopes id tend.scopes = SOME entry /\
     evaluate_subscripts entry.type entry.value path = INR err ==>
     read_popped entry.type path entry.popped = NONE) /\
  gas_marked_exec F (ctx,func) (eval_target_place cx bt)
    (es,s0) marks (INL p) tend (OK t) /\
  place_readable cx (tend with gas_obs := []) (PlaceR p) ==>
  ?path entry etv n vs root_ty.
    p = MemoryPlace id path /\
    cenv.ce_var_type id = SOME root_ty /\
    evaluate_type (get_tenv cx) root_ty = SOME entry.type /\
    lookup_scopes id tend.scopes = SOME entry /\ entry.assignable /\
    mutable_place_path entry.type path /\
    value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
    evaluate_type env.type_defs ann = SOME etv /\
    subscripts_type entry.type path = SOME (ArrayTV etv (Dynamic n)) /\
    evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs))
Proof
  strip_tac >>
  `eval_target_place cx bt
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL p,tend with gas_obs := [])` by
    (fs[gas_marked_exec_def] >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  drule_all eval_target_place_named_root >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env (Pop ann bt)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  qpat_x_assum `expr_body_pre _ _ _ _ es` kall_tac >>
  drule pop_target_live_array >>
  disch_then (drule_at Any) >> simp[] >>
  strip_tac >>
  `?root_ty. cenv.ce_var_type id = SOME root_ty /\
     evaluate_type (get_tenv cx) root_ty = SOME entry.type` by
    (drule pop_target_entry_compile_type >> disch_then drule >> simp[]) >>
  qexistsl_tac [`entry`, `etv`, `n`, `vs`, `root_ty`] >> simp[]
QED

(* This boundary is independent of the path's final type.  Root type
   coherence is supplied by the source environment, not by pointer bytes. *)
Theorem memory_target_encoding_handoff:
  target_post ctx func cenv cx es sa sb s0 es'
    (PlaceR (MemoryPlace id path)) (Type ty) (hdr,loc,pt) s /\
  lookup_scopes id es'.scopes = SOME entry /\
  value_has_type entry.type entry.value /\
  cenv.ce_var_type id = SOME root_ty /\
  evaluate_type (get_tenv cx) root_ty = SOME entry.type ==>
  loc = SOME LocMemory /\ pt = SOME (value_type_place (Type ty)) /\
  stmt_state_rel ctx func cenv cx es' s /\
  wb_frame cenv es es' sa s0 s /\
  (!x. hdr = Var x ==> not_fresh_at sb x) /\
  ?p b sz k tv w.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME b /\
    eval_operand hdr s = SOME w /\ w = b + n2w k /\
    w2n w = w2n b + k /\
    local_region cenv es'.scopes s id (w2n b) sz /\
    w2n b + sz < dimword (:256) /\
    type_memory_size entry.type <= sz /\
    val_wf entry.type entry.value /\
    val_in_memory entry.type entry.value (w2n b) s.vs_memory /\
    mem_path_offset entry.type path = SOME (k,tv) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    local_path_at cenv cx id k tv /\
    k + type_memory_size tv <= sz
Proof
  strip_tac >>
  gvs[target_post_def, place_ptr_rel_def] >>
  `local_ptrs_rel func cenv es'.scopes s` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  `?b'. lookup_var p s = SOME b' /\
     type_memory_size entry.type <= sz /\
     val_wf entry.type entry.value /\
     val_in_memory entry.type entry.value (w2n b') s.vs_memory` by
    (fs[local_ptrs_rel_def] >>
     qpat_x_assum `!name entry p sz. _` drule_all >> strip_tac >>
     gvs[] >> metis_tac[memory_value_rel_val_in_memory]) >>
  gvs[] >>
  `local_region cenv es'.scopes s id (w2n b) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `w2n b + sz < dimword (:256)` by
    (drule stmt_state_rel_region_lt >> metis_tac[]) >>
  `k + type_memory_size tv <= sz` by
    (drule mem_path_offset_sound >> strip_tac >> decide_tac) >>
  `w2n (b + n2w k) = w2n b + k` by
    (irule buffer_offset_no_wrap >> qexists_tac `sz` >> simp[] >> decide_tac) >>
  simp[wb_frame_def] >> conj_tac
  >- first_assum ACCEPT_TAC >>
  simp[local_path_at_def] >> metis_tac[]
QED
