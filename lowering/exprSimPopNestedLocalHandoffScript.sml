Theory exprSimPopNestedLocalHandoff
Ancestors
  exprSimPopNestedLocalSource exprSimSource gasSummary targetPlaceSim
  stmtSimForArrayFrame vyperReadOnlyTargets vyperTypeContract vyperTypeSystem
  loweringPosts vyperState

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
  (!s path t entry err.
     eval_target_place cx bt s = (INL (MemoryPlace id path),t) /\
     lookup_scopes id t.scopes = SOME entry /\
     evaluate_subscripts entry.type entry.value path = INR err ==>
     read_popped entry.type path entry.popped = NONE) /\
  gas_marked_exec F (ctx,func) (eval_target_place cx bt)
    (es,s0) marks (INL p) tend (OK t) /\
  place_readable cx (tend with gas_obs := []) (PlaceR p) ==>
  ?path entry etv n vs.
    p = MemoryPlace id path /\
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
  impl_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!s path t entry err. _` irule >>
      conj_tac
      >- (qexistsl_tac [`es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
                       `tend with gas_obs := []`] >> simp[]) >>
      metis_tac[]) >>
  simp[]
QED
