(* Memory-safe index handoff after a reachable target prefix. *)
Theory popNestedTargetMemory
Ancestors
  bodyMemoryPreds targetPlaceSimMem targetSubscriptSplit
  targetPlaceSim targetPlaceSimCasesBase
  exprSimMemDefs popNestedTargetRootsMemory popNestedTargetAttributeMemory
  popNestedTargetIndexMemory popNestedTargetSuffixMemory
  popNestedStorageIndexReadiness popNestedLocalReadinessMemory

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
