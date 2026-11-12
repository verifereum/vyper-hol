(* Conditional universal simulation: source replay remains an explicit premise. *)
Theory targetPureWalkConditionalSim
Ancestors
  targetPureWalkSimulationProbe targetPureWalkCountedProbe
  targetPureWalkTransportProbe targetPlaceSimDefs
  gasOutcome gasSummary vyperTypeEnv vyperTypeSystem vyperState compileEnv
  finite_map targetPureWalkModuleProbe vyperAST

Theorem simulation_probe_target_sim_conditional_lookup:
  !ctx fn cx env es ee entry.
    lookup_function simulation_probe_label ctx.ctx_functions =
      SOME simulation_probe_callee /\
    FLOOKUP env.var_types "a" =
      SOME (ArrayT (BaseT (UintT 256)) (Fixed 1)) /\
    lookup_scopes "a" es.scopes = SOME entry /\
    (!tail. eval_base_place cx module_probe_target (es with gas_obs := tail) =
      (INL (PlaceR (MemoryPlace "a" [ValueSubscript (IntV 0)])),
       ee with gas_obs := tail)) /\
    place_readable cx (ee with gas_obs := [])
      (PlaceR (MemoryPlace "a" [ValueSubscript (IntV 0)])) /\
    ee.scopes = es.scopes /\ ee.accounts = es.accounts /\
    ee.tStorage = es.tStorage /\ ee.logs = es.logs /\
    ee.outcomes = es.outcomes /\ ee.requests = es.requests /\
    ee.pending_deletions = es.pending_deletions ==>
    target_sim ctx fn simulation_probe_cenv cx env
      module_probe_target es
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[target_sim_def] >> rpt strip_tac >>
  `vt = Type (BaseT (UintT 256))` by
    (gvs[module_probe_target_def, type_place_target_SubscriptTarget,
         type_place_target_NameTarget, subscript_vtype_def, subscript_type_def,
         expr_type_def]) >>
  gvs[] >> drule_all simulation_probe_counted_target_lookup >>
  disch_then (qspec_then `ARB` strip_assume_tac) >> gvs[] >>
  `!x. p = Var x ==> not_fresh_at sb x` by
    (rpt strip_tac >> irule simulation_probe_pointer_reserved >>
     qexistsl_tac [`(p,SOME LocMemory,SOME (ValPT (BaseT (UintT 256))))`, `sa`] >>
     simp[]) >>
  `target_post ctx fn simulation_probe_cenv cx es sa sb
     s0 (ee with gas_obs := [])
     (PlaceR (MemoryPlace "a" [ValueSubscript (IntV 0)]))
     (Type (BaseT (UintT 256)))
     (p,SOME LocMemory,SOME (value_type_place (Type (BaseT (UintT 256))))) t` by
    (irule simulation_probe_target_post_transport_ctx >> simp[] >>
     irule simulation_probe_zero_place >> simp[]) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL (PlaceR (MemoryPlace "a" [ValueSubscript (IntV 0)]))`,
                 `ee`, `OK t`] >>
  simp[gas_marked_exec_def, gas_explicit_nil] >>
  gvs[exprLoweringTheory.value_type_place_def]
QED

Theorem simulation_probe_target_sim_conditional:
  !fn cx env es ee entry.
    FLOOKUP env.var_types "a" =
      SOME (ArrayT (BaseT (UintT 256)) (Fixed 1)) /\
    lookup_scopes "a" es.scopes = SOME entry /\
    (!tail. eval_base_place cx module_probe_target (es with gas_obs := tail) =
      (INL (PlaceR (MemoryPlace "a" [ValueSubscript (IntV 0)])),
       ee with gas_obs := tail)) /\
    place_readable cx (ee with gas_obs := [])
      (PlaceR (MemoryPlace "a" [ValueSubscript (IntV 0)])) /\
    ee.scopes = es.scopes /\ ee.accounts = es.accounts /\
    ee.tStorage = es.tStorage /\ ee.logs = es.logs /\
    ee.outcomes = es.outcomes /\ ee.requests = es.requests /\
    ee.pending_deletions = es.pending_deletions ==>
    target_sim simulation_probe_context fn simulation_probe_cenv cx env
      module_probe_target es
Proof
  rpt strip_tac >> irule simulation_probe_target_sim_conditional_lookup >>
  simp[simulation_probe_context_lookup] >> qexists_tac `ee` >> simp[]
QED

Theorem simulation_probe_target_sim_conditional_with_caller:
  !caller fn cx env es ee entry.
    caller.fn_name <> simulation_probe_label /\
    FLOOKUP env.var_types "a" =
      SOME (ArrayT (BaseT (UintT 256)) (Fixed 1)) /\
    lookup_scopes "a" es.scopes = SOME entry /\
    (!tail. eval_base_place cx module_probe_target (es with gas_obs := tail) =
      (INL (PlaceR (MemoryPlace "a" [ValueSubscript (IntV 0)])),
       ee with gas_obs := tail)) /\
    place_readable cx (ee with gas_obs := [])
      (PlaceR (MemoryPlace "a" [ValueSubscript (IntV 0)])) /\
    ee.scopes = es.scopes /\ ee.accounts = es.accounts /\
    ee.tStorage = es.tStorage /\ ee.logs = es.logs /\
    ee.outcomes = es.outcomes /\ ee.requests = es.requests /\
    ee.pending_deletions = es.pending_deletions ==>
    target_sim (simulation_probe_context_with_caller caller) fn
      simulation_probe_cenv cx env module_probe_target es
Proof
  rpt strip_tac >> irule simulation_probe_target_sim_conditional_lookup >>
  simp[simulation_probe_context_with_caller_lookup] >>
  qexists_tac `ee` >> simp[]
QED
