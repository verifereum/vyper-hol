Theory concretizeLayoutResolvedPositions
Ancestors concretizeLayoutPositions frameResolvedTrace frameActivationCache
  frameJointTransition o1PassContract ptrDiscipline venomWf venomState
  staticLayoutDefs words list

Theorem concretize_positions_resolved_live:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\ fixed_region_reserved lo C /\
  joint_config_reachable vs0 C
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
  LENGTH ids = SUC (LENGTH stk) /\
  resolved_live ids ((fn,s.vs_allocas)::
    MAP (\f. (f.cf_fn,f.cf_state.vs_allocas)) stk) ((token,aid),(b,sz)) ==>
  ?k owner. k < LENGTH ids /\ EL k ids = token /\
    activation_cache (JointConfig stk PG G tn fn inst s oms om hs h)
      (LENGTH stk-k) owner aid (b,sz) /\
    concretize_positions C' owner aid + sz < dimword (:256) /\
    (0 < sz ==> lo <= concretize_positions C' owner aid /\
      EVERY (reserved_intervals_disjoint (concretize_positions C' owner aid,sz))
        C.ctx_global_reserved)
Proof
  strip_tac >> drule_all resolved_live_activation_cache >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  drule_all concretize_positions_activation_numeric >> strip_tac >>
  qexistsl_tac [`k`, `owner`] >> simp[] >> strip_tac >>
  drule_all concretize_positions_activation_lower_bound >> simp[]
QED
