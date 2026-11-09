(* Runtime consistency supplies parameter well-formedness directly, without
   an assignability premise on the source signature. *)
Theory bodyIntCallProducerBounds
Ancestors
  bodyIntCallProducerSemantic exprSimSource vyperTypeInvariants vyperTypeSystem

Theorem consistent_var_types_well_formed:
  env_consistent env cx es ==>
  !n ty. FLOOKUP env.var_types n = SOME ty ==>
    well_formed_type env.type_defs ty
Proof
  rpt strip_tac >> drule_all env_consistent_var_type_evaluates >>
  fs[env_consistent_def, env_context_consistent_def, well_formed_type_def]
QED
