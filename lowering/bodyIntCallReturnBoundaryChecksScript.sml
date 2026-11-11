Theory bodyIntCallReturnBoundaryChecks
Ancestors
  compileEnv loweringStateRelDefs vyperTypeInvariants finite_map option

(* A shared typing environment fixes the live-name domain, even when
   assignments have changed the entries and the scope-stack shape. *)
Theorem local_region_env_transport:
  env_consistent env cx esA /\ env_consistent env cx esB /\
  local_ptrs_reserved cenv sa /\
  (!x w. not_fresh_at sa x /\ lookup_var x sA = SOME w ==>
         lookup_var x sB = SOME w) ==>
  !n b sz. local_region cenv esA.scopes sA n b sz ==>
           local_region cenv esB.scopes sB n b sz
Proof
  simp[env_consistent_def, env_scopes_consistent_def] >>
  rpt strip_tac >>
  qpat_x_assum `local_region _ _ _ _ _ _` mp_tac >>
  simp[local_region_def] >> strip_tac >>
  `IS_SOME (FLOOKUP env.var_types n)` by metis_tac[] >>
  `IS_SOME (lookup_scopes n esB.scopes)` by
    (Cases_on `FLOOKUP env.var_types n` >> gvs[] >> metis_tac[]) >>
  `not_fresh_at sa p` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  Cases_on `lookup_scopes n esB.scopes` >> gvs[] >>
  metis_tac[]
QED
