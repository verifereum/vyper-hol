(* Default, body, and call guards for the checker's live runtime callees. *)
Theory vyperLiveRuntimeCallableGuards
Ancestors
  list alist finite_map vyperAST vyperTypeContract vyperTypeContractContext
  vyperTypeContractStaticMaps vyperRuntimeWriteSafety vyperCheckedRuntimeWriteSafety
  vyperTypeCallGraph vyperTypeCallGraphSoundness vyperDeployLiveClosure

val guard = ``runtime_write_root (\sid id. ?vt.
  FLOOKUP art.cta_toplevel_vtypes (sid,id) = SOME vt /\
  FLOOKUP art.cta_bare_globals (sid,id) = NONE)``;

Theorem checked_live_runtime_callable_guards:
  check_contract F layouts addr mods = SOME art /\
  MEM (src,fn) (live_functions layouts addr mods) /\
  ALOOKUP mods src = SOME ts /\
  lookup_callable_function F fn ts = SOME (mut,nr,args,ds,ret,b) ==>
  EVERY (expr_writes_ok ^guard) ds /\ stmts_writes_ok ^guard b /\
  EVERY (\k. MEM k (live_functions layouts addr mods)) (function_int_calls ds b)
Proof
  strip_tac >> drule lookup_callable_function_F_SOME_MEM >> strip_tac >>
  `check_function_body layouts addr mods art src Internal mut nr args ds ret b` by
    (irule check_contract_function_body_MEM >>
     simp[function_live_def, check_function_body_in_mode_def] >> metis_tac[]) >>
  drule check_contract_runtime_assignable >> strip_tac >>
  `EVERY (expr_writes_ok ^guard) ds /\ stmts_writes_ok ^guard b` by
    (drule check_function_body_write_roots >> disch_then irule >> simp[] >>
     metis_tac[]) >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  irule (cj 2 deploy_live_functions_closed) >> qexists_tac `(src,fn)` >> simp[] >>
  irule contract_call_edges_function >> metis_tac[ALOOKUP_MEM]
QED
