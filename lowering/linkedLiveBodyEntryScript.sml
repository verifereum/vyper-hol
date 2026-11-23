(* Internal calls reached from the selected linked body stay in its call closure. *)
Theory linkedLiveBodyEntry
Ancestors
  linkedBodyLoopCalls constSubstMods vyperTypeContract vyperTypeCallGraph
  vyperTypeCallGraphSoundness list

val _ = Parse.hide "body";

Theorem checked_live_body_subst_calls_mods:
  check_contract mode layouts addr mods = SOME artifact /\
  MEM (src,tops) mods /\
  MEM (FunctionDecl vis mut nr rr fn args dflts ret body) tops /\
  MEM (src,fn) (vyperTypeContract$linked_live_functions mods exps) ==>
  EVERY (\k. MEM k (vyperTypeContract$linked_live_functions mods exps))
    (int_calls_stmts (subst_consts_stmts_mods (consts_env_mods mods) body))
Proof
  strip_tac >> drule_then strip_assume_tac checked_subst_consts_int_calls_mods >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  `MEM k (function_int_calls dflts body)` by simp[function_int_calls_def, MEM_APPEND] >>
  `MEM ((src,fn),k) (contract_call_edges mods)` by
    drule_all_then ACCEPT_TAC contract_call_edges_function >>
  qpat_x_assum `MEM (src,fn) (linked_live_functions mods exps)` mp_tac >>
  PURE_REWRITE_TAC [linked_live_functions_def, linked_live_functions_from_def, LET_THM] >>
  BETA_TAC >> strip_tac >> irule (cj 2 call_closure_from_roots) >>
  qexists_tac `(src,fn)` >> simp[call_edge_rel_def]
QED
