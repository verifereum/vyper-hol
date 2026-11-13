Theory exprSimIfExpWidenedEntry
Ancestors
  exprSimProps exprSimDefs stmtSimDefs loweringPosts exprLoweringProps compileEnv loweringStateRelDefs

(* Interface probe: the runtime simulation entry supplies the pointer
   existence invariant needed for reverse region transport. *)
Theorem simulation_entry_local_regions:
  stmt_state_rel ctx func ce cx es s0 /\
  local_ptrs_reserved ce origin /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!x w. not_fresh_at origin x /\ lookup_var x s0 = SOME w ==>
    lookup_var x u = SOME w) ==>
  !n b sz. local_region ce ee.scopes u n b sz ==>
    local_region ce es.scopes s0 n b sz
Proof
  rpt strip_tac >> irule local_region_frame >>
  conj_tac >- (qexists `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
  qexistsl [`origin`, `ee.scopes`, `u`] >> simp[]
QED
