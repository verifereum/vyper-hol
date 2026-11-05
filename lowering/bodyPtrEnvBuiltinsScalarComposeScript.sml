(* Scalar suffixes retain the original protected frame. *)
Theory bodyPtrEnvBuiltinsScalarCompose
Ancestors
  bodyPtrEnvBuiltinsScalar bodyPtrEnvBuiltinsGhostCompose bodyPtrDefs
  exprLoweringProps stmtFragPtr compileEnv venomState finite_map list

Theorem scalar_frame_kept_trans:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  ghost_kept cenv es sm G tn s G' tn' /\
  (!x. not_fresh_at sa x ==> not_fresh_at sm x) /\
  sa.cs_next_id <= sm.cs_next_id /\
  s.vs_allocas = s0.vs_allocas /\
  local_ptrs_rel ctx cenv es.scopes s0 /\ local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x s0) ==>
  ghost_kept cenv es sa G0 tn0 s0 G' tn'
Proof
  strip_tac >>
  `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
    aid < sa.cs_next_id ==> FLOOKUP s.vs_allocas aid = SOME (off,sz)` by simp[] >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
    lookup_var x s = SOME w` by metis_tac[] >>
  `MAP FDOM es.scopes = MAP FDOM es.scopes` by simp[] >>
  drule_all ghost_kept_locals_trans >> simp[]
QED
