(* Composition transports the protected frame, not merely the ghosts. *)
Theory bodyPtrEnvBuiltinsGhostCompose
Ancestors
  bodyPtrDefs exprSimProps exprLoweringProps compileEnv
  venomState finite_map pred_set list

Theorem ghost_kept_frame_trans:
  ghost_kept cenv es0 sa G0 tn0 s0 G1 tn1 /\
  ghost_kept cenv es1 sb G1 tn1 s1 G2 tn2 /\
  (!x. not_fresh_at sa x ==> not_fresh_at sb x) /\
  sa.cs_next_id <= sb.cs_next_id /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
    aid < sa.cs_next_id ==> FLOOKUP s1.vs_allocas aid = SOME (off,sz)) /\
  (!n b sz. local_region cenv es0.scopes s0 n b sz <=>
             local_region cenv es1.scopes s1 n b sz) ==>
  ghost_kept cenv es0 sa G0 tn0 s0 G2 tn2
Proof
  pure_rewrite_tac[ghost_kept_def] >> strip_tac >> conj_tac
  >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >>
      `aid < sb.cs_next_id` by decide_tac >>
      `FLOOKUP s1.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
      `!n b sz'. local_region cenv es1.scopes s1 n b sz' ==>
         off + sz <= b \/ b + sz' <= off` by metis_tac[] >>
      `i IN tn1.t_mem` by metis_tac[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem ghost_kept_locals_trans:
  ghost_kept cenv es0 sa G0 tn0 s0 G1 tn1 /\
  ghost_kept cenv es1 sb G1 tn1 s1 G2 tn2 /\
  (!x. not_fresh_at sa x ==> not_fresh_at sb x) /\
  sa.cs_next_id <= sb.cs_next_id /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
    aid < sa.cs_next_id ==> FLOOKUP s1.vs_allocas aid = SOME (off,sz)) /\
  local_ptrs_rel ctx cenv es0.scopes s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es0.scopes = MAP FDOM es1.scopes /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x s1 = SOME w) ==>
  ghost_kept cenv es0 sa G0 tn0 s0 G2 tn2
Proof
  strip_tac >>
  `!n b sz. local_region cenv es0.scopes s0 n b sz <=>
             local_region cenv es1.scopes s1 n b sz` suffices_by
    metis_tac[ghost_kept_frame_trans] >>
  rpt gen_tac >> eq_tac
  >- (strip_tac >> irule local_region_frame_fwd >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  metis_tac[local_region_frame]
QED
