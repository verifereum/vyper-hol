Theory bodyPtrPopStoragePureFrame
Ancestors
  bodyPtrEnvBuiltinsGhostCompose bodyPtrDefs loweringPosts compileEnv
  exprOperandVar exprLoweringProps

Theorem target_post_ghost_kept_compose:
  target_post ctx func cenv cx es0 sa sm s0 es1 pv vt r t /\
  ghost_kept cenv es0 sa G0 tn0 s0 G1 tn1 /\
  ghost_kept cenv es1 sm G1 tn1 t G2 tn2 /\
  ci_mono sa sm /\ local_ptrs_rel func cenv es0.scopes s0 /\
  local_ptrs_reserved cenv sa /\ MAP FDOM es0.scopes = MAP FDOM es1.scopes ==>
  ghost_kept cenv es0 sa G0 tn0 s0 G2 tn2
Proof
  strip_tac >> irule ghost_kept_locals_trans >>
  conj_tac >- simp[] >>
  conj_tac >- (qexists `func` >> simp[]) >>
  qexistsl [`G1`, `es1`, `t`, `sm`, `tn1`] >>
  fs[target_post_def, ci_mono_def] >>
  metis_tac[compiler_ci_mono_not_fresh, ci_mono_def]
QED
