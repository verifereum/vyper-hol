Theory bodyPtrIntCallFrontier
Ancestors bodyPtrIntCallAllocation bodyPtrIntCallConfinement
  exprLoweringProps compileEnv venomMemDefs
  finite_map pred_set arithmetic

(* Both parts of the protected set are bounded at expression entry:
   alloca_next_valid covers arbitrary old entries, not just live locals.
   Transport from entry to the INVOKE frontier is a separate obligation. *)
Theorem intcall_protected_below_frontier:
  stmt_state_rel ctx func cenv cx es s ==>
  !a. s.vs_alloca_next <= a ==>
      a NOTIN intcall_protected cenv es sa s
Proof
  strip_tac >>
  `alloca_next_valid s /\ local_ptrs_rel func cenv es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def, alloca_inv_def] >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ _` kall_tac >>
  gen_tac >> strip_tac >> strip_tac >>
  gvs[intcall_protected_def]
  >- (fs[alloca_next_valid_def] >>
      qpat_x_assum `!aid base sz. _` drule >> decide_tac) >>
  fs[local_ptrs_rel_def, local_region_def] >>
  qpat_x_assum `!name entry p sz. _` drule_all >>
  strip_tac >> gvs[] >> decide_tac
QED

Theorem intcall_protected_setup:
  stmt_state_rel ctx func cenv cx es s /\
  setup_callee fn args s = SOME cs ==>
  intcall_alloc_outside (intcall_protected cenv es sa s) cs
Proof
  strip_tac >> irule intcall_alloc_setup >>
  metis_tac[intcall_protected_below_frontier]
QED
