(* Index effects may change a local's value while retaining its address. *)
Theory bodyPtrSubscriptIndexRefresh
Ancestors
  bodyPtrSubscriptLocalAlias bodyPtrSubscriptBoundary loweringPosts
  exprLoweringProps bodyPtrDefs compileEnv

Theorem expr_post_local_pointer:
  expr_post ctx func cenv cx idx es sa sb s0 es' iv iop s /\
  local_ptrs_reserved cenv sa /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s0 = SOME w ==>
  lookup_var p s = SOME w
Proof
  rw[expr_post_def, local_ptrs_reserved_def] >>
  `not_fresh_at sa p` by metis_tac[] >>
  metis_tac[]
QED

Theorem expr_post_local_representation:
  expr_post ctx func cenv cx idx es sa sb s0 es' iv iop s /\
  local_ptrs_reserved cenv sa /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s0 = SOME w /\
  lookup_scopes name es'.scopes = SOME entry ==>
  val_in_memory entry.type entry.value (w2n w) s.vs_memory
Proof
  strip_tac >>
  drule_all expr_post_local_pointer >> strip_tac >>
  irule local_ptrs_rel_retained_root >>
  fs[expr_post_def, stmt_state_rel_def, state_rel_def] >>
  metis_tac[]
QED

Theorem expr_post_local_robust_representation:
  expr_post ctx func cenv cx idx es sa sb s0 es' iv iop s /\
  local_ptrs_reserved cenv sa /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s0 = SOME w /\
  lookup_scopes name es'.scopes = SOME entry /\
  ghost_inv d cenv cx es' G tn s /\
  mem_agree_outside tn.t_mem s.vs_memory mem ==>
  val_in_memory entry.type entry.value (w2n w) mem
Proof
  strip_tac >>
  drule_all expr_post_local_pointer >> strip_tac >>
  drule_all ghost_inv_local_representation >> simp[]
QED

(* Coverage itself needs only the later ghost invariant and live scope. *)
Theorem ghost_inv_local_coverage:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_scopes name es'.scopes = SOME entry /\
  ghost_inv d cenv cx es' G tn s ==>
  ptr_covers G tn p s sz
Proof
  simp[ghost_inv_def] >> metis_tac[]
QED
