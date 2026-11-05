(* Counted declaration setup and the explicit not-yet-live pointer frame. *)
Theory annAssignPtrSetup
Ancestors
  annAssignPtrFacts bodyPtrDefs allocationPtr fragGasSeqPtr
  exprSimProps loweringPosts finite_map

Theorem annassign_declared_pointer_after_rhs_ptr:
  !cenv es sa G0 tn0 s0 G tn s p sz.
    ghost_kept cenv es sa G0 tn0 s0 G tn /\
    not_fresh_at sa p /\ lookup_var p s = lookup_var p s0 /\
    ptr_covers G0 tn0 p s0 sz ==>
    ptr_covers G tn p s sz
Proof
  rw[ghost_kept_def, ptr_covers_def] >> metis_tac[]
QED

Theorem annassign_expr_pointer_frame_ptr:
  !ctx func cenv cx e es sa sb s0 es' v op s G0 tn0 G tn p sz aid b.
    expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
    ghost_kept cenv es sa G0 tn0 s0 G tn /\ not_fresh_at sa p /\
    ptr_covers G0 tn0 p s0 sz /\
    FLOOKUP s0.vs_allocas aid = SOME (b,sz) ==>
    ptr_covers G tn p s sz /\ FLOOKUP s.vs_allocas aid = SOME (b,sz)
Proof
  rw[expr_post_def, ghost_kept_def, ptr_covers_def] >> metis_tac[]
QED

Theorem annassign_vv_pointer_frame_ptr:
  !ctx func cenv cx e es sa sb s0 es' tv vv s G0 tn0 G tn p sz aid b.
    vv_post ctx func cenv cx e es sa sb s0 es' tv vv s /\
    ghost_kept cenv es sa G0 tn0 s0 G tn /\ not_fresh_at sa p /\
    ptr_covers G0 tn0 p s0 sz /\
    FLOOKUP s0.vs_allocas aid = SOME (b,sz) ==>
    ptr_covers G tn p s sz /\ FLOOKUP s.vs_allocas aid = SOME (b,sz)
Proof
  rw[vv_post_def, ghost_kept_def, ptr_covers_def] >> metis_tac[]
QED
