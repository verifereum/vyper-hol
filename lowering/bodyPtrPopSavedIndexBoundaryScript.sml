Theory bodyPtrPopSavedIndexBoundary
Ancestors
  bodyPtrPopRegionInvariant bodyPtrDefs loweringPosts venomState

(* A saved storage operand across a successful index fragment.  expr_post
   includes the complete endpoint stmt_state_rel, not a free ghost endpoint.
   The additional liveness premise is explicit: this tests the live branch,
   and does NOT assert that index effects preserve saved-place liveness. *)
Theorem pop_saved_index_live_storage:
  expr_post ctx func cenv cx e es sa sb s0 ee v op s /\
  ghost_inv d cenv cx ee G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME w /\
  op_taint tn0 (Var x) = {} /\
  s.vs_call_ctx.cc_address = cx.txn.target /\
  p.ptr_operand = Var x /\ p.ptr_location = LocStorage /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  storage_read_live cx F (s.vs_accounts cx.txn.target).storage w tv ==>
  ptr_vv_ok cx t result (LocatedValue t' p) ee G tn s
Proof
  strip_tac >>
  `lookup_var x s = SOME w` by metis_tac[expr_post_def] >>
  `op_taint tn (Var x) = {}` by metis_tac[ghost_kept_def] >>
  `pop_region_taint_ok (s.vs_accounts cx.txn.target).storage
      (w2n w) tv tn.t_stor` by
    (irule pop_region_taint_storage_entry >>
     gvs[ghost_inv_def] >> metis_tac[]) >>
  gvs[ptr_vv_ok_def, eval_operand_def, pop_region_taint_ok_def] >>
  metis_tac[]
QED

(* Interface audit (not extra hypotheses for pop_expr_ptr_ok):
   - NameTarget/TopLevelNameTarget have no index premise. S1 splits these
     in body_pop_case; compile_pop_name_case supplies ordinary simulation,
     not a counted pointer path. Runtime pointer paths are still needed.
   - pop_target_index_ptr_premise in bodyPtrPopTargetFactor supplies the
     index body_expr_ptr_ok from body_base_target_ptr_ok and source base
     success. target_pre_of_pop supplies the S1 target precondition from
     body_inv and expr_body_pre (bodyPopNestedTargetFrag).
   - The index expr_sim_ptr post gives expr_post, ghost_inv and ghost_kept.
     The theorem above transports the saved operand and obtains its local
     storage taint bound IF storage_read_live still holds at that cut.
     expr_post's stmt_state_rel includes lookup_function through alloca_room;
     this is not an arbitrary caller or an unframed ghost projection.
   - Missing for a saved child made globally dead by index effects:
       pop_region_taint_ok st0 base tv tn0.t_stor ==>
       pop_region_taint_ok st1 base tv tn1.t_stor
     along the actual counted index path, together with raw header agreement
     on the saved child's old length. The transient case is analogous.
     ghost_kept constrains old variables and memory, not storage taint.
     stmt_state_rel and stor_taint_ok constrain globally live storage only.
     Full code-context membership has NOT been shown to imply this frame.
   - pop_region_taint_trace_transport is conditional on each edge already
     preserving the observer. pop_region_taint_sstore_transport exposes both
     retained-byte and new-byte obligations. Neither proves compatibility
     for arbitrary typed writes or INVOKE. Adopting CALL resets taint, but
     that does not cover INVOKE's callee writes or saved raw header agreement.
   - S1's exprSimPopNestedStorageEffectful explicitly leaves
     pop_nested_storage_effectful_dead_case admitted pending the shared
     dead-slot frame; it cannot be used as proof of the pointer observer.
   - At the final pop suffix nested_pop_suffix_shape lists load, two
     ISZERO, ASSERT, SUB, store, ADD, MUL, ADD. A successful path needs the
     local child taint bound BEFORE the header store; dead_bytes_frame
     handles the store missing that child's slots. Existing
     pop_saved_child_taint_header and pop_saved_storage_ptr_at_base cover
     that final local step conditionally. Empty arrays need an abort path.
     Memory results additionally need coverage and ptr_mem_ok; word outputs
     need no provenance. expr_sim_ptr_of_vv is the final unwrap interface.
   This audit identifies an operational proof obligation, not a verified
   counterexample and not permission to strengthen the frozen theorem. *)
