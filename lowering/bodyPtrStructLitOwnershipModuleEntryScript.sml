Theory bodyPtrStructLitOwnershipModuleEntry
Ancestors bodyPtrStructLitOwnershipModuleParams loweringShapeProps

(* Internal-entry interface audit.
   The following ShapeProps interfaces are local, not exported:
   - compile_internal_param_decls_shape: shape_step T with pre T, post
     EVERY (\(name,is_stack,op). plain_operand st op) (FST result).
   - internal_cenv_install_shape: static cenv, optional plain return buffer,
     and retpc_operand pc imply shape for the installed PtrVar return PC
     and converted return-buffer slot.
   - materialize_internal_params_shape: cenv_shape_ok and EVERY captured
     operand plain imply cenv_shape_ok of the returned environment and
     preservation of ce_return_pc. Its Finalise is [local].
   - compile_internal_imm_alloc_shape: conditional fixed-region allocation
     returns NONE or a plain immutable base.
   - internal_installed_body_suffix_shape: installed cenv shape and a
     return-PC operand, with supported-body exclusion, close the suffix.

   compile_internal_function_shape is exported, but its post is T; it
   does not expose the state/environment immediately before compile_stmts.
   That call uses cenv2 with ce_imm_alloca := imm_opt and
   ce_alloca_locals := T, after materialization, temporary return-region
   allocation, and optional nonreentrant lock.

   The attempted materialization ownership/shape join cannot reference
   materialize_internal_params_shape from this theory. New task-owned
   shape interfaces are needed; non-owned ShapeProps is not modified.
   This audit is not a certificate for internal entry or module ownership. *)

(* Selected consumer contract audit (C1.contract).
   The unit-facing allocation ownership theorem is NOT yet written.
   body_frame_compiled_context gives lower_vyper_runtime_unit or
   lower_vyper_deploy_unit and lookup of the running function. Their raw
   runners (vyperCompiler.run_lowering / run_deploy_lowering) start at
   initial_compile_state, execute compile_generate_runtime / deploy, and
   call extract_context_with_internals. The existing OwnershipExtraction
   transfer needs alloc_writers_unique of that final compiler state.
   Thus the unit proof needs alloc_run, not a path-local freshness claim.

   Proposed bounded contracts (all are obligations, not declarations):
   - guarded body: ce_alloca_locals and body exclusion imply alloc_run
     (shape_state s /\ cenv_shape_ok s ce) of compile_guarded_body,
     with fresh_outputs post. External function composes the already
     exported positional registration shape/mode join with this contract;
     fallback adds only the payable-check prefix.
   - internal function: cenv_static_ok ce and body exclusion imply
     alloc_run shape_state of compile_internal_function with fresh_outputs
     post. No runnable cenv_shape_ok premise is imposed on the static
     internal MemLoc return-PC environment. The entry must establish it.
   - deploy generator: noninternal runnable static constructor environment,
     ce_alloca_locals, constructor body exclusion, and the internal-function
     contracts imply alloc_run shape_state with fresh_outputs post.
     Constructor registration uses DLOAD, not the calldata-only shape
     theorem. No-constructor deploy still emits an allocation and return.

   Exact statement callback, already proved by conjunct 2 of
   alloc_run_compile_stmt_route_mutual:
     ce.ce_alloca_locals /\ loop_ctx_shape_ok lc /\
     ~supported_stmts_expr_exists expr_shape_root body ==>
     alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
       (compile_stmts ce lc ty body) (\u s. fresh_outputs s).
   NoLoop discharges the loop premise. Internal callback ce is exactly
   cenv2 with ce_imm_alloca := imm_opt and ce_alloca_locals := T;
   ty is the optional return type or BaseT BoolT. Deploy callback ce is
   registered cenv with ce_ctor_exit_label := SOME exit_lbl; ty is NoneT.

   Minimal dependency map:
   * PARAM return buffer: emit_op ownership exists; need framed plain
     operand through capture, RETPC and optional immutable reservation.
   * capture: alloc_run_internal_param_capture is exported.
   * RETPC_PARAM: emit_op ownership exists, but ordinary shape emit_op
     excludes RETPC_PARAM; dedicated retpc shape plus framing is missing.
   * optional fixed-region allocation: shape result exported by
     structlit_compile_internal_imm_alloc_shape; ownership join missing.
   * install: structlit_internal_cenv_install_shape is exported; retain
     captured plain operands, return PC and immutable base at this point.
   * materialize: alloc_run_internal_param_materialization is exported;
     its return-PC equality does not by itself frame the immutable base.
   * temporary return buffer: alloc_run_compile_alloc_buffer_shape exists;
     preserve cenv_shape_ok, retpc_operand and optional immutable operand.
   * lock: unlock ownership exists; lock ownership/shape framing still
     needs a boundary before invoking the statement callback.
   * body: use the callback above and independently join compile_stmt_shape
     when suffix fresh_outputs/retpc shape requires it.
   * suffix: comp_get tests block_is_terminated; terminated branch returns,
     fallthrough unlocks and emits RET [return_pc] for NONE or INVALID for
     SOME. RET shape is not ordinary emit_op shape; emit_inst ownership
     applies without claiming a post-body environment from post T.

   Runtime uses Linear dispatch under lowering_policy_ok, external body
   list, optional fallback and internal body list (moduleLowering:785-821).
   Deploy uses payable check, immutable region, DLOAD registration, lock,
   constructor body, common exit block, unlock, epilogue and constructor
   internal list (825-873). All are necessary because body_inv permits
   runtime/deploy and lookup of any packaged internal function. Kwarg/common
   body routines are not called by these generators; supported classified
   headers force defaults=[] (OwnershipSources), so no default recursion
   is needed. Sources also exports body exclusion for all four selections.

   Independent unresolved cut: even complete alloc_writers_unique after
   extraction proves only writer identity, not that a successful runtime
   path crosses the ALLOCA before the supplied endpoint. This audit gives
   no dominance certificate and does not reopen suffix confinement.
   Admission inventory: scoped grep of bodyPtrStructLit*Script.sml finds
   only bodyPtrStructLitScript.sml:21 (the frozen target proof); no helper
   cheat found. This comment is an audit, not module or unit certification. *)
