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

(* Runtime/deploy packaging audit (C1.modules.closure.remaining.integration.packaging).
   This is a consumer inventory, NOT generator certification.

   E0218 supplies alloc_run_compile_internal_function. Guarded supplies external
   and fallback bodies. Their post fresh_outputs alone cannot feed the next
   list element: join each with its existing shape theorem to retain shape_state.
   cenv_static_ok_shape_ok converts static ce with ce_return_pc=NONE to runnable
   ce. External/fallback ownership additionally needs ce_alloca_locals=T; this
   is NOT part of external_fn_shape_ok or fallback_shape_ok. The unit consumer
   must establish that mode from its actual environment builder.

   Proposed list contracts, with tuple arities exactly moduleLowering:756-781:
   EVERY (\(lbl,ce,args,min_cds,pay,nr,key,tr,view,stmts,rt).
     external_fn_shape_ok (lbl,ce,args,min_cds,pay,nr,key,tr,view,stmts,rt) /\
     ce.ce_alloca_locals) exts ==>
   alloc_run shape_state (compile_external_fn_bodies exts)
     (\u s. shape_state s /\ fresh_outputs s).
   EVERY (\(lbl,ce,params,rb,nr,key,tr,view,ctor,ilen,stmts,rt).
     internal_fn_shape_ok (lbl,ce,params,rb,nr,key,tr,view,ctor,ilen,stmts,rt) /\
     internal_label_ok lbl) ints ==>
   alloc_run shape_state (compile_internal_fn_bodies ints)
     (\u s. shape_state s /\ fresh_outputs s).
   The internal new_block boundary must install the exact current label:
   alloc_run_new_block_frame retains shape but does not export that equality.
   Internal labels come from the list premise, NEVER fresh_label.

   Proposed runtime contract: EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) sels,
   the external and internal list premises above, fallback_shape_ok fb, and
   (for SOME (ce,pay,nr,key,tr,view,stmts,rt)) ce.ce_alloca_locals imply
   alloc_run shape_state
     (compile_generate_runtime sels exts ints fb Linear buckets metadata dense info)
     (\u s. shape_state s /\ fresh_outputs s).
   No claim is made for Sparse or Dense. Existing dispatch shape requires
   jump_label_ok target/fallback labels and ~label_sfx "dispatch" fallback.
   fresh_label "fallback" exports compiler_label and label_sfx "fallback";
   label_sfx_distinct supplies the exclusion. A new ownership boundary for
   Linear dispatch and a joined arbitrary-size entry-check boundary are needed;
   alloc_run_payable_check covers only compile_entry_checks 4 pay.

   Proposed deploy contract: if has_ctor then cenv_static_ok ce,
   ce.ce_return_pc=NONE, ce.ce_alloca_locals=T, body exclusion, and the internal
   list premise above; conclude alloc_run shape_state of the exact
   compile_generate_deploy call with post shape_state /\ fresh_outputs.
   If has_ctor=F no constructor/list premises are necessary (list is unused).
   After immutable reservation, exact registration input is
     ce with ce_imm_alloca := (if ilen>0 then SOME imm else NONE).
   ConstructorRegistration exports shape_state, cenv_shape_ok ce',
   ce'.ce_return_pc=ce.ce_return_pc, and unchanged ce_alloca_locals.
   Preserve plain_operand imm by stable framing across registration/lock/body.
   fresh_label "ctor_exit" exports compiler_label, hence jump_label_ok.
   The runnable callback environment is ce' with ce_ctor_exit_label:=SOME lbl.
   deploy_cenv_exit_shape in ctorGeneratorShape proves precisely its shape
   from cenv_shape_ok ce', ce'.ce_return_pc=NONE, jump_label_ok lbl, but is
   LOCAL: it is not an exported reusable rule. Need an owned boundary or a
   direct cenv_shape_ok_def proof once at this constructor boundary. Freshness
   alone cannot discharge it. BodyRun handles NoLoop NoneT and returns shape.

   Finite remaining semantic boundaries: (1) function shape/ownership joins
   and list composition, including exact internal block-label installation;
   (2) Linear dispatch ownership/shape and arbitrary entry checks; (3) optional
   immutable constructor entry plus framed DLOAD registration/exit-label install;
   (4) constructor fallthrough JMP/new_block/unlock/epilogue ownership, preserving
   imm only while required; (5) simple-deploy ownership; (6) runtime/deploy
   assembly using those boundaries. ctorShapeProps already exports epilogue
   shape with plain_operand imm and simple-deploy shape, not ownership.
   Unit transport still must discharge selected tuple premises and allocation
   mode. None of these ownership obligations proves runtime ALLOCA dominance.
*)
