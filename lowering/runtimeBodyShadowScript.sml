(* The selected external body's shadow placement: the runtime unit's GAS
   shadow (gas_shadow_run_lowering) holds the shadow body's code at the
   compile states paired with the actual body's. *)
Theory runtimeBodyShadow
Ancestors
  runtimeBodyStartDefs gasShadowRunLowering gasShadowUnit gasShadowState
  gasShadow fragExec loweringPosts bodySim supportedStmts compileVyper
  moduleLowering vyperCompiler

val _ = Parse.hide "body";

(* From the pinned start st, the shadow chain runs the spine's per-step
   gas_shadow_compiles results (fresh_label, dispatch,
   compile_external_fn_bodies of the prefix, new_block, entry checks,
   registration, guarded body) from gas_shadow_state_refl, and the shadow
   unit from gas_shadow_run_lowering holds its code at the same labels.

   Intuition:
   - The actual unit is run_lowering's (supported_program excludes
     defaults; lowering_policy_ok forces Linear dispatch), so st, sa, sb,
     st' are its compile states; source_selected_body_code's chain
     (runtime_external_boundary, external_bodies_append/run_shape,
     run_lowering_entry_interval, fn_has_code_split/mid) gives the actual
     fn_has_code facts at these pinned states.
   - gas_shadow_inst is a relation, not a function, so cs_extends does not
     transfer from the actual to the shadow side: the same generic chain
     has to run on the shadow packages, which needs their shapes
     (expr_shape_root is invariant under gas_shadow_expr: Call targets are
     kept and builtin_arity (Env _) = 0).
   - The shadow body at type ret lands where the shadow guarded body's
     compile at (case rt ...) does: stmts_env_ret_ty on the shadow body,
     which needs supported_stmts preserved by gas_shadow_stmt (Env MsgGas
     and Env GasPrice are both supported env builtins) and
     ~stmts_valued_return preserved.
   - The shadow stmts_env pairs with the actual one through a
     gas_shadow_compiles result for stmts_env (FST equal: same cenv').
   - gas_shadow_lookup_function gives the shadow partner of func. *)
Theorem runtime_selected_body_shadow:
  !tops rpolicy unit lbl ce pos mincd pay key ut iv fbody rt st cenv sa st'
   bindings ctx cx env env' ret.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    runtime_selected_body_start tops rpolicy
      (lbl,ce,pos,mincd,pay,F,key,ut,iv,fbody,rt) st /\
    compile_register_positional_args ce pos 4 st = (cenv,sa) /\
    compile_guarded_body cenv F key ut iv fbody rt sa = ((),st') /\
    supported_stmts tops bindings fbody /\ body_inv tops ctx cenv cx /\
    rt = (if ret = NoneT then NONE else SOME ret) /\
    type_stmts env ret fbody = SOME env' ==>
    ?func shadow_ctx shadow_func cenv' sb shadow_sa shadow_sb.
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      gas_shadow_context unit.cu_context shadow_ctx /\
      gas_shadow_function func shadow_func /\
      MEM func unit.cu_context.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      stmts_env cenv NoLoop ret fbody sa = (cenv',sb) /\
      stmts_env cenv NoLoop ret (MAP gas_shadow_stmt fbody) shadow_sa =
        (cenv',shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      fn_has_code sa sb func /\ fn_has_code sb st' func /\
      fn_has_code shadow_sa shadow_sb shadow_func
Proof
  cheat
QED
