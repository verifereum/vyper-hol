(* The selected external body's shadow placement: the runtime unit's GAS
   shadow (gas_shadow_run_lowering) holds the shadow body's code at the
   compile states paired with the actual body's. *)
Theory runtimeBodyShadow
Ancestors
  runtimeBodyStartDefs gasShadowRunLowering gasShadowUnit gasShadowState
  gasShadow fragExec loweringPosts bodySim supportedStmts compileVyper
  moduleLowering vyperCompiler

val _ = Parse.hide "body";

(* STAGED HEADER: proof pending.  From the pinned start st, the shadow
   chain runs the spine's per-step gas_shadow_compiles results (dispatch,
   compile_external_fn_bodies of the prefix, new_block, entry checks,
   registration, guarded body), and the shadow unit from
   gas_shadow_run_lowering holds its code at the same labels. *)
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
