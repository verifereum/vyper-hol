(* Joint array-literal execution, conditional only on completed-buffer packaging. *)
Theory bodyFullMakeArrayArray
Ancestors
  bodyFullMakeArrayResultDefs bodyFullMakeArrayInit bodyFullMakeArrayLoop
  bodyInvNoDalloca bodyMemArrayLayout
  exprSimAggregateEncoding exprSimAggregateSource exprSimAggregateLayout
  gasOutcomeFullGuarded gasOutcomeFullStmts gasOutcomeFullCompose
  gasShadowCompileStmtHelpers gasShadowCompileHelpers gasShadowCompileContext
  calldataOverwritePtr bodyFullHashCleanFrame bodyPtrMakeArrayCopyStep
  bodyPtrMakeArrayWordStore exprSimSource exprLoweringProps emitHelperProps
  exprSimHyps exprSimHypsDefs bodySimFull vyperTypeSystem bodyFullPreds

val _ = Parse.hide "base";

Theorem make_array_vv_sim_full_conditional:
  make_array_packaging_ok /\
  (builtin_args_length_ok (MakeArray (SOME et) n) (LENGTH args) ==>
     body_exprs_full_ok cx args) /\
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann (MakeArray (SOME et) n) args) es ==>
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin ann (MakeArray (SOME et) n) args) es
Proof
  strip_tac >>
  `~ctx_has_dalloca ctx` by metis_tac[body_inv_no_dalloca] >>
  `compatible_bound n (LENGTH args)` by
    gvs[expr_body_pre_def,well_typed_expr_def,well_typed_builtin_app_def] >>
  `body_exprs_full_ok cx args` by
    (first_x_assum irule >> simp[vyperContextTheory.builtin_args_length_ok_def]) >>
  `!e ee. MEM e args /\ expr_sim_inv cenv cx env ee ==>
     expr_body_pre cenv cx env e ee` by
    (rpt strip_tac >> irule expr_body_pre_builtin_arg >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`ann`,`args`,`MakeArray (SOME et) n`,`es`] >> simp[]) >>
  rw[expr_vv_sim_full_def] >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (irule gas_outcome_full_bad_intro >>
      qexistsl_tac [`storage_trace_horizon es.storage_trace`,`func`,`G0`,
                    `PG`,`tn0`,`[]`,`s0`] >>
      simp[gasOutcomeFullTheory.gas_origin_ptr_focus_nil] >>
      irule gasStorageTheory.gas_bad_storage_at_initial >>
      simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  drule_all array_body_allocation_layout >> strip_tac >> gvs[] >>
  drule_all (SRULE [] (Q.INST
    [`cap` |-> `type_memory_bytes cenv ann`] make_array_init_full)) >>
  disch_then (qspec_then `gas_explicit_sites ctx shadow_ctx` strip_assume_tac) >>
  cheat
QED
