(* Tuple MakeArray: one allocation and the joint full-H element loop. *)
Theory bodyFullMakeTuple
Ancestors exprSimDefs[qualified,ignore_grammar]
  bodyFullMakeArrayResultDefs bodyFullMakeArrayInit bodyFullMakeArrayLoop
  bodyFullPreds bodySimFull bodyInvNoDalloca bodyMemTupleLayout
  exprSimAggregateLayout exprSimAggregateSource exprSimHyps exprSimHypsDefs exprSimSource
  exprOperandVar exprLoweringProps exprLowering compileEnv
  gasOutcomeFullStmts gasOutcomeFullCompose gasOutcomeFull gasStorage
  gasShadowCompileContext gasShadowState gasShadow
  exprSimCopy abiBuiltinAllocation emitHelperProps valueEncoding
  loweringPosts bodyPtrDefs vyperStorageTrace vyperStorageFootprint
  vyperInterpreter vyperState venomState venomInst

val _ = Parse.hide "base";

Theorem make_tuple_vv_sim_full_conditional:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty ann n args es.
    make_array_packaging_ok /\
    (builtin_args_length_ok (MakeArray NONE n) (LENGTH args) ==>
      body_exprs_full_ok cx args) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin ann (MakeArray NONE n) args) es ==>
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann (MakeArray NONE n) args) es
Proof
  rpt gen_tac >> strip_tac >>
  `~ctx_has_dalloca ctx` by metis_tac[body_inv_no_dalloca] >>
  `expr_sim_inv cenv cx env es /\ compatible_bound n (LENGTH args)` by
    gvs[expr_body_pre_def,vyperTypeSystemTheory.well_typed_expr_def,
        vyperTypeSystemTheory.well_typed_builtin_app_def] >>
  `body_exprs_full_ok cx args` by
    (first_x_assum irule >> simp[vyperContextTheory.builtin_args_length_ok_def]) >>
  `!e ee. MEM e args /\ expr_sim_inv cenv cx env ee ==>
      expr_body_pre cenv cx env e ee` by
    (rpt strip_tac >> irule expr_body_pre_builtin_arg >>
     qpat_assum `expr_body_pre _ _ _ (Builtin _ _ _) _` (irule_at Any) >>
     simp[]) >>
  rewrite_tac[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  simp[evaluate_storage_trace_frame] >> strip_tac >>
  drule_all tuple_body_allocation_layout >> strip_tac >> gvs[] >>
  `type_memory_bytes cenv (TupleT tys) = type_memory_size_list tvs` by
    simp[type_memory_bytes_def] >>
  `?sba ssm su.
    compile_alloc_buffer (type_memory_size_list tvs) shadow_sa = (sba,ssm) /\
    compile_make_tuple compile_expr cenv (MAP gas_shadow_expr args) tys
      sba.buf_operand 0 ssm = (su,shadow_sb)` by
    (qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     simp[gas_shadow_expr_def,gas_shadow_builtin_def,compile_tuple_literal] >>
     Cases_on `compile_alloc_buffer (type_memory_size_list tvs) shadow_sa` >>
     simp[tuple_literal_types_def] >>
     Cases_on `compile_make_tuple compile_expr cenv (MAP gas_shadow_expr args)
       tys q.buf_operand 0 r` >>
     simp[as_ptr_val_def] >> metis_tac[]) >>
  `sba = ba /\ gas_shadow_state sm ssm` by
    (mp_tac (Q.INST [`nbytes` |-> `type_memory_size_list tvs`]
      gas_shadow_compiles_alloc_buffer) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >> gvs[] >>
  mp_tac (Q.INST [`cap` |-> `type_memory_size_list tvs`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`, `PG` |-> `PG`]
    make_array_init_full) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`q`,`w`,`si`,`Gi`,`tni`] strip_assume_tac) >>
  `u = Var q /\ su = Var q` by metis_tac[compiler_make_tuple_result] >> gvs[] >>
  suspend "loop"
QED

Resume make_tuple_vv_sim_full_conditional[loop]:
  cheat
QED

Finalise make_tuple_vv_sim_full_conditional
