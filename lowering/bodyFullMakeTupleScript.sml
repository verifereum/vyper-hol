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
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`, `PG` |-> `PG`,
    `ann` |-> `TupleT tys`, `elem_opt` |-> `NONE`, `bnd` |-> `n`]
    make_array_init_full) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`q`,`w`,`si`,`Gi`,`tni`] strip_assume_tac) >>
  `u = Var q /\ su = Var q` by metis_tac[compiler_make_tuple_result] >> gvs[] >>
  suspend "loop"
QED

Resume make_tuple_vv_sim_full_conditional[loop]:
  `LIST_REL (\ty tv. type_memory_bytes cenv ty = type_memory_size tv) tys tvs` by
    (drule vyperTypeABITheory.OPT_MMAP_LIST_REL >>
     match_mp_tac listTheory.LIST_REL_mono >> rpt strip_tac >>
     metis_tac[expr_sim_inv_memory_size]) >>
  `ci_mono shadow_sa ssm /\ ci_mono ssm shadow_sb` by
    metis_tac[ci_mono_compile_alloc_buffer,ci_mono_compile_make_tuple_cfn,
      compile_expr_ci_mono,pairTheory.SND] >>
  `fn_has_code ssm shadow_sb shadow_func` by
    (irule (cj 2 fragExecTheory.fn_has_code_split) >>
     conj_tac >- fs[ci_mono_def] >> qexists `shadow_sa` >> fs[ci_mono_def]) >>
  mp_tac (Q.INST [`csbase` |-> `sa`, `ebase` |-> `es`, `sbase` |-> `s0`,
    `Gbase` |-> `G0`, `tnbase` |-> `tn0`, `aid` |-> `sa.cs_next_id`,
    `base` |-> `w2n (w:256 word)`, `cap` |-> `type_memory_size_list tvs`]
    make_array_loop_full) >>
  disch_then (qspecl_then [`args`,`tys`,`tvs`,`0`,`[]`,`sm`,`sb`,
    `ssm`,`shadow_sb`,`es`,`si`,`Gi`,`tni`] mp_tac) >>
  (impl_tac >-
    (fs[ci_mono_def] >> rpt conj_tac >> rpt strip_tac >> simp[]
     >- (qpat_x_assum `!name b len. local_region _ _ _ name b len ==> _` irule >>
         goal_assum (drule_at Any)))) >>
  strip_tac >>
  drule_at Any (Q.INST [
    `f` |-> `\rr. case rr of INL vs => INL (Value (ArrayV (TupleV vs))) | INR ex => INR ex`]
    (INST_TYPE [beta |-> ``:value list``, alpha |-> ``:eval_result``]
      gas_outcome_full_source_map)) >>
  disch_then (qspec_then
    `eval_expr cx (Builtin (TupleT tys) (MakeArray NONE n) args)` mp_tac) >>
  (impl_tac >-
    (simp[] >> gen_tac >>
     Cases_on `eval_exprs cx args es'` >>
     drule aggregate_eval_make_tuple >> simp[])) >>
  strip_tac >>
  irule gas_outcome_full_zero_prefix >>
  qexistsl_tac [`Gi`,`si`,`tni`] >> simp[] >>
  irule gas_outcome_full_post_source >>
  goal_assum (drule_at Any) >>
  conj_tac >- suspend "package" >>
  BETA_TAC >> rpt strip_tac >>
  gvs[oneline exprSimDefsTheory.expr_exit_def,exprSimDefsTheory.halt_exit_def,
      AllCaseEqs()]
QED

Resume make_tuple_vv_sim_full_conditional[package]:
  BETA_TAC >> rpt strip_tac >> gvs[] >>
  rpt (qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac) >>
  `eval_expr cx (Builtin (TupleT tys) (MakeArray NONE n) args)
     (es with gas_obs := xs) = (INL (Value (ArrayV (TupleV vs))),ee)` by
    (qpat_x_assum `!tail. _ = _` (qspec_then `[]` mp_tac) >>
     simp[evaluation_state_component_equality]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_size_list tvs))] [q])
      (fn_insts func)` by
    (qpat_assum `compile_alloc_buffer _ sa = _`
       (mp_tac o MATCH_MP abi_builtin_alloc_buffer_shape) >> strip_tac >>
     drule emitted_insts_emit_op >> simp[] >> strip_tac >> gvs[]) >>
  `!name b len. local_region cenv es.scopes si name b len <=>
     local_region cenv es.scopes s0 name b len` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >>
     qexists `sa` >> simp[]) >>
  `make_array_completed H (DF H) lo d ctx func cenv cx env
    (Builtin (TupleT tys) (MakeArray NONE n) args) es sa sm sb s0 si
    G0 tn0 ee (ArrayV (TupleV vs)) (TupleTV tvs) (w2n (w:256 word))
    (type_memory_size_list tvs) q G' tn' t xs` by
    (simp[make_array_completed_def,vyperASTTheory.expr_type_def,lowered_value_type_def,
          is_word_type_def,type_memory_size_def,valueEncodingDefsTheory.val_in_memory_def] >>
     conj_tac >-
       (rpt strip_tac >>
        qpat_x_assum `!name b n. local_region cenv ee.scopes t name b n ==> _` drule >>
        simp[]) >>
     qpat_x_assum `EVERY _ args ==> _` mp_tac >> simp[]) >>
  qpat_x_assum `make_array_packaging_ok` mp_tac >>
  rewrite_tac[make_array_packaging_ok_def] >>
  disch_then drule >>
  simp[post_value_type_def,vyperASTTheory.expr_type_def]
QED

Finalise make_tuple_vv_sim_full_conditional
