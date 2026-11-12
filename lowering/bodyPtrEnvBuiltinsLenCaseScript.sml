(* Composition at the raw value/place boundary, without pointer internals. *)
Theory bodyPtrEnvBuiltinsLenCase
Ancestors
  bodyPtrEnvBuiltinsLenCallResidual bodyPtrEnvBuiltinsLenSuffix bodyPtrEnvBuiltinsLenSource bodyPtrDefs
  gasSummaryComposePtr fragGasPathPtr exprSimDefs exprSimHyps exprSimHypsDefs
  exprLowering exprLoweringProps compileEnv context loweringPosts
  exprSimSource fragGasPath fragGasMode gasSummary exprSimProps
  exprSimUnwrap fragExec vyperTypeInvariants
  bodyPtrEnvBuiltinsBoundary bodyPtrPreds builtinSimple vyperContext
  vyperState vyperInterpreter vyperAST

Theorem len_marked_ptr_normal:
  gas_marked_exec_ptr D (ctx,func) PG (eval_expr cx e)
    (es,s0,G0,tn0) marks (INL tv) ee G tn (OK t) /\
  result_array_length cx tv (ee with gas_obs := []) = (INL n,ee with gas_obs := []) /\
  gas_path_ptr D 0 ctx func PG G tn t 0 G' tn' (OK t') ==>
  gas_marked_exec_ptr D (ctx,func) PG (eval_expr cx (Builtin ann Len [e]))
    (es,s0,G0,tn0) marks (INL (Value (IntV (&n)))) ee G' tn' (OK t')
Proof
  strip_tac >> rewrite_tac[len_builtin_source] >>
  irule (Q.INST [`right` |-> `[]`] gas_marked_exec_ptr_bind_normal
         |> REWRITE_RULE [listTheory.APPEND_NIL]) >>
  qexistsl_tac [`G`, `ee`, `t`, `tn`, `tv`] >> simp[] >>
  simp[gas_marked_exec_ptr_def, bind_def, return_def] >>
  rpt strip_tac >>
  qspecl_then [`cx`, `tv`, `ee with gas_obs := []`, `tail`]
    mp_tac len_result_length_observation >> simp[]
QED

Theorem len_summary_ptr_compose:
  gas_summary_ptr_at D (ctx,func) PG marks (eval_expr cx e)
    (es,s0,G0,tn0) Q (\res ee gt r. expr_exit res r) /\
  (!res ee G tn t.
    gas_marked_exec_ptr D (ctx,func) PG (eval_expr cx e)
      (es,s0,G0,tn0) marks res ee G tn (OK t) /\
    Q res (ee with gas_obs := []) G tn t ==>
    ?tv n t' G' tn'. res = INL tv /\
      result_array_length cx tv (ee with gas_obs := []) = (INL n,ee with gas_obs := []) /\
      gas_path_ptr D 0 ctx func PG G tn t 0 G' tn' (OK t') /\
      Q' (INL (Value (IntV (&n)))) (ee with gas_obs := []) G' tn' t') ==>
  gas_summary_ptr_at D (ctx,func) PG marks
    (eval_expr cx (Builtin ann Len [e])) (es,s0,G0,tn0) Q'
    (\res ee gt r. expr_exit res r)
Proof
  rewrite_tac[gas_summary_ptr_at_marked] >> strip_tac >> gvs[]
  >- (first_x_assum drule_all >> strip_tac >> gvs[] >>
      drule_all len_marked_ptr_normal >>
      disch_then (qspec_then `ann` assume_tac) >>
      goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `res` >- fs[expr_exit_def] >>
  qexistsl_tac [`INR y`, `es_end`, `G`, `tn`, `r`] >> simp[] >>
  rewrite_tac[len_builtin_source] >>
  irule gas_marked_exec_ptr_bind_exception >> simp[]
QED

Theorem len_outcome_ptr_compose:
  gas_outcome_ptr D tops (ctx,func) PG (eval_expr cx e)
    (es,s0,G0,tn0) Q (\res ee gt r. expr_exit res r) /\
  (!marks res ee G tn t.
    gas_marked_exec_ptr D (ctx,func) PG (eval_expr cx e)
      (es,s0,G0,tn0) marks res ee G tn (OK t) /\
    Q res (ee with gas_obs := []) G tn t ==>
    ?tv n t' G' tn'. res = INL tv /\
      result_array_length cx tv (ee with gas_obs := []) = (INL n,ee with gas_obs := []) /\
      gas_path_ptr D 0 ctx func PG G tn t 0 G' tn' (OK t') /\
      Q' (INL (Value (IntV (&n)))) (ee with gas_obs := []) G' tn' t') ==>
  gas_outcome_ptr D tops (ctx,func) PG
    (eval_expr cx (Builtin ann Len [e])) (es,s0,G0,tn0) Q'
    (\res ee gt r. expr_exit res r)
Proof
  rewrite_tac[gas_outcome_ptr_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      irule len_summary_ptr_compose >> goal_assum (drule_at Any) >>
      first_x_assum (qspec_then `marks` ACCEPT_TAC)) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule len_builtin_exempt_cert >> simp[]
QED

Theorem len_marked_operand_typed:
  expr_body_pre cenv cx env e es /\
  gas_marked_exec_ptr D (ctx,func) PG (eval_expr cx e)
    (es,s0,G0,tn0) marks (INL r) ee G tn (OK t) ==>
  ~t.vs_halted /\
  ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    eval_result_typed (env,cx,ee with gas_obs := []) r (Type (expr_type e)) /\
    (!v. read_result cx r (ee with gas_obs := []) = (INL v,ee with gas_obs := []) ==>
      value_has_type tv v)
Proof
  strip_tac >>
  `gas_marked_exec F (ctx,func) (eval_expr cx e) (es,s0) marks (INL r) ee (OK t)` by
    metis_tac[gas_marked_exec_ptr_exec] >>
  conj_tac
  >- metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL r,ee with gas_obs := [])` by
    (fs[gas_marked_exec_ptr_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  irule expr_body_pre_runtime_typed >> goal_assum (drule_at Any) >>
  simp[] >> qexists_tac `cenv` >> simp[]
QED

Theorem compile_len_singleton_eq_sim_ptr:
  !d ctx PG func cenv cx env ty e es.
    post_value_type cenv e = expr_type e /\
    expr_body_pre cenv cx env (Builtin (BaseT (UintT 256)) Len [e]) es /\
    expr_vv_sim_ptr d ctx PG func cenv cx ty e es ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty
      (Builtin (BaseT (UintT 256)) Len [e]) es
Proof
  rpt gen_tac >> strip_tac >>
  `is_sized_type (expr_type e)` by (drule len_builtin_pre_shape >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >>
     disch_then (qspecl_then [`e`, `es`] mp_tac) >> fs[expr_body_pre_def]) >>
  simp[expr_vv_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  gvs[len_compile_split] >> pairarg_tac >> gvs[] >>
  rename1 `compile_expr cenv ty e sa = (evv,sm)` >>
  Cases_on `compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand evv)
    (case vv_location evv of SOME l => l | NONE => LocMemory) sm` >>
  gvs[as_stack_val_def] >>
  drule_all len_builtin_load_extends >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[expr_body_pre_vv_gas_admissible] >>
  qpat_x_assum `expr_vv_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_ptr_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `evv`, `s0`] mp_tac) >>
  disch_then (qspecl_then [`G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  irule len_outcome_ptr_compose >> goal_assum (drule_at Any) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all len_marked_operand_typed >> strip_tac >>
  `compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand evv)
     (case vv_location evv of SOME l => l | NONE => LocMemory) sm = (q,r)` by simp[] >>
  qpat_assum `post_value_type cenv e = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> assume_tac th) >>
  drule_all len_vv_path_ptr >> disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`n`, `t'`, `G'`, `tn'`] >> simp[expr_type_def, is_word_type_def]
QED

Theorem compile_len_singleton_sim_ptr:
  !d ctx PG func cenv cx env ty e es.
    expr_body_pre cenv cx env (Builtin (BaseT (UintT 256)) Len [e]) es /\
    expr_vv_sim_ptr d ctx PG func cenv cx ty e es ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty
      (Builtin (BaseT (UintT 256)) Len [e]) es
Proof
  rpt gen_tac >> strip_tac >> Cases_on `post_value_type cenv e = expr_type e`
  >- (irule compile_len_singleton_eq_sim_ptr >> rpt conj_tac >>
      TRY (first_assum ACCEPT_TAC) >> qexists_tac `env` >> first_assum ACCEPT_TAC) >>
  irule bodyPtrEnvBuiltinsLenCallResidualTheory.compile_len_singleton_call_sim_ptr >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexists_tac `env` >> first_assum ACCEPT_TAC
QED

Theorem len_builtin_body_ptr_ok:
  !cx ann args.
    (!s'' x t.
      type_check (builtin_args_length_ok Len (LENGTH args)) "Builtin args" s'' =
        (INL x,t) ==> body_expr_ptr_ok cx (HD args)) ==>
    body_expr_ptr_ok cx (Builtin ann Len args)
Proof
  rpt gen_tac >> strip_tac >> irule body_expr_ptr_of_vv >> reverse conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  drule len_builtin_pre_shape >> strip_tac >> gvs[] >>
  `body_expr_ptr_ok cx e` by
    (first_x_assum (qspecl_then [`es`, `es`] mp_tac) >>
     simp[builtin_args_length_ok_def, type_check_def, assert_def,
          return_def]) >>
  irule compile_len_singleton_sim_ptr >>
  conj_tac >- (qexists_tac `env` >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >>
     disch_then (qspecl_then [`e`, `es`] mp_tac) >> fs[expr_body_pre_def]) >>
  fs[body_expr_ptr_ok_def] >> metis_tac[]
QED
