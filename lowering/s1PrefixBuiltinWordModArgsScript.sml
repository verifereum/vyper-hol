(* Request prefixes for modular builtins come entirely from their operands. *)
Theory s1PrefixBuiltinWordModArgs
Ancestors
  s1PrefixPreds s1PrefixOfVV s1PrefixDefs bodyFullWordArgs exprBodyPreProps
  exprSimSource exprSimWordBuiltins exprSimWordArgs exprLoweringProps
  vyperTyping vyperTypeSystem vyperInterpreter vyperContext vyperState
  builtinMath compileEnv fragExec gasShadowState list pair

Theorem modular_word_args_fragment[local]:
  (bt = AddMod \/ bt = MulMod) /\
  lower_value compile_expr cenv ty (Builtin ann bt [a;b;m]) sa = (op,sb) /\
  fn_has_code sa sb func ==>
  ?xs sm. lower_word_args cenv (\e. ty) [a;b;m] sa = (xs,sm) /\
    fn_has_code sa sm func
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule_all lower_value_ternary_modular >> strip_tac >>
  `lower_word_args cenv (\e. ty) [a;b;m] sa = ([x;y;z],s3)` by
    simp[lower_word_args_def, comp_bind_def, comp_return_def] >>
  `cs_extends sa s3` by
    (drule ci_mono_lower_word_args >> simp[ci_mono_def]) >>
  `cs_extends s3 sb` by
    (`cs_appends ((if bt = AddMod then compile_addmod else compile_mulmod) x y z)` by
       (Cases_on `bt = AddMod` >> simp[compile_addmod_def, compile_mulmod_def] >>
        irule cs_appends_ignore_bind >> simp[cs_appends_emit_helpers]) >>
     fs[cs_appends_def]) >>
  metis_tac[fn_has_code_split]
QED

Theorem modular_word_args_state[local]:
  (bt = AddMod \/ bt = MulMod) /\ LENGTH args = 3 ==>
  !qe. SND (bind (eval_expr cx (Builtin ann bt args)) (read_result cx) qe) =
       SND (eval_exprs cx args qe)
Proof
  strip_tac >>
  `bind (eval_expr cx (Builtin ann bt args)) (read_result cx) =
   bind (eval_exprs cx args)
     (\vs ee. (builtin_result cx ee.accounts ann bt (MAP expr_type args) vs,ee))` by
    (irule eval_expr_builtin_action >>
     gvs[builtin_args_length_ok_def, code_slice_source_def,
         precompile_builtin_def, is_self_codesize_def]) >>
  gen_tac >> simp[] >> Cases_on `eval_exprs cx args qe` >>
  rename1 `_ = (res,ee)` >> Cases_on `res` >> simp[bind_def]
QED

Theorem modular_sim_prefix_of_word_args:
  (!todo DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx tyf
    es st0 sa sm shadow_sa shadow_sm xs s0 G0 tn0.
    (!e. tyf (gas_shadow_expr e) = tyf e) /\
    (!e ee. MEM e todo /\ expr_sim_inv cenv cx env ee ==>
      expr_body_pre cenv cx env e ee /\ is_word_type (expr_type e)) /\
    body_exprs_full_ok cx todo /\
    body_exprs_prefix_ok cx todo /\
    body_inv tops ctx cenv cx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    shadow_body_inv tops ctx shadow_ctx /\ expr_sim_inv cenv cx env es /\
    lower_word_args cenv tyf todo sa = (xs,sm) /\
    lower_word_args (gas_shadow_env T cenv) tyf (MAP gas_shadow_expr todo) shadow_sa =
      (xs,shadow_sm) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sm shadow_sm /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_exprs cx todo) (es,s0,G0,tn0)) ==>
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty ann bt args es.
    (bt = AddMod \/ bt = MulMod) /\
    (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_full_ok cx args) /\
    (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_prefix_ok cx args) /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env (Builtin ann bt args) es ==>
    expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann bt args) es /\
    expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann bt args) es
Proof
  disch_then (markerLib.mk_asm "args_prefix") >> rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule expr_body_pre_static_facts >> strip_tac >>
  `MAP expr_type args = [BaseT (UintT 256); BaseT (UintT 256); BaseT (UintT 256)]` by
    (qpat_x_assum `well_typed_expr env (Builtin _ _ _)`
       (strip_assume_tac o PURE_REWRITE_RULE [well_typed_expr_def]) >>
     drule_at Any word_builtin_modular_types >> simp[] >>
     Cases_on `bt = AddMod` >> gvs[]) >>
  `?a b m. args = [a;b;m]` by
    (qpat_assum `MAP expr_type args = _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[MAP_EQ_CONS, MAP_EQ_NIL] >> metis_tac[]) >>
  `builtin_args_length_ok bt (LENGTH args)` by gvs[builtin_args_length_ok_def] >>
  `!e ee. MEM e args /\ expr_sim_inv cenv cx env ee ==>
          expr_body_pre cenv cx env e ee /\ is_word_type (expr_type e)` by
    (rpt gen_tac >> strip_tac >> conj_tac
     >- (drule expr_body_pre_builtin_arg >>
         disch_then (qspecl_then [`e`,`ee`] mp_tac) >> gvs[]) >>
     gvs[is_word_type_def]) >>
  conj_asm1_tac
  >- suspend "value" >>
  irule expr_vv_sim_stack_prefix >> simp[] >> reverse conj_tac
  >- (rpt gen_tac >> disch_tac >> drule eval_expr_builtin_value >> simp[]) >>
  gen_tac >> Cases_on `compile_expr cenv ty (Builtin ann bt [a;b;m]) sa` >>
  drule_at Any compile_word_builtin_stack >> simp[] >>
  disch_then strip_assume_tac >> simp[]
QED

Resume modular_sim_prefix_of_word_args[value]:
  pure_rewrite_tac[expr_sim_prefix_def, expr_sim_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `args = [a;b;m]` SUBST_ALL_TAC >>
  `?xs sm. lower_word_args cenv (\e. ty) [a;b;m] sa = (xs,sm) /\
           fn_has_code sa sm func` by
    (drule_all modular_word_args_fragment >> simp[]) >>
  `?ys shadow_sm. lower_word_args (gas_shadow_env T cenv) (\e. ty)
         (MAP gas_shadow_expr [a;b;m]) shadow_sa = (ys,shadow_sm) /\
         fn_has_code shadow_sa shadow_sm shadow_func` by
    (`gasShadow$gas_shadow_builtin bt = bt` by
       (Cases_on `bt` >> gvs[gasShadowTheory.gas_shadow_builtin_def]) >>
     qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     simp[gasShadowTheory.gas_shadow_expr_def] >> strip_tac >>
     qpat_assum `lower_value _ _ _ (Builtin _ _ [gas_shadow_expr _;_;_]) _ = _`
       (mp_then Any mp_tac modular_word_args_fragment) >>
     disch_then (qspec_then `shadow_func` mp_tac) >> simp[]) >>
  `xs = ys /\ gas_shadow_state sm shadow_sm` by
    (Q.INST [`tyf` |-> `\e. ty`, `cenv` |-> `cenv`] gas_shadow_compiles_lower_word_args |>
     SIMP_RULE (srw_ss()) [gas_shadow_compiles_def] |>
     qspecl_then [`[a;b;m]`,`sa`,`shadow_sa`] mp_tac >> simp[]) >>
  qpat_x_assum `xs = ys` SUBST_ALL_TAC >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (eval_exprs cx [a;b;m]) (es,s0,G0,tn0)` by
    (markerLib.asm "args_prefix" irule >> simp[] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     goal_assum (drule_at (Pat `lower_word_args _ _ [a;b;m] _ = _`)) >>
     qpat_x_assum `lower_word_args _ _ (MAP gas_shadow_expr _) _ = _`
       (assume_tac o REWRITE_RULE [MAP]) >>
     goal_assum (drule_at (Pat `lower_word_args _ _ [gas_shadow_expr _;_;_] _ = _`)) >>
     goal_assum (drule_at (Pat `gas_shadow_function func shadow_func`)) >>
     goal_assum (drule_at (Pat `return_buf_frame _ _ sa s0`)) >>
     goal_assum (drule_at (Pat `body_const_cells_agree _ _ env es`)) >>
     simp[] >> rpt strip_tac >> gvs[is_word_type_def]) >>
  `!qe. SND (bind (eval_expr cx (Builtin ann bt [a;b;m])) (read_result cx) qe) =
        SND (eval_exprs cx [a;b;m] qe)` by (irule modular_word_args_state >> simp[]) >>
  drule gas_prefix_full_state_cong >> simp[]
QED

Finalise modular_sim_prefix_of_word_args
