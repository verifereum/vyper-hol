(* Pair the linked constructor's body interval with the shadow compilation. *)
Theory linkedConstructorBodyShadowCode
Ancestors
  linkedDeployConstructorCode gasShadowDeployRunner gasShadowUnit
  gasShadowUnitGuards gasShadowUnitExtract gasShadowDeployRegisterEnv
  gasShadowCompileBase gasShadowStmtEnv gasShadowCompileStmtBase
  gasShadowState gasShadow moduleLowering compileVyper compileEnv
  stmtSimProps vyperCompiler venomInst fragExec list pair option

Theorem linked_constructor_body_shadow_code:
  ce0.ce_nonreentrant = (F,key,ut,F) /\
  run_deploy_lowering T rp runtime_bc cap args 0 ifns ce0 stmts
    pay F key ut "__deploy" = SOME unit /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ifns) /\
  venomInst$lookup_function "__deploy" unit.cu_context.ctx_functions = SOME fn /\
  (if pay then comp_return () else
    comp_bind (emit_op CALLVALUE []) (\cv.
      comp_bind (emit_op ISZERO [cv]) (\v. emit_void ASSERT [v])))
    (initial_compile_state "__deploy") = ((),st_pay) /\
  (if cap > 0 then
     comp_bind (compile_fixed_region_with_id cap)
       (\r. comp_return (SND r).buf_operand)
   else comp_return (Lit 0w)) st_pay = (imm,st1) /\
  compile_register_constructor_args
    (ce0 with ce_imm_alloca := (if cap > 0 then SOME imm else NONE))
    args 0 0 st1 = (ce1,st2) /\
  fresh_label "ctor_exit" st2 = (exit_lbl,sa) /\
  ce = ce1 with ce_ctor_exit_label := SOME exit_lbl /\
  compile_stmts ce NoLoop NoneT stmts sa = ((),sb) ==>
  ?shadow_unit shadow_fn shadow_sb.
    run_deploy_lowering T rp runtime_bc cap args 0
      (MAP gas_shadow_internal_package ifns) (gas_shadow_env T ce0)
      (MAP gas_shadow_stmt stmts) pay F key ut "__deploy" = SOME shadow_unit /\
    gas_shadow_context unit.cu_context shadow_unit.cu_context /\
    gas_shadow_function fn shadow_fn /\
    MEM shadow_fn shadow_unit.cu_context.ctx_functions /\
    compile_stmts (gas_shadow_env T ce) NoLoop NoneT
      (MAP gas_shadow_stmt stmts) sa = ((),shadow_sb) /\
    gas_shadow_state sa sa /\ gas_shadow_state sb shadow_sb /\
    fn_has_code sa shadow_sb shadow_fn
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qspecl_then [`T`,`rp`,`runtime_bc`,`cap`,`args`,`0`,`ifns`,
    `ce0`,`stmts`,`pay`,`F`,`key`,`ut`,`"__deploy"`]
    mp_tac gas_shadow_run_deploy_lowering >>
  asm_rewrite_tac[] >> simp[OPTREL_def, AllCaseEqs()] >>
  disch_then (qx_choose_then `shadow_unit` strip_assume_tac) >>
  `gas_shadow_context unit.cu_context shadow_unit.cu_context` by
    fs[gas_shadow_unit_def] >>
  `(gas_shadow_env T ce0).ce_nonreentrant = (F,key,ut,F)` by simp[] >>
  `EVERY (\d. internal_label_ok (FST d))
     (internal_fn_descriptors (MAP gas_shadow_internal_package ifns))` by simp[] >>
  qpat_assum `run_deploy_lowering T _ _ _ _ _ (MAP _ _) _ _ _ _ _ _ _ = _`
    (fn run =>
     qpat_assum `(gas_shadow_env T ce0).ce_nonreentrant = _` (fn flags =>
       qpat_assum `EVERY _ (internal_fn_descriptors (MAP _ _))` (fn labels =>
         mp_tac (MATCH_MP run_linked_deploy_constructor_code
           (LIST_CONJ [flags,run,labels]))))) >>
  disch_then (qx_choosel_then [`st_pay_s`,`imm_s`,`st1_s`,`ce1_s`,`st2_s`,
    `st3_s`,`exit_lbl_s`,`sa_s`,`sb_s`,`sj_s`,`old_bb_s`,`st_exit_s`,
    `st_epilogue_s`,`st_final_s`,`shadow_fn`] strip_assume_tac) >>
  `st_pay_s = st_pay` by
    (qpat_assum `_ = ((),st_pay_s)` (fn shadow =>
       qpat_assum `_ = ((),st_pay)` (mp_tac o TRANS (SYM shadow))) >> simp[]) >>
  qpat_x_assum `st_pay_s = st_pay` SUBST_ALL_TAC >>
  `imm_s = imm /\ st1_s = st1` by
    (qpat_assum `_ st_pay = (imm_s,st1_s)` (fn shadow =>
       qpat_assum `_ st_pay = (imm,st1)` (mp_tac o TRANS (SYM shadow))) >> simp[]) >>
  gvs[comp_return_def] >>
  `gas_shadow_env T ce0 with
      ce_imm_alloca := (if cap > 0 then SOME imm else NONE) =
    gas_shadow_env T (ce0 with
      ce_imm_alloca := (if cap > 0 then SOME imm else NONE))` by
    simp[gas_shadow_env_def, compile_env_component_equality] >>
  `ce1_s = gas_shadow_env T ce1 /\ st2_s = st2` by
    (qpat_x_assum `compile_register_constructor_args _ _ _ _ _ = (ce1_s,st2_s)`
      mp_tac >>
     simp[compile_register_constructor_args_gas_shadow_env]) >>
  gvs[] >>
  `gas_shadow_env T ce1 with ce_ctor_exit_label := SOME exit_lbl =
    gas_shadow_env T (ce1 with ce_ctor_exit_label := SOME exit_lbl)` by
    simp[gas_shadow_env_def, compile_env_component_equality] >>
  `gas_shadow_state sb sb_s` by
    (mp_tac (Q.SPECL [`stmts`,`ce1 with ce_ctor_exit_label := SOME exit_lbl`,
       `NoLoop`,`NoneT`] (Q.INST [`sd` |-> `T`] gas_shadow_stmts_env_env)) >>
     rewrite_tac[gas_shadow_compiles_env_def] >>
     disch_then (qspecl_then [`sa`,`sa`] mp_tac) >>
     simp[gas_shadow_state_refl] >>
     fs[compile_stmts_env]) >>
  `gas_shadow_function fn shadow_fn` by
    (qspecl_then [`unit.cu_context.ctx_functions`,
       `shadow_unit.cu_context.ctx_functions`,`"__deploy"`]
       mp_tac gas_shadow_lookup_function >>
     fs[gas_shadow_context_def]) >>
  `MEM shadow_fn shadow_unit.cu_context.ctx_functions` by
    drule_then ACCEPT_TAC lookup_function_MEM >>
  qexistsl_tac [`shadow_fn`,`sb_s`] >> simp[gas_shadow_state_refl] >>
  qpat_assum `gas_shadow_env T ce1 with ce_ctor_exit_label := SOME exit_lbl = _`
    (fn update => ONCE_REWRITE_TAC [GSYM update]) >>
  FIRST_ASSUM ACCEPT_TAC
QED
