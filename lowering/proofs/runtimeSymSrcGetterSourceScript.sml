Theory runtimeSymSrcGetterSource
Ancestors
  runtimeSymSrcGetterExpr runtimeSymSrcGetterReturn runtimeSymSrcInterfaces
  runtimeSymSrcExpressions runtimeSymSrcPrimitives ctorDeployDefs
  supportedGetterProps supportedExprs supportedProgram supportedExprTraverse constSubst
  compileVyper vyperGetter compileEnv stmtLowering stackPlanTypes list alist

Theorem runtime_sym_getter_stmts[local]:
  !tops nr ne kt vt gm gn args dflts ret gbody.
  getter nr ne kt vt = (gm,gn,args,dflts,ret,gbody) /\
  (!ce ty s v s'. runtime_sym_env tops ce /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_expr ce ty ne s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v) /\
  (!b v info s op s'. ~is_label_operand b /\ ~is_label_operand v /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_encode_to_buf b v info s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  !ce ty s u s'. runtime_sym_env tops ce /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_stmts ce NoLoop ty gbody s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  rpt gen_tac >> simp[getter_def] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rpt gen_tac >> strip_tac >>
  irule runtime_sym_single_return_raw >>
  conj_tac >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at (Pat `compile_stmts _ _ _ _ _ = _`)) >>
  simp[runtime_sym_loop_def] >>
  mp_tac runtime_sym_build_getter_expr >>
  disch_then (drule_at (Pat `build_getter _ _ _ _ = _`)) >>
  simp[] >> disch_tac >> qexists_tac `tops` >> simp[] >>
  rpt strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem runtime_sym_subst_getter[local]:
  getter nr ne kt vt = (gm,gn,args,dflts,ret,gbody) ==>
  getter nr (subst_consts_expr E ne) kt vt =
    (gm,gn,args,dflts,ret,subst_consts_stmts E gbody)
Proof
  simp[getter_def] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule build_getter_subst >>
  disch_then (qspec_then `E` assume_tac) >>
  simp[subst_consts_stmt_def, subst_consts_expr_def]
QED

Theorem runtime_sym_subst_topname[local]:
  (!id e. ALOOKUP (module_consts_env tops []) id = SOME e ==>
    ~supported_expr_exists is_self_code e) /\
  supported_program tops /\ runtime_sym_env tops ce /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_expr ce ty
    (subst_consts_expr (module_consts_env tops []) (TopLevelName rt (NONE,id))) s =
      (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  Cases_on `ALOOKUP (module_consts_env tops []) id` >>
  simp[subst_consts_expr_def]
  >- metis_tac[runtime_sym_getter_topname_raw] >>
  strip_tac >>
  drule_all supported_program_const_replacement >> strip_tac >>
  qpat_assum `!id e. ALOOKUP (module_consts_env tops []) id = SOME e ==> _`
    (drule_at (Pat `ALOOKUP _ _ = _`)) >>
  strip_tac >>
  qspec_then `tops` mp_tac runtime_sym_generators >>
  disch_then (mp_tac o cj 1 o MATCH_MP runtime_sym_expression_contracts) >>
  disch_then (qspecl_then [`ce`,`ty`,`x`] mp_tac) >>
  simp[runtime_sym_expr_contract_def, supported_expr_def] >>
  metis_tac[]
QED

Theorem runtime_sym_subst_getter_stmts[local]:
  (!id e. ALOOKUP (module_consts_env tops []) id = SOME e ==>
    ~supported_expr_exists is_self_code e) /\
  getter nr (TopLevelName rt (NONE,id)) kt vt = (gm,gn,args,dflts,ret,gbody) /\
  supported_program tops /\ runtime_sym_env tops ce /\
  (!b v info s op s'. ~is_label_operand b /\ ~is_label_operand v /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_encode_to_buf b v info s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_stmts ce NoLoop ty (subst_consts_stmts (module_consts_env tops []) gbody) s =
    (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> drule runtime_sym_subst_getter >>
  disch_then (qspec_then `module_consts_env tops []` assume_tac) >>
  qspecl_then
    [`tops`, `nr`,
     `subst_consts_expr (module_consts_env tops []) (TopLevelName rt (NONE,id))`,
     `kt`, `vt`, `gm`, `gn`, `args`, `dflts`, `ret`,
     `subst_consts_stmts (module_consts_env tops []) gbody`]
    mp_tac runtime_sym_getter_stmts >>
  asm_rewrite_tac[] >>
  impl_tac
  >- (rpt gen_tac >> strip_tac >> drule_all runtime_sym_subst_topname >> simp[]) >>
  disch_then (qspecl_then [`ce`, `ty`, `s`, `u`, `s'`] mp_tac) >>
  simp[]
QED

Theorem runtime_sym_public_getter_stmts:
  (!id e. ALOOKUP (module_consts_env tops []) id = SOME e ==>
    ~supported_expr_exists is_self_code e) /\
  public_getter top = SOME (mut,nr,rr,name,args,dflts,ret,gbody) /\
  supported_program tops /\ runtime_sym_env tops ce /\
  (!b v info s op s'. ~is_label_operand b /\ ~is_label_operand v /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_encode_to_buf b v info s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_stmts ce NoLoop ty (subst_consts_stmts (module_consts_env tops []) gbody) s =
    (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Cases_on `top` >> simp[public_getter_def] >>
  all_tac
  >- (rename1 `public_getter (VariableDecl vis _ _ _ _)` >>
      Cases_on `vis` >> simp[public_getter_def] >>
      IF_CASES_TAC >> simp[]
      >- (strip_tac >> gvs[subst_consts_stmt_def, Once subst_consts_expr_def] >>
          irule runtime_sym_single_return_raw >>
          conj_tac >- first_assum ACCEPT_TAC >>
          goal_assum (drule_at (Pat `compile_stmts _ _ _ _ _ = _`)) >>
          simp[runtime_sym_loop_def] >> qexists_tac `tops` >> simp[] >> rpt strip_tac >>
          drule_all runtime_sym_subst_topname >> simp[]) >>
      pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      drule_all runtime_sym_subst_getter_stmts >> simp[]) >>
  rename1 `public_getter (HashMapDecl vis _ _ _ _ _)` >>
  Cases_on `vis` >> simp[public_getter_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule_all runtime_sym_subst_getter_stmts >> simp[]
QED
