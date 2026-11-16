Theory runtimeSymSrcGetterSource
Ancestors
  runtimeSymSrcGetterExpr runtimeSymSrcGetterReturn runtimeSymSrcInterfaces
  compileVyper vyperGetter compileEnv stmtLowering stackPlanTypes list

Theorem runtime_sym_getter_stmts[local]:
  getter nr ne kt vt = (gm,gn,args,dflts,ret,gbody) /\
  (!ce ty s v s'. runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_expr ce ty ne s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v) /\
  (!b v info s op s'. ~is_label_operand b /\ ~is_label_operand v /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_encode_to_buf b v info s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  !ce ty s u s'. runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_stmts ce NoLoop ty gbody s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  simp[getter_def] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rpt gen_tac >> strip_tac >>
  irule runtime_sym_single_return_raw >>
  conj_tac >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at (Pat `compile_stmts _ _ _ _ _ = _`)) >>
  simp[runtime_sym_loop_def] >>
  mp_tac runtime_sym_build_getter_expr >>
  disch_then (drule_at (Pat `build_getter _ _ _ _ = _`)) >>
  simp[] >> rpt strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem runtime_sym_public_getter_stmts:
  public_getter top = SOME (mut,nr,rr,name,args,dflts,ret,gbody) /\
  runtime_sym_env ce /\
  (!b v info s op s'. ~is_label_operand b /\ ~is_label_operand v /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_encode_to_buf b v info s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_stmts ce NoLoop ty gbody s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Cases_on `top` >> simp[public_getter_def] >>
  all_tac
  >- (rename1 `public_getter (VariableDecl vis _ _ _ _)` >>
      Cases_on `vis` >> simp[public_getter_def] >>
      IF_CASES_TAC >> simp[]
      >- (strip_tac >> gvs[] >> irule runtime_sym_single_return_raw >>
          conj_tac >- first_assum ACCEPT_TAC >>
          goal_assum (drule_at (Pat `compile_stmts _ _ _ _ _ = _`)) >>
          simp[runtime_sym_loop_def] >> rpt strip_tac >>
          drule_all runtime_sym_getter_topname_raw >> simp[]) >>
      pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      drule_at (Pat `getter _ _ _ _ = _`) runtime_sym_getter_stmts >>
      disch_then (drule_at (Pat `compile_stmts _ _ _ _ _ = _`)) >>
      simp[] >> disch_then irule >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >>
          drule_at (Pat `compile_expr _ _ _ _ = _`) runtime_sym_getter_topname_raw >>
          simp[]) >>
      first_assum ACCEPT_TAC) >>
  rename1 `public_getter (HashMapDecl vis _ _ _ _ _)` >>
  Cases_on `vis` >> simp[public_getter_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule_at (Pat `getter _ _ _ _ = _`) runtime_sym_getter_stmts >>
  disch_then (drule_at (Pat `compile_stmts _ _ _ _ _ = _`)) >>
  simp[] >> disch_then irule >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_at (Pat `compile_expr _ _ _ _ = _`) runtime_sym_getter_topname_raw >>
      simp[]) >>
  first_assum ACCEPT_TAC
QED
