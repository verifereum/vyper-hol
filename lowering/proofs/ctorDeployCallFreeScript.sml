(* A call-free constructor lowers to a deployment entry function that makes
 * no internal or external calls: no INVOKE and no RETURNDATACOPY.
 * TOP-LEVEL: lower_vyper_deploy_unit_call_free_entry (used by
 * deploy_frame_gas_sufficient).
 *)
Theory ctorDeployCallFree
Ancestors
  compileVyper vyperCompiler e2eDeployDefs venomInst ctorCallFreeEntry
  ctorCallFreeBodies ctorCallFreeExpr ctorCallFreeStmtReturns ctorCallFreeStmtStorage
  ctorCallFreeStmtLogs ctorCallFreeStmtTargets ctorCallFreeWrapper ctorCallFreeSource
  supportedStmtTraverse loweringShapeDefs compileEnv moduleLowering
  ctorDeployLoweringCode context loweringShapeProps
  vyperTypeContract vyperTypeContractContext ctorCallFreeStmt

(* The lowering emits INVOKE only for an internal call and RETURNDATACOPY
   only on the external-call, raw_call and create paths, all of which
   constructor_call_free excludes from __init__'s body; typing fixes each
   builtin's argument count, so no lowering reads past its arguments.
   Without a constructor the entry is the fixed CODECOPY/RETURN stub. *)
Theorem lower_vyper_deploy_unit_call_free_entry:
  !tops rpolicy runtime_bc dunit am tx.
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
    constructor_call_free tops /\ deploy_typing_ok tops am tx
    ==>
    ?efn.
      dunit.cu_context.ctx_entry = SOME efn.fn_name /\
      lookup_function efn.fn_name dunit.cu_context.ctx_functions = SOME efn /\
      !inst. MEM inst (fn_insts efn) ==>
             inst.inst_opcode <> RETURNDATACOPY /\ inst.inst_opcode <> INVOKE
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `classify_functions tops` >>
  rename1 `classify_functions tops = (exts, rest)` >>
  PairCases_on `rest` >>
  rename1 `classify_functions tops = (exts, ints, fb, ctor)` >>
  Cases_on `ctor`
  >- (qpat_x_assum `lower_vyper_deploy_unit _ _ _ = _` mp_tac >>
      simp[lower_vyper_deploy_unit_def, set_constructor_package_target_def] >>
      strip_tac >> drule no_ctor_lowering_entry_call_free >>
      simp[listTheory.EVERY_MEM]) >>
  rename1 `classify_functions tops = (exts, ints, fb, SOME cf)` >>
  PairCases_on `cf` >>
  rename1 `classify_functions tops =
    (exts,ints,fb,SOME (v_mut,v_nr,v_raw,v_name,v_args,v_defaults,v_ret,v_body))` >>
  drule_all classified_constructor_call_free_source >> strip_tac >>
  Cases_on `set_constructor_package_target rpolicy.rpol_target
    (package_constructor tops T (K global_nonreentrant_slot)
      (v_mut,v_nr,v_raw,v_name,v_args,v_defaults,v_ret,v_body))` >>
  rename1 `set_constructor_package_target _ _ = (ce, pkg)` >>
  PairCases_on `pkg` >>
  rename1 `set_constructor_package_target _ _ =
    (ce,args,pay,nr,key,trans,fbody,ret)` >>
  `fbody = v_body` by
    gvs[package_constructor_def, set_constructor_package_target_def] >>
  gvs[] >>
  `v_mut <> View` by
    (`MEM (FunctionDecl Deploy v_mut v_nr v_raw v_name v_args v_defaults v_ret fbody) tops` by
       (irule deploy_classify_constructor_mem >> simp[]) >>
     qpat_x_assum `deploy_typing_ok _ _ _` mp_tac >>
     simp[deploy_typing_ok_def] >> strip_tac >>
     rename1 `check_contract T am.layouts tx.target [(NONE,tops)] = SOME artifact` >>
     `check_toplevel_decl [(NONE,tops)] artifact NONE
        (FunctionDecl Deploy v_mut v_nr v_raw v_name v_args v_defaults v_ret fbody)` by
       (qpat_x_assum `check_contract T _ _ _ = _` mp_tac >>
        simp[check_contract_def, check_module_def, listTheory.EVERY_MEM] >>
        metis_tac[]) >>
     gvs[check_toplevel_decl_def, function_mutability_ok_def]) >>
  `cenv_static_ok ce /\ ce.ce_return_pc = NONE /\
   ce.ce_nonreentrant = (nr,key,trans,F)` by
    (qpat_x_assum `set_constructor_package_target _ _ = _` mp_tac >>
     simp[package_constructor_def, set_constructor_package_target_def,
       update_cenv_nonreentrant_def] >> strip_tac >> gvs[] >>
     `cenv_static_ok (build_compile_env tops Deploy v_mut v_name v_args ret fbody T)` by
       irule build_compile_env_static >>
     gvs[deploy_build_env_no_return_pc, cenv_static_ok_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!ce st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_stmts ce NoLoop NoneT fbody st)))` by
    (rpt strip_tac >> irule compile_stmts_call_free_from_expr >>
     simp[compile_expr_call_free] >> rpt strip_tac >>
     irule compile_expr_call_free >> simp[]) >>
  drule_all deploy_ctor_call_free_prefix >> strip_tac >>
  drule packaged_entry_every >> simp[] >>
  strip_tac >> first_x_assum drule_all >> strip_tac >>
  drule_all immutable_reservation_entry_every >>
  gvs[listTheory.EVERY_MEM] >> metis_tac[]
QED
