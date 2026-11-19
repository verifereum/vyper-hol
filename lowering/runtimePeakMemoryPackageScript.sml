(* Typed runtime packages satisfy the expression, statement and default gates. *)
Theory runtimePeakMemoryPackage
Ancestors
  runtimePeakMemoryRuntime runtimePeakMemoryStmt runtimePeakMemoryExprDispatch
  runtimePeakMemoryCode runtimePeakMemorySourceGate runtimePeakMemoryArity
  supportedExprTraverse supportedStmtTraverse compileVyper compileEnv
  vyperCompiler moduleLowering venomInst e2eDefs list arithmetic


Theorem dalloca_windows_packaged_stmts[local]:
  compile_env_blueprint_free ce /\ compile_env_builtin_arity ce /\
  ~supported_stmts_expr_exists blueprint_create_root fbody /\
  ~supported_stmts_expr_exists short_builtin_args fbody /\
  env.ce_func_defaults = ce.ce_func_defaults ==>
  preserves_dalloca_windows
    (\chunk k. raw_call_dalloca_chunk chunk k \/ create_copy_dalloca_chunk chunk k)
    (compile_stmts env lc rt fbody)
Proof
  rpt strip_tac >> irule dalloca_windows_compile_stmts >>
  simp[compile_env_blueprint_free_def, compile_env_builtin_arity_def] >>
  fs[compile_env_blueprint_free_def, compile_env_builtin_arity_def]
QED

Theorem dalloca_windows_external_env[local]:
  source_typing_ok source_tops am tx /\ runtime_blueprint_free source_tops ==>
  compile_env_blueprint_free
    (FST (SND (set_external_package_target target
                (package_external_fn source_tops tr keys (mut,nr,rr,name,args,ds,ret,fbody))))) /\
  compile_env_builtin_arity
    (FST (SND (set_external_package_target target
                (package_external_fn source_tops tr keys (mut,nr,rr,name,args,ds,ret,fbody)))))
Proof
  strip_tac >>
  `compile_env_blueprint_free
     (build_compile_env source_tops External mut name args ret fbody tr)` by
    metis_tac[build_compile_env_blueprint_free] >>
  `compile_env_builtin_arity
     (build_compile_env source_tops External mut name args ret fbody tr)` by
    metis_tac[build_compile_env_builtin_arity] >>
  Cases_on `ret = NoneT` >>
  gvs[package_external_fn_def, set_external_package_target_def,
      update_cenv_ret_abi_def, update_cenv_nonreentrant_def,
      compile_env_blueprint_free_def, compile_env_builtin_arity_def]
QED

Theorem zip_snd_mem[local]:
  !xs ys a b. MEM (a,b) (ZIP (xs,ys)) ==> MEM b ys
Proof
  Induct >> simp[ZIP_def] >> gen_tac >> Cases >> simp[ZIP_def] >> metis_tac[]
QED

Theorem group_spec_default_mem[local]:
  MEM e (MAP (\(_,_,d). d)
    (MAP (\((name,ty),d). (name,ty,d)) (ZIP (xs,ds)))) ==> MEM e ds
Proof
  simp[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[zip_snd_mem]
QED

Theorem dalloca_windows_packaged_externals[local]:
  source_typing_ok source_tops am tx /\ runtime_blueprint_free source_tops ==>
  EVERY (runtime_external_package_windows
          (\chunk k. raw_call_dalloca_chunk chunk k \/ create_copy_dalloca_chunk chunk k))
    (MAP (set_external_package_target target o package_external_fn source_tops tr keys)
      (FST (classify_functions source_tops)))
Proof
  strip_tac >> simp[EVERY_MAP, EVERY_MEM, combinTheory.o_DEF] >>
  qx_gen_tac `e` >> PairCases_on `e` >> strip_tac >>
  imp_res_tac classify_external_blueprint_free >>
  imp_res_tac classify_external_builtin_arity >>
  drule_all (Q.INST [`mut` |-> `e0`, `nr` |-> `e1`, `rr` |-> `e2`,
    `name` |-> `e3`, `args` |-> `e4`, `ds` |-> `e5`, `ret` |-> `e6`,
    `fbody` |-> `e7`] dalloca_windows_external_env) >> strip_tac >>
  simp[package_external_fn_def, set_external_package_target_def,
       runtime_external_package_windows_def] >>
  irule dalloca_windows_external_function_body >>
  rpt strip_tac >> irule dalloca_windows_packaged_stmts >> simp[] >>
  qexists_tac `FST (SND (set_external_package_target target
    (package_external_fn source_tops tr keys (e0,e1,e2,e3,e4,e5,e6,e7))))` >>
  gvs[package_external_fn_def, set_external_package_target_def]
QED

Theorem dalloca_windows_packaged_groups[local]:
  source_typing_ok source_tops am tx /\ runtime_blueprint_free source_tops ==>
  EVERY (runtime_external_group_windows
          (\chunk k. raw_call_dalloca_chunk chunk k \/ create_copy_dalloca_chunk chunk k))
    (MAP (package_external_group source_tops target tr keys) (FST (classify_functions source_tops)))
Proof
  strip_tac >> simp[EVERY_MAP, EVERY_MEM] >>
  qx_gen_tac `e` >> PairCases_on `e` >> strip_tac >>
  imp_res_tac classify_external_blueprint_free >>
  imp_res_tac classify_external_builtin_arity >>
  drule_all (Q.INST [`mut` |-> `e0`, `nr` |-> `e1`, `rr` |-> `e2`,
    `name` |-> `e3`, `args` |-> `e4`, `ds` |-> `e5`, `ret` |-> `e6`,
    `fbody` |-> `e7`] dalloca_windows_external_env) >> strip_tac >>
  simp[package_external_group_def] >> COND_CASES_TAC
  >- (simp[runtime_external_group_windows_def] >>
      fs[EVERY_MEM, combinTheory.o_DEF] >>
      metis_tac[dalloca_windows_packaged_externals, EVERY_MEM, MEM_MAP,
                combinTheory.o_THM]) >>
  simp[runtime_external_group_windows_def, package_external_fn_def,
       set_external_package_target_def] >> conj_tac
  >- (rpt strip_tac >> irule dalloca_windows_packaged_stmts >> simp[] >>
      qexists_tac `FST (SND (set_external_package_target target
        (package_external_fn source_tops tr keys (e0,e1,e2,e3,e4,e5,e6,e7))))` >>
      gvs[package_external_fn_def, set_external_package_target_def]) >>
  rpt strip_tac >> irule dalloca_windows_compile_expr >> simp[] >>
  fs[package_external_fn_def, set_external_package_target_def, EVERY_MEM] >>
  metis_tac[group_spec_default_mem]
QED

Theorem dalloca_windows_packaged_internals[local]:
  source_typing_ok source_tops am tx /\ runtime_blueprint_free source_tops ==>
  EVERY (\(lbl,ce,ps,buf,nr,key,ut,vw,ctor,im,fbody,rt).
    preserves_dalloca_windows
      (\chunk k. raw_call_dalloca_chunk chunk k \/ create_copy_dalloca_chunk chunk k)
      (compile_internal_function ce ps buf nr key ut vw ctor im fbody rt))
    (MAP (set_internal_package_target target o package_internal_fn source_tops tr keys F 0)
      (order_internals order (FST (SND (classify_functions source_tops)))))
Proof
  strip_tac >> simp[EVERY_MAP, EVERY_MEM, combinTheory.o_DEF, MEM_order_internals] >>
  qx_gen_tac `e` >> PairCases_on `e` >> strip_tac >>
  imp_res_tac classify_internal_blueprint_free >>
  imp_res_tac classify_internal_builtin_arity >>
  imp_res_tac build_compile_env_blueprint_free >>
  imp_res_tac build_compile_env_builtin_arity >>
  simp[package_internal_fn_def, set_internal_package_target_def] >>
  irule dalloca_windows_internal_function >>
  rpt strip_tac >> irule dalloca_windows_packaged_stmts >> simp[] >>
  qexists_tac `build_compile_env source_tops Internal e0 e3 e4 e6 e7 tr` >>
  simp[update_cenv_nonreentrant_def] >>
  metis_tac[build_compile_env_blueprint_free, build_compile_env_builtin_arity]
QED

Theorem dalloca_windows_packaged_fallback[local]:
  source_typing_ok source_tops am tx /\ runtime_blueprint_free source_tops ==>
  (case set_fallback_package_target target
     (package_fallback_fn source_tops tr keys (FST (SND (SND (classify_functions source_tops))))) of
     NONE => T
   | SOME (ce,pay,nr,key,ut,vw,fbody,rt) =>
     preserves_dalloca_windows
       (\chunk k. raw_call_dalloca_chunk chunk k \/ create_copy_dalloca_chunk chunk k)
       (compile_fallback_body ce pay nr key ut vw fbody rt))
Proof
  strip_tac >> Cases_on `FST (SND (SND (classify_functions source_tops)))`
  >- simp[package_fallback_fn_def, set_fallback_package_target_def] >>
  rename1 `SOME src` >> PairCases_on `src` >>
  imp_res_tac classify_fallback_blueprint_free >>
  imp_res_tac classify_fallback_builtin_arity >>
  imp_res_tac build_compile_env_blueprint_free >>
  imp_res_tac build_compile_env_builtin_arity >>
  simp[package_fallback_fn_def, set_fallback_package_target_def] >>
  irule dalloca_windows_fallback_body >>
  rpt strip_tac >> irule dalloca_windows_packaged_stmts >> simp[] >>
  qexists_tac `build_compile_env source_tops External src0 src3 src4 src6 src7 tr` >>
  Cases_on `src6 = NoneT` >>
  gvs[update_cenv_ret_abi_def, update_cenv_nonreentrant_def] >>
  metis_tac[build_compile_env_blueprint_free, build_compile_env_builtin_arity]
QED

Theorem run_lowering_dalloca_windows[local]:
  run_lowering selectors exts ints fb policy 0 0 [] info lbl = SOME unit /\
  preserves_dalloca_windows window
    (compile_generate_runtime selectors exts ints fb policy.rpol_frontend_dispatch 0 0 [] info) ==>
  !fn bb. MEM fn unit.cu_context.ctx_functions /\ MEM bb fn.fn_blocks ==>
    dalloca_windows window bb.bb_instructions
Proof
  simp[run_lowering_def] >> pairarg_tac >> gvs[AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[extract_context_dalloca_windows, preserves_dalloca_windows_def,
            dalloca_windows_initial]
QED

Theorem run_grouped_lowering_dalloca_windows[local]:
  run_grouped_lowering groups ints fb policy lbl = SOME unit /\
  preserves_dalloca_windows window (compile_generate_grouped_runtime groups ints fb) ==>
  !fn bb. MEM fn unit.cu_context.ctx_functions /\ MEM bb fn.fn_blocks ==>
    dalloca_windows window bb.bb_instructions
Proof
  simp[run_grouped_lowering_def] >> pairarg_tac >> gvs[AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[extract_context_dalloca_windows, preserves_dalloca_windows_def,
            dalloca_windows_initial]
QED

Theorem runtime_external_package_windows_eq[local]:
  runtime_external_package_windows window =
  (\(lbl,ce,args,cds,pay,nr,key,tr,vw,fbody,rt).
     preserves_dalloca_windows window
       (compile_external_function_body ce args nr key tr vw fbody rt))
Proof
  simp[FUN_EQ_THM, pairTheory.FORALL_PROD, runtime_external_package_windows_def]
QED

Theorem lower_vyper_runtime_unit_dalloca_windows:
  lower_vyper_runtime_unit source_tops policy = SOME unit /\
  source_typing_ok source_tops am tx /\ runtime_blueprint_free source_tops ==>
  !fn bb. MEM fn unit.cu_context.ctx_functions /\ MEM bb fn.fn_blocks ==>
    dalloca_windows (\chunk k. raw_call_dalloca_chunk chunk k \/
                                create_copy_dalloca_chunk chunk k) bb.bb_instructions
Proof
  strip_tac >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_def] >> pairarg_tac >> gvs[AllCaseEqs()] >>
  rpt strip_tac >>
  FIRST (map (drule o REWRITE_RULE [GSYM AND_IMP_INTRO] o
    Q.INST [`window` |-> `\chunk k. raw_call_dalloca_chunk chunk k \/
                                  create_copy_dalloca_chunk chunk k`])
    [run_grouped_lowering_dalloca_windows, run_lowering_dalloca_windows]) >>
  disch_then (qspecl_then [`fn`, `bb`] mp_tac) >>
  (impl_tac >-
    (simp[] >>
     FIRST [irule dalloca_windows_generate_grouped_runtime,
            irule dalloca_windows_generate_runtime] >>
     rpt conj_tac >>
     TRY (drule_all (Q.INST [`tr` |-> `T`, `target` |-> `policy.rpol_target`,
                          `keys` |-> `K global_nonreentrant_slot`]
          dalloca_windows_packaged_groups) >> fs[] >> NO_TAC) >>
     all_tac >~ [`order_internals _ _`] >-
       (drule_all (Q.INST [`tr` |-> `T`, `target` |-> `policy.rpol_target`,
          `keys` |-> `K global_nonreentrant_slot`,
          `order` |-> `runtime_internal_order source_tops (FST (SND (classify_functions source_tops)))`]
          dalloca_windows_packaged_internals) >>
        qpat_assum `classify_functions _ = _` (fn eq =>
          disch_then (assume_tac o REWRITE_RULE [eq, pairTheory.FST, pairTheory.SND] o SPEC_ALL)) >>
        first_assum ACCEPT_TAC) >>
     TRY (drule_all (Q.INST [`tr` |-> `T`, `target` |-> `policy.rpol_target`,
                          `keys` |-> `K global_nonreentrant_slot`]
          dalloca_windows_packaged_fallback) >> fs[] >> NO_TAC) >>
     drule_all (Q.INST [`tr` |-> `T`, `target` |-> `policy.rpol_target`,
                        `keys` |-> `K global_nonreentrant_slot`]
       dalloca_windows_packaged_externals) >>
     qpat_assum `classify_functions _ = _` (fn eq =>
       disch_then (assume_tac o REWRITE_RULE
         [eq, pairTheory.FST, runtime_external_package_windows_eq] o SPEC_ALL)) >>
     first_assum ACCEPT_TAC)) >>
  simp[]
QED
