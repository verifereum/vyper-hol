(* Typed runtime packages satisfy the expression, statement and default gates. *)
Theory runtimePeakMemoryPackage
Ancestors
  runtimePeakMemoryRuntime runtimePeakMemoryStmt runtimePeakMemoryExprDispatch
  runtimePeakMemoryCode runtimePeakMemorySourceGate runtimePeakMemoryArity
  supportedExprTraverse supportedStmtTraverse compileVyper compileEnv
  vyperCompiler moduleLowering venomInst e2eDefs vyperTypeContract vyperAST list arithmetic


Theorem dalloca_windows_packaged_stmts:
  (!chunk. raw_call_dalloca_chunk chunk 1 ==> window chunk 1) /\
  (!chunk. create_copy_dalloca_chunk chunk 5 ==> window chunk 5) /\
  (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
    compile_env_blueprint_free ce) /\ compile_env_builtin_arity ce /\
  (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
    ~supported_stmts_expr_exists blueprint_create_root fbody) /\
  ~supported_stmts_expr_exists short_builtin_args fbody /\
  env.ce_func_defaults = ce.ce_func_defaults ==>
  preserves_dalloca_windows
    window
    (compile_stmts env lc rt fbody)
Proof
  rpt strip_tac >> irule dalloca_windows_compile_stmts >>
  simp[compile_env_blueprint_free_def, compile_env_builtin_arity_def] >>
  fs[compile_env_blueprint_free_def, compile_env_builtin_arity_def]
QED

Theorem runtime_blueprint_free_internal[local]:
  runtime_blueprint_free source_tops ==>
  !mut nr rr name args ds ret ss.
    MEM (FunctionDecl Internal mut nr rr name args ds ret ss) source_tops ==>
    ~supported_stmts_expr_exists blueprint_create_root ss /\
    EVERY (\d. ~supported_expr_exists blueprint_create_root d) ds
Proof
  simp[runtime_blueprint_free_def] >> metis_tac[function_visibility_distinct]
QED

Theorem dalloca_windows_external_env[local]:
  check_contract F layouts addr [(NONE, source_tops)] = SOME art /\
  (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
    runtime_blueprint_free source_tops) ==>
  (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
   compile_env_blueprint_free
    (FST (SND (set_external_package_target target
                (package_external_fn source_tops tr keys (mut,nr,rr,name,args,ds,ret,fbody)))))) /\
  compile_env_builtin_arity
    (FST (SND (set_external_package_target target
                (package_external_fn source_tops tr keys (mut,nr,rr,name,args,ds,ret,fbody)))))
Proof
  strip_tac >>
  `~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
    compile_env_blueprint_free
      (build_compile_env source_tops External mut name args ret fbody tr)` by
    metis_tac[runtime_blueprint_free_internal, build_compile_env_blueprint_free] >>
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
  (!chunk. raw_call_dalloca_chunk chunk 1 ==> window chunk 1) /\
  (!chunk. create_copy_dalloca_chunk chunk 5 ==> window chunk 5) /\
  check_contract F layouts addr [(NONE, source_tops)] = SOME art /\ (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
    runtime_blueprint_free source_tops) ==>
  EVERY (runtime_external_package_windows window)
    (MAP (set_external_package_target target o package_external_fn source_tops tr keys)
      (FST (classify_functions source_tops)))
Proof
  strip_tac >>
  Cases_on `!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1` >>
  fs[] >>
  (simp[EVERY_MAP, EVERY_MEM, combinTheory.o_DEF] >>
  qx_gen_tac `e` >> PairCases_on `e` >> strip_tac >>
  imp_res_tac classify_external_blueprint_free >>
  imp_res_tac classify_external_builtin_arity >>
  mp_tac (Q.INST [`mut` |-> `e0`, `nr` |-> `e1`, `rr` |-> `e2`,
    `name` |-> `e3`, `args` |-> `e4`, `ds` |-> `e5`, `ret` |-> `e6`,
    `fbody` |-> `e7`] dalloca_windows_external_env) >> (impl_tac >- simp[]) >> strip_tac >>
  simp[package_external_fn_def, set_external_package_target_def,
       runtime_external_package_windows_def] >>
  irule dalloca_windows_external_function_body >>
  rpt strip_tac >> irule dalloca_windows_packaged_stmts >> simp[] >>
  qexists_tac `FST (SND (set_external_package_target target
    (package_external_fn source_tops tr keys (e0,e1,e2,e3,e4,e5,e6,e7))))` >>
  gvs[package_external_fn_def, set_external_package_target_def])
QED

Theorem dalloca_windows_packaged_groups[local]:
  (!chunk. raw_call_dalloca_chunk chunk 1 ==> window chunk 1) /\
  (!chunk. create_copy_dalloca_chunk chunk 5 ==> window chunk 5) /\
  check_contract F layouts addr [(NONE, source_tops)] = SOME art /\ (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
    runtime_blueprint_free source_tops) ==>
  EVERY (runtime_external_group_windows window)
    (MAP (package_external_group source_tops target tr keys) (FST (classify_functions source_tops)))
Proof
  strip_tac >>
  mp_tac (Q.INST [`target` |-> `target`, `tr` |-> `tr`, `keys` |-> `keys`]
    dalloca_windows_packaged_externals) >>
  (impl_tac >- simp[]) >>
  disch_then (assume_tac o SIMP_RULE (srw_ss ())
    [EVERY_MAP, EVERY_MEM, combinTheory.o_DEF]) >>
  Cases_on `!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1` >>
  fs[] >>
  (simp[EVERY_MAP, EVERY_MEM] >>
  qx_gen_tac `e` >> PairCases_on `e` >> strip_tac >>
  imp_res_tac classify_external_blueprint_free >>
  imp_res_tac classify_external_builtin_arity >>
  mp_tac (Q.INST [`mut` |-> `e0`, `nr` |-> `e1`, `rr` |-> `e2`,
    `name` |-> `e3`, `args` |-> `e4`, `ds` |-> `e5`, `ret` |-> `e6`,
    `fbody` |-> `e7`] dalloca_windows_external_env) >> (impl_tac >- simp[]) >> strip_tac >>
  simp[package_external_group_def] >> COND_CASES_TAC
  >- (qpat_assum `!e. MEM e _ ==> runtime_external_package_windows _ _` drule >>
      simp[runtime_external_group_windows_def]) >>
  simp[runtime_external_group_windows_def, package_external_fn_def,
       set_external_package_target_def] >> conj_tac
  >- (rpt strip_tac >> irule dalloca_windows_packaged_stmts >> simp[] >>
      qexists_tac `FST (SND (set_external_package_target target
        (package_external_fn source_tops tr keys (e0,e1,e2,e3,e4,e5,e6,e7))))` >>
      gvs[package_external_fn_def, set_external_package_target_def]) >>
  rpt strip_tac >> irule dalloca_windows_compile_expr >> simp[] >>
  fs[package_external_fn_def, set_external_package_target_def, EVERY_MEM] >>
  metis_tac[group_spec_default_mem])
QED

Theorem dalloca_windows_packaged_internals:
  check_contract F layouts addr [(NONE, source_tops)] = SOME art /\
  (!chunk. raw_call_dalloca_chunk chunk 1 ==> window chunk 1) /\
  (!chunk. create_copy_dalloca_chunk chunk 5 ==> window chunk 5) /\
  (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
    !mut nr rr name args ds ret ss.
    MEM (FunctionDecl Internal mut nr rr name args ds ret ss) source_tops ==>
    ~supported_stmts_expr_exists blueprint_create_root ss /\
    EVERY (\d. ~supported_expr_exists blueprint_create_root d) ds) ==>
  EVERY (\(lbl,ce,ps,buf,nr,key,ut,vw,ctor,im,fbody,rt).
    preserves_dalloca_windows
      window
      (compile_internal_function ce ps buf nr key ut vw ctor im fbody rt))
    (MAP (set_internal_package_target target o package_internal_fn source_tops tr keys ctor_mode ilen)
      (order_internals order (FST (SND (classify_functions source_tops)))))
Proof
  strip_tac >>
  fs[] >> simp[EVERY_MAP, EVERY_MEM, combinTheory.o_DEF, MEM_order_internals] >>
  qx_gen_tac `e` >> PairCases_on `e` >> strip_tac >>
  imp_res_tac classify_internal_builtin_arity >>
  simp[package_internal_fn_def, set_internal_package_target_def] >>
  irule dalloca_windows_internal_function >>
  rpt strip_tac >> irule dalloca_windows_packaged_stmts >>
  simp[GSYM LEFT_EXISTS_AND_THM] >>
  qmatch_goalsub_abbrev_tac
    `update_cenv_nonreentrant (base_env with <|ce_is_ctor := _; ce_raw_return := _|>) _ _ _ _` >>
  qexists_tac `base_env` >>
  simp[update_cenv_nonreentrant_def, Abbr `base_env`] >>
  conj_tac
  >- (conj_tac >- metis_tac[build_compile_env_builtin_arity] >>
      disch_tac >>
      qpat_assum `(?chunk. create_blueprint_dalloca_chunk chunk 1 /\ ~window chunk 1) ==> _`
        (fn th => drule th >> strip_tac) >>
      irule build_compile_env_blueprint_free >> metis_tac[]) >>
  disch_tac >>
  qpat_assum `(?chunk. create_blueprint_dalloca_chunk chunk 1 /\ ~window chunk 1) ==> _`
    (fn th => drule th >> strip_tac) >>
  drule_all classify_internal_blueprint_free >> simp[]
QED

Theorem dalloca_windows_packaged_fallback[local]:
  (!chunk. raw_call_dalloca_chunk chunk 1 ==> window chunk 1) /\
  (!chunk. create_copy_dalloca_chunk chunk 5 ==> window chunk 5) /\
  check_contract F layouts addr [(NONE, source_tops)] = SOME art /\ (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
    runtime_blueprint_free source_tops) ==>
  (case set_fallback_package_target target
     (package_fallback_fn source_tops tr keys (FST (SND (SND (classify_functions source_tops))))) of
     NONE => T
   | SOME (ce,pay,nr,key,ut,vw,fbody,rt) =>
     preserves_dalloca_windows
       window
       (compile_fallback_body ce pay nr key ut vw fbody rt))
Proof
  strip_tac >>
  Cases_on `!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1` >>
  fs[] >>
  (TRY (drule runtime_blueprint_free_internal >> strip_tac) >>
  Cases_on `FST (SND (SND (classify_functions source_tops)))`
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
  metis_tac[build_compile_env_blueprint_free, build_compile_env_builtin_arity])
QED

Theorem run_lowering_dalloca_windows:
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

Theorem run_grouped_lowering_dalloca_windows:
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

Theorem lower_vyper_runtime_unit_dalloca_windows_for:
  (!chunk. raw_call_dalloca_chunk chunk 1 ==> window chunk 1) /\
  (!chunk. create_copy_dalloca_chunk chunk 5 ==> window chunk 5) /\
  lower_vyper_runtime_unit source_tops policy = SOME unit /\
  source_typing_ok source_tops am tx /\ (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
    runtime_blueprint_free source_tops) ==>
  !fn bb. MEM fn unit.cu_context.ctx_functions /\ MEM bb fn.fn_blocks ==>
    dalloca_windows window bb.bb_instructions
Proof
  strip_tac >>
  fs[source_typing_ok_def] >>
  `(?chunk. create_blueprint_dalloca_chunk chunk 1 /\ ~window chunk 1) ==>
   !mut nr rr name args ds ret ss.
     MEM (FunctionDecl Internal mut nr rr name args ds ret ss) source_tops ==>
     ~supported_stmts_expr_exists blueprint_create_root ss /\
     EVERY (\d. ~supported_expr_exists blueprint_create_root d) ds` by
    (disch_tac >>
     qpat_assum `_ ==> runtime_blueprint_free _` (fn th => drule th >> strip_tac) >>
     drule runtime_blueprint_free_internal >> simp[]) >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_def] >> pairarg_tac >> gvs[AllCaseEqs()] >>
  rpt strip_tac >>
  FIRST (map (drule o REWRITE_RULE [GSYM AND_IMP_INTRO])
    [run_grouped_lowering_dalloca_windows, run_lowering_dalloca_windows]) >>
  disch_then (qspecl_then [`window`, `fn`, `bb`] mp_tac) >>
  (impl_tac >-
    (simp[] >>
     FIRST [irule dalloca_windows_generate_grouped_runtime,
            irule dalloca_windows_generate_runtime] >>
     rpt conj_tac >>
     qpat_assum `classify_functions _ = _` (fn eq =>
       FIRST (map (irule o REWRITE_RULE
         [eq, pairTheory.FST, pairTheory.SND, runtime_external_package_windows_eq,
          NOT_FORALL_THM, NOT_IMP] o Q.INST_TYPE [`:'a` |-> `:160 word`])
         [dalloca_windows_packaged_groups, dalloca_windows_packaged_internals,
          dalloca_windows_packaged_fallback, dalloca_windows_packaged_externals])) >>
     simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rename1 `check_contract F _ _ _ = SOME checked` >>
     map_every qexists_tac [`tx.target`, `checked`, `am.layouts`] >> simp[])) >>
  simp[]
QED

Theorem lower_vyper_runtime_unit_dalloca_windows:
  lower_vyper_runtime_unit source_tops policy = SOME unit /\
  source_typing_ok source_tops am tx /\ runtime_blueprint_free source_tops ==>
  !fn bb. MEM fn unit.cu_context.ctx_functions /\ MEM bb fn.fn_blocks ==>
    dalloca_windows (\chunk k. raw_call_dalloca_chunk chunk k \/
                                create_copy_dalloca_chunk chunk k) bb.bb_instructions
Proof
  strip_tac >>
  mp_tac (Q.INST [`window` |-> `\chunk k. raw_call_dalloca_chunk chunk k \/
                                  create_copy_dalloca_chunk chunk k`]
    lower_vyper_runtime_unit_dalloca_windows_for) >>
  simp[]
QED
