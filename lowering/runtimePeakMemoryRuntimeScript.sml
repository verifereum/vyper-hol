(* Runtime entry, function bodies, and grouped default dispatch. *)
Theory runtimePeakMemoryRuntime
Ancestors
  runtimePeakMemoryModule runtimePeakMemoryExpr
  runtimePeakMemoryArity runtimePeakMemorySourceGate runtimePeakMemoryCode
  runtimePeakMemoryControl runtimePeakMemoryStmtOps
  loweringRuntimeOpcodes compileVyper moduleLowering stmtLowering
  compileEnv context emitHelper venomInst list finite_map

fun windows_tac thms =
  rpt (FIRST [
    CHANGED_TAC (simp(thms @ [LET_THM, pairTheory.FORALL_PROD, pairTheory.UNCURRY_DEF,
      dalloca_windows_emit_helpers, dalloca_windows_new_block, dalloca_windows_get,
      dalloca_windows_fresh, dalloca_windows_return, dalloca_windows_entry_checks,
      dalloca_windows_nonreentrant, dalloca_windows_alloc_buffer])),
    gen_tac, irule dalloca_windows_bind >> conj_tac,
    irule dalloca_windows_ignore_bind >> conj_tac,
    COND_CASES_TAC, BasicProvers.TOP_CASE_TAC]);

Theorem dalloca_windows_guarded_body:
  (!env lc rt. env.ce_func_defaults = ce.ce_func_defaults ==>
     preserves_dalloca_windows window (compile_stmts env lc rt fbody)) ==>
  preserves_dalloca_windows window
    (compile_guarded_body ce nr key tr view fbody ret)
Proof
  strip_tac >> simp[compile_guarded_body_def] >> windows_tac []
QED

Theorem dalloca_windows_external_function_body:
  (!env lc rt. env.ce_func_defaults = ce.ce_func_defaults ==>
     preserves_dalloca_windows window (compile_stmts env lc rt fbody)) ==>
  preserves_dalloca_windows window
    (compile_external_function_body ce args nr key tr view fbody ret)
Proof
  strip_tac >> simp[compile_external_function_body_def] >>
  match_mp_tac (Q.ISPEC `\env. env.ce_func_defaults = ce.ce_func_defaults`
    (Q.GEN `P` dalloca_windows_bind_result)) >>
  simp[dalloca_windows_register_positional_args, register_positional_args_defaults] >>
  rpt strip_tac >> irule dalloca_windows_guarded_body >> metis_tac[]
QED

Theorem dalloca_windows_fallback_body:
  (!env lc rt. env.ce_func_defaults = ce.ce_func_defaults ==>
     preserves_dalloca_windows window (compile_stmts env lc rt fbody)) ==>
  preserves_dalloca_windows window
    (compile_fallback_body ce pay nr key tr view fbody ret)
Proof
  strip_tac >> simp[compile_fallback_body_def] >>
  windows_tac [dalloca_windows_guarded_body]
QED

Theorem dalloca_windows_internal_function:
  (!env lc rt. env.ce_func_defaults = ce.ce_func_defaults ==>
     preserves_dalloca_windows window (compile_stmts env lc rt fbody)) ==>
  preserves_dalloca_windows window
    (compile_internal_function ce params buf nr key tr view ctor imm_size fbody ret)
Proof
  strip_tac >> Cases_on `nr` >>
  simp[compile_internal_function_def, comp_ignore_bind_def] >> (
    irule dalloca_windows_bind >> reverse conj_tac
    >- (COND_CASES_TAC >> windows_tac []) >>
    rpt gen_tac >> BETA_TAC >>
    NTAC 6 (irule dalloca_windows_bind >> reverse conj_tac
      >- windows_tac [dalloca_windows_internal_param_decls,
                      compile_fixed_region_with_id_def, dalloca_windows_emit, mk_inst_def] >>
      rpt gen_tac >> BETA_TAC) >>
    match_mp_tac (Q.ISPEC `\env. env.ce_func_defaults = ce.ce_func_defaults`
      (Q.GEN `P` dalloca_windows_bind_result)) >>
    conj_tac >- simp[dalloca_windows_return] >>
    conj_tac >- simp[comp_return_def] >>
    gen_tac >> strip_tac >> BETA_TAC >>
    match_mp_tac (Q.ISPEC `\env. env.ce_func_defaults = ce.ce_func_defaults`
      (Q.GEN `P` dalloca_windows_bind_result)) >>
    conj_tac >- simp[dalloca_windows_materialize_internal_params] >>
    conj_tac >- fs[materialize_internal_params_defaults] >>
    rpt strip_tac >> BETA_TAC >> windows_tac [] >> first_assum irule >> fs[])
QED

Theorem dalloca_windows_external_fn_bodies:
  !pkgs. EVERY (\(lbl,ce,args,cds,pay,nr,key,tr,vw,fbody,rt).
    preserves_dalloca_windows window
      (compile_external_function_body ce args nr key tr vw fbody rt)) pkgs ==>
  preserves_dalloca_windows window (compile_external_fn_bodies pkgs)
Proof
  Induct >> simp[compile_external_fn_bodies_def, dalloca_windows_return] >>
  gen_tac >> PairCases_on `h` >>
  simp[compile_external_fn_bodies_def] >> strip_tac >> windows_tac []
QED

Theorem dalloca_windows_internal_fn_bodies:
  !pkgs. EVERY (\(lbl,ce,ps,buf,nr,key,tr,vw,ctor,im,fbody,rt).
    preserves_dalloca_windows window
      (compile_internal_function ce ps buf nr key tr vw ctor im fbody rt)) pkgs ==>
  preserves_dalloca_windows window (compile_internal_fn_bodies pkgs)
Proof
  Induct >> simp[compile_internal_fn_bodies_def, dalloca_windows_return] >>
  gen_tac >> PairCases_on `h` >>
  simp[compile_internal_fn_bodies_def] >> strip_tac >> windows_tac []
QED

Theorem dalloca_windows_generate_runtime:
  EVERY (\(lbl,ce,args,cds,pay,nr,key,tr,vw,fbody,rt).
    preserves_dalloca_windows window
      (compile_external_function_body ce args nr key tr vw fbody rt)) exts /\
  EVERY (\(lbl,ce,ps,buf,nr,key,tr,vw,ctor,im,fbody,rt).
    preserves_dalloca_windows window
      (compile_internal_function ce ps buf nr key tr vw ctor im fbody rt)) ints /\
  (case fallback of NONE => T
   | SOME (ce,pay,nr,key,tr,vw,fbody,rt) =>
     preserves_dalloca_windows window (compile_fallback_body ce pay nr key tr vw fbody rt)) ==>
  preserves_dalloca_windows window
    (compile_generate_runtime sels exts ints fallback strategy 0 0 [] info)
Proof
  Cases_on `strategy` >> Cases_on `fallback` >>
  TRY (rename1 `SOME pkg` >> PairCases_on `pkg`) >>
  simp[compile_generate_runtime_def] >> rpt strip_tac >>
  windows_tac [dalloca_windows_dispatch, dalloca_windows_external_fn_bodies,
               dalloca_windows_internal_fn_bodies]
QED

Theorem dalloca_windows_common_function_body:
  (!env lc rt. env.ce_func_defaults = ce.ce_func_defaults ==>
     preserves_dalloca_windows window (compile_stmts env lc rt fbody)) ==>
  preserves_dalloca_windows window
    (compile_common_function_body ce args kwvars nr key tr view fbody ret)
Proof
  strip_tac >> simp[compile_common_function_body_def] >>
  match_mp_tac (Q.ISPEC `\env. env.ce_func_defaults = ce.ce_func_defaults`
    (Q.GEN `P` dalloca_windows_bind_result)) >>
  simp[dalloca_windows_register_positional_args, register_positional_args_defaults,
       register_kwarg_vars_defaults] >>
  rpt strip_tac >> irule dalloca_windows_guarded_body >> metis_tac[]
QED

Theorem dalloca_windows_group_entries[local]:
  !entries.
    (!e ct. MEM e (MAP (\(_,_,_,d). d) kwvars) ==>
       preserves_dalloca_windows window (compile_expr common.ec_env ct e)) ==>
    preserves_dalloca_windows window
      (compile_group_entries method entries common kwvars off)
Proof
  Induct >> simp[compile_group_entries_def, dalloca_windows_return] >>
  gen_tac >> PairCases_on `h` >>
  simp[compile_group_entries_def, compile_entry_point_kwargs_def] >> strip_tac >>
  windows_tac [dalloca_windows_init_kwargs]
QED

Definition runtime_external_package_windows_def:
  runtime_external_package_windows window (lbl,ce,args,cds,pay,nr,key,tr,vw,fbody,rt) =
    preserves_dalloca_windows window (compile_external_function_body ce args nr key tr vw fbody rt)
End

Definition runtime_external_job_windows_def:
  runtime_external_job_windows window (ExternalLegacyJob pkg) =
    runtime_external_package_windows window pkg /\
  runtime_external_job_windows window (ExternalCommonJob common kwvars) =
    (!env lc rt. env.ce_func_defaults = common.ec_env.ce_func_defaults ==>
      preserves_dalloca_windows window (compile_stmts env lc rt common.ec_body))
End

Definition runtime_external_group_windows_def:
  runtime_external_group_windows window (ExternalSingle sel pkg) =
    runtime_external_package_windows window pkg /\
  runtime_external_group_windows window (ExternalDefaults common entries specs offset) =
    ((!env lc rt. env.ce_func_defaults = common.ec_env.ce_func_defaults ==>
        preserves_dalloca_windows window (compile_stmts env lc rt common.ec_body)) /\
     (!e ct. MEM e (MAP (\(_,_,d). d) specs) ==>
        preserves_dalloca_windows window (compile_expr common.ec_env ct e)))
End

Theorem external_group_job_windows[local]:
  !groups st.
    EVERY (runtime_external_group_windows window) groups ==>
    EVERY (runtime_external_job_windows window)
      (FST (compile_external_groups method groups st))
Proof
  Induct >> simp[compile_external_groups_def, comp_return_def] >>
  Cases_on `h`
  >- (rename1 `ExternalSingle sel _` >> PairCases_on `sel` >>
      simp[compile_external_groups_def, runtime_external_group_windows_def,
           comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
      rpt gen_tac >> strip_tac >> rpt (pairarg_tac >> simp[]) >>
      gvs[runtime_external_job_windows_def] >> metis_tac[pairTheory.FST]) >>
  simp[compile_external_groups_def, runtime_external_group_windows_def,
       comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  rpt gen_tac >> strip_tac >> rpt (pairarg_tac >> simp[]) >>
  gvs[runtime_external_job_windows_def] >> metis_tac[pairTheory.FST]
QED

Theorem dalloca_windows_external_groups[local]:
  !groups.
    EVERY (runtime_external_group_windows window) groups ==>
    preserves_dalloca_windows window (compile_external_groups method groups)
Proof
  Induct >> simp[compile_external_groups_def, dalloca_windows_return] >>
  Cases_on `h`
  >- (rename1 `ExternalSingle sel _` >> PairCases_on `sel` >>
      simp[compile_external_groups_def, runtime_external_group_windows_def] >>
      rpt strip_tac >> windows_tac [dalloca_windows_selector_checks]) >>
  simp[compile_external_groups_def, runtime_external_group_windows_def] >>
  rpt strip_tac >>
  rename1 `compile_create_kwarg_allocas common.ec_env specs` >>
  irule dalloca_windows_bind_result >> simp[dalloca_windows_create_kwarg_allocas] >>
  qexists_tac `\kwvars. MAP (\(_,_,_,e). e) kwvars = MAP (\(_,_,e). e) specs` >>
  simp[dalloca_windows_kwarg_alloca_defaults] >>
  rpt strip_tac >> windows_tac [dalloca_windows_group_entries] >>
  metis_tac[dalloca_windows_group_entries]
QED

Theorem group_dispatch_jobs[local]:
  EVERY (runtime_external_group_windows window) groups ==>
  EVERY (runtime_external_job_windows window)
    (FST (compile_group_dispatch_linear groups fb st))
Proof
  simp[compile_group_dispatch_linear_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> strip_tac >>
  rpt (pairarg_tac >> simp[]) >> metis_tac[external_group_job_windows, pairTheory.FST]
QED

Theorem dalloca_windows_group_dispatch[local]:
  EVERY (runtime_external_group_windows window) groups ==>
  preserves_dalloca_windows window (compile_group_dispatch_linear groups fb)
Proof
  strip_tac >> simp[compile_group_dispatch_linear_def] >>
  windows_tac [dalloca_windows_external_groups]
QED

Theorem dalloca_windows_external_jobs[local]:
  !jobs. EVERY (runtime_external_job_windows window) jobs ==>
    preserves_dalloca_windows window (compile_external_jobs jobs)
Proof
  Induct >> simp[compile_external_jobs_def, dalloca_windows_return] >>
  Cases_on `h` >> TRY (rename1 `ExternalLegacyJob pkg` >> PairCases_on `pkg`) >>
  simp[compile_external_jobs_def, runtime_external_job_windows_def,
       runtime_external_package_windows_def] >>
  rpt strip_tac >> windows_tac [dalloca_windows_external_fn_bodies,
                               dalloca_windows_common_function_body]
QED

Theorem dalloca_windows_generate_grouped_runtime:
  EVERY (runtime_external_group_windows window) groups /\
  EVERY (\(lbl,ce,ps,buf,nr,key,tr,vw,ctor,im,fbody,rt).
    preserves_dalloca_windows window
      (compile_internal_function ce ps buf nr key tr vw ctor im fbody rt)) ints /\
  (case fallback of NONE => T
   | SOME (ce,pay,nr,key,tr,vw,fbody,rt) =>
     preserves_dalloca_windows window (compile_fallback_body ce pay nr key tr vw fbody rt)) ==>
  preserves_dalloca_windows window (compile_generate_grouped_runtime groups ints fallback)
Proof
  Cases_on `fallback` >> TRY (rename1 `SOME pkg` >> PairCases_on `pkg`) >>
  simp[compile_generate_grouped_runtime_def] >> rpt strip_tac >>
  irule dalloca_windows_bind >> conj_tac >> simp[dalloca_windows_fresh] >>
  gen_tac >> simp[] >> irule dalloca_windows_bind_result >>
  conj_tac >> simp[dalloca_windows_group_dispatch] >>
  qexists_tac `EVERY (runtime_external_job_windows window)` >> simp[group_dispatch_jobs] >>
  rpt strip_tac >>
  windows_tac [dalloca_windows_external_jobs, dalloca_windows_internal_fn_bodies]
QED
