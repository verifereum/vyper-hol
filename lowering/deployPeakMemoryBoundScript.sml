(* The deploy entry and its internal functions use the same raw recorder as
   the runtime unit. The deployment prefix and epilogue emit no DALLOCA. *)
Theory deployPeakMemoryBound
Ancestors
  runtimePeakMemoryPackage runtimePeakMemoryRuntime runtimePeakMemoryModule
  runtimePeakMemoryProof runtimePeakMemoryCode runtimePeakMemorySourceGate
  runtimePeakMemoryArity runtimePeakMemoryStmt runtimePeakMemoryControl
  runtimePeakMemoryStmtOps stmtLowering immSectionDead lowerDloadDefs
  loweringBudgetAccountCodes loweringFunctionOpcodes deployUnitProducers
  ctorDeployDefs e2eDeployDefs compileVyper moduleLowering compileEnv
  supportedExprTraverse supportedStmtTraverse constSubst context emitHelper
  vyperCompiler vyperTypeContract vyperAST contextCodegenRel contextRawReachable
  venomInst venomState venomLayout list words arithmetic finite_map

val _ = Parse.hide "tops";
val _ = Parse.hide "body";

fun windows_tac thms =
  rpt (FIRST [
    CHANGED_TAC (simp(thms @ [LET_THM, pairTheory.FORALL_PROD, pairTheory.UNCURRY_DEF,
      dalloca_windows_emit_helpers, dalloca_windows_new_block, dalloca_windows_get,
      dalloca_windows_fresh, dalloca_windows_return, dalloca_windows_alloc_buffer,
      dalloca_windows_nonreentrant])),
    gen_tac, irule dalloca_windows_bind >> conj_tac,
    irule dalloca_windows_ignore_bind >> conj_tac,
    COND_CASES_TAC, BasicProvers.TOP_CASE_TAC]);

Theorem dalloca_windows_register_constructor_args[local]:
  !args ce off size.
    preserves_dalloca_windows window
      (compile_register_constructor_args ce args off size)
Proof
  Induct >> simp[compile_register_constructor_args_def, dalloca_windows_return] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[compile_register_constructor_args_def] >>
  windows_tac [dalloca_windows_decode_args]
QED

Theorem dalloca_windows_deploy_epilogues[local]:
  preserves_dalloca_windows window (compile_constructor_epilogue sz ilen imm_buf) /\
  preserves_dalloca_windows window (compile_simple_deploy sz ilen)
Proof
  simp[compile_constructor_epilogue_def, compile_simple_deploy_def] >>
  rpt conj_tac >> windows_tac []
QED

Theorem dalloca_windows_generate_deploy:
  (has ==>
    (!env. env.ce_func_defaults = ce.ce_func_defaults ==>
      preserves_dalloca_windows window (compile_stmts env NoLoop NoneT fbody)) /\
    EVERY (\(lbl,env,ps,buf,nr,key,tr,vw,ctor,im,ss,rt).
      preserves_dalloca_windows window
        (compile_internal_function env ps buf nr key tr vw ctor im ss rt)) ints) ==>
  preserves_dalloca_windows window
    (compile_generate_deploy has sz ilen args data_size ints ce fbody pay nr key tr)
Proof
  Cases_on `has` >>
  simp[compile_generate_deploy_def] >>
  all_tac >~ [`compile_simple_deploy sz ilen`]
  >- windows_tac [dalloca_windows_deploy_epilogues] >>
  strip_tac >>
  `?a b c v. ce.ce_nonreentrant = (a,b,c,v)` by metis_tac[pairTheory.ABS_PAIR_THM] >>
  irule dalloca_windows_ignore_bind >> conj_tac
  >- windows_tac [] >>
  irule dalloca_windows_bind >> reverse conj_tac
  >- windows_tac [compile_fixed_region_with_id_def, dalloca_windows_emit, mk_inst_def] >>
  gen_tac >> BETA_TAC >>
  match_mp_tac (Q.ISPEC `\env. env.ce_func_defaults = ce.ce_func_defaults`
    (Q.GEN `P` dalloca_windows_bind_result)) >>
  simp[register_constructor_args_defaults,
       dalloca_windows_register_constructor_args] >>
  rpt strip_tac >> windows_tac [dalloca_windows_deploy_epilogues,
       dalloca_windows_internal_fn_bodies, dalloca_windows_register_constructor_args] >>
  first_assum irule >> simp[]
QED

Theorem run_deploy_lowering_dalloca_windows:
  run_deploy_lowering has rpolicy bc ilen args data_size ints ce ss pay nr key tr lbl =
    SOME dunit /\
  preserves_dalloca_windows window
    (compile_generate_deploy has (LENGTH bc) ilen args data_size ints ce ss pay nr key tr) ==>
  !fn bb. MEM fn dunit.cu_context.ctx_functions /\ MEM bb fn.fn_blocks ==>
    dalloca_windows window bb.bb_instructions
Proof
  simp[run_deploy_lowering_def] >> pairarg_tac >> gvs[AllCaseEqs()] >>
  rpt strip_tac >> gvs[install_immutable_reservation_def] >>
  metis_tac[extract_context_dalloca_windows, preserves_dalloca_windows_def,
            dalloca_windows_initial]
QED

Theorem dalloca_windows_packaged_constructor[local]:
  (!chunk. raw_call_dalloca_chunk chunk 1 ==> window chunk 1) /\
  (!chunk. create_copy_dalloca_chunk chunk 5 ==> window chunk 5) /\
  check_contract T layouts (addr:160 word) [(NONE, source_tops)] = SOME deploy_art /\
  check_contract F layouts addr [(NONE, source_tops)] = SOME art /\
  (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
    !vis mut nr rr name args ds ret ss.
    MEM (FunctionDecl vis mut nr rr name args ds ret ss) source_tops /\
    (vis = Deploy \/ vis = Internal) ==>
    ~supported_stmts_expr_exists blueprint_create_root ss /\
    EVERY (\d. ~supported_expr_exists blueprint_create_root d) ds) /\
  SND (SND (SND (classify_functions source_tops))) =
    SOME (mut,nr,rr,name,args,dflts,ret,ss) /\
  set_constructor_package_target target
    (package_constructor source_tops tr keys (mut,nr,rr,name,args,dflts,ret,ss)) =
    (ce,params,pay,nonreentrant,nkey,use_trans,fbody,ret_ty) /\
  env.ce_func_defaults = ce.ce_func_defaults ==>
  preserves_dalloca_windows
    window
    (compile_stmts env NoLoop NoneT fbody)
Proof
  strip_tac >>
  drule classify_functions_ctor_mem >> strip_tac >>
  `~supported_stmts_expr_exists short_builtin_args raw_body /\
   EVERY (\e. ~supported_expr_exists short_builtin_args e) raw_defaults` by
    metis_tac[checked_source_builtin_arity] >>
  drule_all (Q.INST [`stmts` |-> `raw_body`, `dflts` |-> `raw_defaults`]
    subst_checked_fn_builtin_arity) >> strip_tac >>
  `compile_env_builtin_arity
    (build_compile_env source_tops Deploy mut (name:string) args ret ss tr)` by
    metis_tac[build_compile_env_builtin_arity] >>
  gvs[package_constructor_def, set_constructor_package_target_def,
      update_cenv_nonreentrant_def, subst_consts_fn_def] >>
  irule dalloca_windows_packaged_stmts >>
  simp[GSYM LEFT_EXISTS_AND_THM] >>
  qexists_tac `build_compile_env source_tops Deploy mut name args ret
    (subst_consts_stmts (module_consts_env source_tops []) raw_body) tr` >>
  simp[] >>
  conj_tac
  >- (disch_tac >>
      qpat_assum `(?chunk. create_blueprint_dalloca_chunk chunk 1 /\
                           ~window chunk 1) ==> _`
        (fn th => drule th >> strip_tac) >>
      metis_tac[build_compile_env_blueprint_free]) >>
  disch_tac >>
  `~supported_stmts_expr_exists blueprint_create_root raw_body /\
   EVERY (\e. ~supported_expr_exists blueprint_create_root e) raw_defaults` by
    metis_tac[] >>
  drule_all (Q.INST [`stmts` |-> `raw_body`, `dflts` |-> `raw_defaults`]
    subst_consts_fn_blueprint_free) >> simp[]
QED

Theorem lower_vyper_deploy_unit_dalloca_windows_for:
  (!chunk. raw_call_dalloca_chunk chunk 1 ==> window chunk 1) /\
  (!chunk. create_copy_dalloca_chunk chunk 5 ==> window chunk 5) /\
  lower_vyper_deploy_unit source_tops rpolicy runtime_bc = SOME dunit /\
  deploy_typing_ok source_tops am tx /\
  (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
    !vis mut nr rr name args ds ret ss.
    MEM (FunctionDecl vis mut nr rr name args ds ret ss) source_tops /\
    (vis = Deploy \/ vis = Internal) ==>
    ~supported_stmts_expr_exists blueprint_create_root ss /\
    EVERY (\d. ~supported_expr_exists blueprint_create_root d) ds) ==>
  !fn bb. MEM fn dunit.cu_context.ctx_functions /\ MEM bb fn.fn_blocks ==>
    dalloca_windows window bb.bb_instructions
Proof
  strip_tac >>
  fs[deploy_typing_ok_def] >>
  `~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
    !mut nr rr name args ds ret ss.
    MEM (FunctionDecl Internal mut nr rr name args ds ret ss) source_tops ==>
    ~supported_stmts_expr_exists blueprint_create_root ss /\
    EVERY (\d. ~supported_expr_exists blueprint_create_root d) ds` by
    metis_tac[] >>
  qpat_x_assum `lower_vyper_deploy_unit _ _ _ = _` mp_tac >>
  simp[lower_vyper_deploy_unit_def] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule (REWRITE_RULE [GSYM AND_IMP_INTRO] run_deploy_lowering_dalloca_windows) >>
  disch_then (qspecl_then [`window`, `fn`, `bb`] mp_tac) >>
  impl_tac >-
    (simp[] >> irule dalloca_windows_generate_deploy >>
     Cases_on `ctor_fn` >> fs[] >>
     rename1 `classify_functions source_tops = (exts,ints,fb,SOME ctor)` >>
     PairCases_on `ctor` >> simp[] >>
     conj_tac
     >- (rpt strip_tac >> irule dalloca_windows_packaged_constructor >>
         rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]) >>
     qpat_assum `check_contract F _ _ _ = _` (fn checked =>
       mp_tac (Q.INST [`tr` |-> `T`, `target` |-> `rpolicy.rpol_target`,
             `keys` |-> `K global_nonreentrant_slot`, `ctor_mode` |-> `T`,
             `ilen` |-> `compute_immutables_len
                (get_struct_fields (make_struct_fields_map source_tops)) source_tops`,
             `order` |-> `deploy_internal_order
               (SND (SND (SND (classify_functions source_tops))))
               (FST (SND (classify_functions source_tops)))`]
         (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
           dalloca_windows_packaged_internals) checked))) >>
     simp[] >> impl_tac >- (simp[] >> gvs[]) >>
     simp[]) >>
  simp[]
QED

Theorem lower_vyper_deploy_unit_dalloca_windows[local]:
  lower_vyper_deploy_unit source_tops rpolicy runtime_bc = SOME dunit /\
  deploy_typing_ok source_tops am tx /\
  (!vis mut nr rr name args ds ret ss.
    MEM (FunctionDecl vis mut nr rr name args ds ret ss) source_tops /\
    (vis = Deploy \/ vis = Internal) ==>
    ~supported_stmts_expr_exists blueprint_create_root ss /\
    EVERY (\d. ~supported_expr_exists blueprint_create_root d) ds) ==>
  !fn bb. MEM fn dunit.cu_context.ctx_functions /\ MEM bb fn.fn_blocks ==>
    dalloca_windows (\chunk k. raw_call_dalloca_chunk chunk k \/
                               create_copy_dalloca_chunk chunk k) bb.bb_instructions
Proof
  strip_tac >>
  mp_tac (Q.INST [`window` |-> `\chunk k. raw_call_dalloca_chunk chunk k \/
                                  create_copy_dalloca_chunk chunk k`]
    lower_vyper_deploy_unit_dalloca_windows_for) >>
  simp[] >> metis_tac[]
QED

Theorem lower_vyper_deploy_unit_dynamic_peak_memory_from_unit:
  !tops rpolicy runtime_bc (dunit:compilation_unit) (cp_fmp:num) am tx
   (fmp:bytes32) vs vs0.
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
    deploy_typing_ok tops am tx /\
    ~vs.vs_halted /\
    vs.vs_accounts = accounts_after_transfer tx am.accounts /\
    (!vis mut nr rr name args dflts ret body.
       MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops /\
       (vis = Deploy \/ vis = Internal) ==>
       ~supported_stmts_expr_exists
         (\e. ?ty raw salted rof order es d.
            e = Call ty (CreateTarget (CreateFromBlueprint raw) salted rof order) es d)
         body /\
       EVERY (\d0. ~supported_expr_exists
         (\e. ?ty raw salted rof order es d.
            e = Call ty (CreateTarget (CreateFromBlueprint raw) salted rof order) es d)
         d0) dflts) /\
    vs.vs_initial_fmp = n2w cp_fmp /\
    vs.vs_fmp = n2w cp_fmp /\
    cp_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    imm_len tops + unit_alloca_budget dunit.cu_context +
      32 * ctx_dload_count dunit.cu_context <= w2n fmp /\
    raw_variant fmp vs0 vs /\
    LENGTH vs0.vs_outcomes < 2 ** 64 /\
    outcomes_accounts_typed (SOME vs0.vs_outcomes) /\
    LENGTH vs0.vs_call_ctx.cc_calldata < 2 ** 64 ==>
    !fn i s.
      raw_reachable vs0 dunit.cu_context fn i s ==>
      s.vs_initial_fmp = fmp /\
      w2n s.vs_initial_fmp <= w2n s.vs_fmp /\
      fmp_frontier_rel cp_fmp (w2n fmp)
        (cp_fmp + (w2n s.vs_fmp - w2n fmp)) s.vs_fmp /\
      (i.inst_opcode = DALLOCA ==>
       w2n s.vs_fmp <= w2n fmp + 2 ** 64 * 2 ** 64 /\
       !sz_op sz.
         i.inst_operands = [sz_op] /\ eval_operand sz_op s = SOME sz ==>
         w2n s.vs_fmp + venomLayout$ceil32 (w2n sz) < dimword (:256))
Proof
  rpt gen_tac >> strip_tac >>
  `blueprint_create_root =
    (\e. ?ty raw salted rof order es d.
       e = Call ty (CreateTarget (CreateFromBlueprint raw) salted rof order) es d)` by
    simp[FUN_EQ_THM, blueprint_create_root_def] >>
  `lowering_context_ok dunit.cu_context` by
    metis_tac[lower_vyper_deploy_unit_context_ok] >>
  `account_code_lengths_ok vs.vs_accounts` by
    fs[deploy_typing_ok_def, initial_account_codes_after_transfer] >>
  mp_tac (Q.INST [`source_tops` |-> `tops`, `rpolicy` |-> `rpolicy`,
    `runtime_bc` |-> `runtime_bc`, `am` |-> `am`, `tx` |-> `tx`, `dunit` |-> `dunit`]
    lower_vyper_deploy_unit_dalloca_windows) >>
  impl_tac >- asm_rewrite_tac[] >> strip_tac >>
  `!fn. MEM fn dunit.cu_context.ctx_functions ==> ALL_DISTINCT (fn_labels fn)` by
    fs[lowering_context_ok_def, EVERY_MEM] >>
  mp_tac (Q.INST [`ctx` |-> `dunit.cu_context`] raw_dynamic_peak_memory_from_windows) >>
  impl_tac >- (asm_rewrite_tac[] >> metis_tac[active_inst_dalloca_windows]) >>
  simp[]
QED

Theorem lower_vyper_deploy_unit_raw_headroom:
  lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
  deploy_typing_ok tops am tx /\
  vi.vs_accounts = accounts_after_transfer tx am.accounts /\
  ~vi.vs_halted /\ vi.vs_fmp = vi.vs_initial_fmp /\
  w2n vi.vs_initial_fmp < 2 ** 254 /\
  LENGTH vi.vs_outcomes < 2 ** 64 /\
  outcomes_accounts_typed (SOME vi.vs_outcomes) /\
  LENGTH vi.vs_call_ctx.cc_calldata < 2 ** 64 ==>
  !fn i s. raw_reachable vi dunit.cu_context fn i s ==> dalloca_fmp_headroom i s
Proof
  strip_tac >>
  `lowering_context_ok dunit.cu_context` by
    metis_tac[lower_vyper_deploy_unit_context_ok] >>
  `account_code_lengths_ok vi.vs_accounts` by
    fs[deploy_typing_ok_def, initial_account_codes_after_transfer] >>
  mp_tac (Q.INST [`source_tops` |-> `tops`, `rpolicy` |-> `rpolicy`,
    `runtime_bc` |-> `runtime_bc`, `am` |-> `am`, `tx` |-> `tx`, `dunit` |-> `dunit`,
    `window` |-> `\chunk k. raw_call_dalloca_chunk chunk k \/
       create_copy_dalloca_chunk chunk k \/ create_blueprint_dalloca_chunk chunk k`]
    lower_vyper_deploy_unit_dalloca_windows_for) >>
  (impl_tac >- (strip_tac >> metis_tac[])) >> strip_tac >>
  `!fn. MEM fn dunit.cu_context.ctx_functions ==> ALL_DISTINCT (fn_labels fn)` by
    fs[lowering_context_ok_def, EVERY_MEM] >>
  mp_tac (Q.INST [`ctx` |-> `dunit.cu_context`] raw_headroom_from_dalloca_windows) >>
  impl_tac >- (asm_rewrite_tac[] >> metis_tac[active_inst_dalloca_windows_with_blueprint]) >>
  simp[]
QED
