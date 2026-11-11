(* Structural producers on the raw deployment unit that run_venom_pipeline_correct
 * consumes (the deploy counterparts of lower_vyper_runtime_unit_source_unit_ok,
 * _o1_shape_extras, _global_reserved and the eom/fixed-region facts).
 * TOP-LEVEL: deploy_unit_shape_ok (a piece of e2e_deploy_correctness).
 * Helpers: classify_functions_ctor_mem, lower_vyper_deploy_unit_source_unit_ok,
 * lower_vyper_deploy_unit_o1_shape_extras, lower_vyper_deploy_unit_eom_none,
 * o1_pipeline_global_reserved, generate_context_plan_reserved_wf.
 * The reservation's size is not bounded by the lowering; its well-formedness
 * comes from codegen's context plan (max_live_eom checks it), which sees the
 * same reservation since every O1 pass keeps ctx_global_reserved.
 *)
Theory ctorDeployShape
Ancestors
  list ctorDeployDefs o1PassContract unitShapeDefs staticLayoutDefs
  ctorUnitShape deployUnitProducers loweringShapeProps loweringShapeSource
  supportedProgram supportedNames compileVyper vyperCompiler
  o1PipelineCorrect o1ComposeSupport fcgPruning stackPlanGen
  venomPipelineRunner venomFnScheduleRunner venomFnScheduleRunnerProps
  ctorGeneratorShape loweringShapeDefs moduleLowering compileEnv context
  emitHelper venomInst ptrDiscipline

(* ===== The constructor's source ===== *)

Theorem classify_function_ctor_source_step[local]:
  !top acc mut nr rr fname args defaults ret body.
    SND (SND (SND (classify_function top acc))) =
      SOME (mut,nr,rr,fname,args,defaults,ret,body) ==>
    top = FunctionDecl Deploy mut nr rr fname args defaults ret body \/
    SND (SND (SND acc)) = SOME (mut,nr,rr,fname,args,defaults,ret,body)
Proof
  rpt gen_tac >> PairCases_on `acc` >> Cases_on `top` >>
  simp[classify_function_def] >>
  rename1 `case vis of External => _ | Internal => _ | Deploy => _` >>
  Cases_on `vis` >> rw[]
QED

Theorem classify_functions_ctor_mem:
  !tops mut nr rr fname args defaults ret body.
    SND (SND (SND (classify_functions tops))) =
      SOME (mut,nr,rr,fname,args,defaults,ret,body) ==>
    MEM (FunctionDecl Deploy mut nr rr fname args defaults ret body) tops
Proof
  Induct_on `tops` >- simp[classify_functions_def] >>
  rpt gen_tac >>
  simp[classify_functions_def] >> strip_tac >>
  drule classify_function_ctor_source_step >>
  strip_tac >- simp[] >>
  fs[GSYM classify_functions_def] >> metis_tac[]
QED

Theorem build_compile_env_non_internal_no_return_pc[local]:
  !tops vis mut fname args ret body use_trans.
    vis <> Internal ==>
    (build_compile_env tops vis mut fname args ret body use_trans).ce_return_pc =
      NONE
Proof
  rpt strip_tac >> simp[build_compile_env_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem package_constructor_shape_ok[local]:
  !tops use_trans nkey_map target cf cenv args pay nr nkey trans body ret.
    supported_program tops /\
    SND (SND (SND (classify_functions tops))) = SOME cf /\
    set_constructor_package_target target
      (package_constructor tops use_trans nkey_map cf) =
      (cenv, args, pay, nr, nkey, trans, body, ret) ==>
    cenv_static_ok cenv /\ cenv.ce_return_pc = NONE /\
    ~supported_stmts_expr_exists expr_shape_root body
Proof
  rpt gen_tac >> PairCases_on `cf` >> strip_tac >>
  drule classify_functions_ctor_mem >> strip_tac >>
  drule_all supported_program_function >> strip_tac >>
  drule supported_function_body_shape >> strip_tac >>
  gvs[package_constructor_def, set_constructor_package_target_def,
      update_cenv_nonreentrant_def, build_compile_env_non_internal_no_return_pc] >>
  simp[cenv_static_ok_def] >>
  metis_tac[build_compile_env_static, cenv_static_ok_def]
QED

Theorem package_internal_fn_ctor_shape_ok[local]:
  !tops use_trans nkey_map imm target src.
    supported_program tops /\
    MEM src (FST (SND (classify_functions tops))) ==>
    internal_fn_shape_ok
      (set_internal_package_target target
         (package_internal_fn tops use_trans nkey_map T imm src))
Proof
  rpt gen_tac >> PairCases_on `src` >> strip_tac >>
  drule (iffLR MEM_classify_internal) >> strip_tac >>
  drule_all supported_program_function >> strip_tac >>
  drule supported_function_body_shape >> strip_tac >>
  simp[package_internal_fn_def, set_internal_package_target_def,
       update_cenv_nonreentrant_def, internal_fn_shape_ok_def,
       cenv_static_ok_def] >>
  metis_tac[build_compile_env_static, cenv_static_ok_def]
QED

(* ===== The lowered unit ===== *)

(* The entry function of run_deploy_lowering is the generator's entry
   blocks, whose instructions are entry code (lowered_inst_ok F): no PARAM.
   The prefix is run_deploy_lowering_source_unit_ok's. *)
Theorem run_deploy_lowering_entry_no_params[local]:
  !has_constructor rpolicy runtime_bytecode immutables_len constructor_args
   data_size ctor_internal_fns cenv body is_payable is_nonreentrant nkey
   use_transient unit.
    run_deploy_lowering has_constructor rpolicy runtime_bytecode immutables_len
      constructor_args data_size ctor_internal_fns cenv body is_payable
      is_nonreentrant nkey use_transient "__deploy" = SOME unit /\
    (has_constructor ==>
      cenv_static_ok cenv /\ cenv.ce_return_pc = NONE /\
      ~supported_stmts_expr_exists expr_shape_root body) /\
    (~has_constructor ==> ctor_internal_fns = []) /\
    EVERY internal_fn_shape_ok ctor_internal_fns /\
    EVERY (\d. internal_label_ok (FST d))
      (internal_fn_descriptors ctor_internal_fns) /\
    ALL_DISTINCT (MAP FST (internal_fn_descriptors ctor_internal_fns)) ==>
    EVERY (\inst. ~is_param_opcode inst.inst_opcode)
      (fn_insts (HD unit.cu_context.ctx_functions))
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `~supported_stmts_expr_exists expr_shape_root ss` >>
  `(if has_constructor then ctor_internal_fns else []) = ctor_internal_fns`
    by (Cases_on `has_constructor` >> gvs[]) >>
  Cases_on `compile_generate_deploy has_constructor (LENGTH runtime_bytecode)
    immutables_len constructor_args data_size ctor_internal_fns cenv ss
    is_payable is_nonreentrant nkey use_transient
    (initial_compile_state "__deploy")` >>
  rename1 `_ = (u, st1)` >> Cases_on `u` >>
  drule compile_generate_deploy_shape >> simp[] >> strip_tac >>
  drule_all shape_state_source_certificates >> strip_tac >>
  `package_internal_blocks (internal_fn_descriptors ctor_internal_fns)
     (entry_blocks ++ FLAT segs) =
   SOME (entry_blocks,
         MAP2 (\d seg. mk_internal_function (FST d) seg (FST (SND d))
                         (SND (SND d))) (internal_fn_descriptors ctor_internal_fns)
              segs)`
    by (irule package_internal_blocks_segments >> asm_rewrite_tac [] >>
        REWRITE_TAC[EVERY_MEM] >> gen_tac >> strip_tac >> BETA_TAC >>
        irule deploy_internal_label_separate >> fs[EVERY_MEM]) >>
  qpat_x_assum `run_deploy_lowering _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `all_blocks st1 = _`
    (assume_tac o REWRITE_RULE[all_blocks_def]) >>
  gs[run_deploy_lowering_def, extract_context_with_internals_def] >>
  strip_tac >> gvs[install_immutable_reservation_def, mk_venom_context_def] >>
  simp[fn_insts_def, mk_raw_function_def, EVERY_MEM,
       MEM_fn_insts_blocks_iff, PULL_EXISTS] >>
  rpt strip_tac >> gvs[EVERY_MEM] >> res_tac >>
  gvs[lowered_inst_ok_def]
QED

(* The facts of the unpacked lower_vyper_deploy_unit that
   run_deploy_lowering_source_unit_ok asks for. *)
Theorem lower_vyper_deploy_unit_run[local]:
  !tops rpolicy runtime_bc unit.
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME unit /\
    supported_program tops ==>
    ?has_constructor imm args ctor_internal_fns cenv body pay nr nkey trans.
      run_deploy_lowering has_constructor rpolicy runtime_bc imm args 0
        ctor_internal_fns cenv body pay nr nkey trans "__deploy" = SOME unit /\
      (has_constructor ==>
        cenv_static_ok cenv /\ cenv.ce_return_pc = NONE /\
        ~supported_stmts_expr_exists expr_shape_root body) /\
      (~has_constructor ==> ctor_internal_fns = []) /\
      EVERY internal_fn_shape_ok ctor_internal_fns /\
      EVERY (\d. internal_label_ok (FST d))
        (internal_fn_descriptors ctor_internal_fns) /\
      ALL_DISTINCT (MAP FST (internal_fn_descriptors ctor_internal_fns))
Proof
  rpt gen_tac >> simp[lower_vyper_deploy_unit_def] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> rpt strip_tac >>
  first_x_assum (irule_at Any) >>
  Cases_on `ctor_fn` >> gvs[internal_fn_descriptors_def] >>
  rename1 `classify_functions tops = (ext_fns, int_fns, fb_fn, SOME cf)` >>
  `SND (SND (SND (classify_functions tops))) = SOME cf` by simp[] >>
  drule_all package_constructor_shape_ok >> strip_tac >> simp[] >>
  `ALL_DISTINCT (MAP (\p. FST (SND (SND (SND p))))
                   (FST (SND (classify_functions tops))))`
    by metis_tac[supported_names_internal_names_distinct,
                 supported_program_names, supported_declaration_names_unique] >>
  qspecl_then [`tops`, `T`] mp_tac internal_descriptors_ok >>
  impl_tac >- simp[] >> simp[] >> strip_tac >>
  gs[GSYM MAP_MAP_o, internal_fn_descriptors_set_internal_package_target,
     internal_fn_descriptors_MAP_package_internal_fn, EVERY_MAP] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  irule package_internal_fn_ctor_shape_ok >> simp[]
QED

Theorem lower_vyper_deploy_unit_source_unit_ok:
  !tops rpolicy runtime_bc unit.
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME unit /\
    supported_program tops ==>
    o1_source_unit_ok unit
Proof
  rpt strip_tac >> drule_all lower_vyper_deploy_unit_run >> strip_tac >>
  drule run_deploy_lowering_source_unit_ok >> simp[]
QED

Theorem run_deploy_lowering_raw_defaults[local]:
  run_deploy_lowering has_constructor rpolicy runtime_bc immutables_len
    constructor_args data_size ctor_internal_fns cenv stmts is_payable
    is_nonreentrant nkey use_transient entry_label = SOME u ==>
  EVERY (\fn. fn.fn_eom = NONE) u.cu_context.ctx_functions /\
  unit_fmp_unsealed u
Proof
  simp[run_deploy_lowering_def, extract_context_with_internals_def,
       install_immutable_reservation_def, mk_venom_context_def,
       unit_fmp_unsealed_def] >>
  pairarg_tac >> gvs[AllCaseEqs()] >> rpt strip_tac >>
  gvs[mk_raw_function_def] >>
  drule package_internal_blocks_raw_defaults >>
  simp[EVERY_MEM, function_raw_metadata_defaults_def]
QED

Theorem lower_vyper_deploy_unit_eom_none:
  !tops rpolicy runtime_bc unit.
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME unit ==>
    EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
    unit_fmp_unsealed unit
Proof
  rpt gen_tac >> simp[lower_vyper_deploy_unit_def] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> rpt strip_tac >>
  drule run_deploy_lowering_raw_defaults >> simp[]
QED

(* The entry function is the unit's first (entry_fn_first) and names are
   distinct (lowering_context_ok), so it is the only one the entry names. *)
Theorem lower_vyper_deploy_unit_o1_shape_extras:
  !tops rpolicy runtime_bc unit.
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME unit /\
    supported_program tops ==>
    unit_entry_no_params unit /\ unit_fmp_unsealed unit
Proof
  rpt gen_tac >> strip_tac >>
  reverse conj_tac >- metis_tac[lower_vyper_deploy_unit_eom_none] >>
  drule_all lower_vyper_deploy_unit_run >> strip_tac >>
  drule_all run_deploy_lowering_entry_no_params >> strip_tac >>
  drule_all run_deploy_lowering_source_unit_ok >> strip_tac >>
  `entry_fn_first unit.cu_context` by
    fs[o1_source_unit_ok_def, unit_shape_ok_def] >>
  `ALL_DISTINCT (MAP (\f. f.fn_name) unit.cu_context.ctx_functions)` by
    (drule lower_vyper_deploy_unit_context_ok >>
     simp[lowering_context_ok_def, ctx_fn_names_def]) >>
  qpat_x_assum `entry_fn_first _`
    (strip_assume_tac o REWRITE_RULE [entry_fn_first_def]) >>
  rename1 `_ = efn :: rest` >>
  qpat_x_assum `_.ctx_functions = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >>
              rewrite_tac [unit_entry_no_params_def, entry_fn_no_params_def, th]) >>
  qx_gen_tac `g` >> simp_tac std_ss [MEM] >> rpt strip_tac
  >- fs[] >>
  `MEM g.fn_name (MAP (\f. f.fn_name) rest)` by
    (simp[MEM_MAP] >> metis_tac[]) >>
  gs[]
QED

(* ===== The reservation ===== *)

(* Every stage of the O1 pipeline keeps the global reservation: the pass
   runners only replace functions and relabel them. *)
Theorem run_configured_fn_passes_global_reserved[local]:
  run_configured_fn_passes runner rpolicy passes name unit supply =
    SOME (unit',supply') ==>
  unit'.cu_context.ctx_global_reserved = unit.cu_context.ctx_global_reserved
Proof
  simp[run_configured_fn_passes_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  drule apply_unit_label_map_global_reserved >> simp[]
QED

Theorem run_named_fn_schedules_global_reserved[local]:
  !names unit supply unit' supply'.
    run_named_fn_schedules runner rpolicy passes names unit supply =
      SOME (unit',supply') ==>
    unit'.cu_context.ctx_global_reserved = unit.cu_context.ctx_global_reserved
Proof
  Induct >> simp[run_named_fn_schedules_def] >> rpt gen_tac >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule run_configured_fn_passes_global_reserved >>
  first_x_assum drule >> simp[]
QED

Theorem run_pipeline_stages_global_reserved[local]:
  !stages unit supply unit' supply'.
    run_pipeline_stages rpolicy stages unit supply = SOME (unit',supply') ==>
    unit'.cu_context.ctx_global_reserved = unit.cu_context.ctx_global_reserved
Proof
  Induct >> simp[run_pipeline_stages_def] >> Cases >>
  simp[run_pipeline_stage_def, run_mapped_functions_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> first_x_assum drule >>
  imp_res_tac run_named_fn_schedules_global_reserved >> gvs[]
QED

Theorem o1_pipeline_global_reserved:
  !rpolicy unit out.
    o1_pipeline rpolicy unit = SOME out ==>
    out.po_unit.cu_context.ctx_global_reserved =
      unit.cu_context.ctx_global_reserved
Proof
  rpt strip_tac >> fs[o1_pipeline_def] >>
  drule o1_driver_runs >> strip_tac >>
  drule run_pipeline_stages_global_reserved >>
  fs[run_callee_first_def] >>
  drule run_named_fn_schedules_global_reserved >>
  simp[prune_unit_fcg_unreachable_fields]
QED

(* Codegen's context plan exists only for a well-formed reservation. *)
Theorem generate_context_plan_reserved_wf:
  !ctx cp.
    generate_context_plan ctx = SOME cp ==>
    reserved_intervals_wf ctx.ctx_global_reserved
Proof
  rpt strip_tac >> CCONTR_TAC >>
  gvs[generate_context_plan_def, generate_context_plan_with_def,
      max_live_eom_def]
QED

Theorem deploy_unit_shape_ok:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx
    ==>
    o1_source_unit_ok dunit /\ unit_entry_no_params dunit /\
    unit_fmp_unsealed dunit /\
    EVERY (\fn. fn.fn_eom = NONE) dunit.cu_context.ctx_functions /\
    fixed_region_reserved (imm_len tops) dunit.cu_context /\
    reserved_intervals_wf dunit.cu_context.ctx_global_reserved
Proof
  rpt gen_tac >> simp[deploy_phases_def, deploy_source_ok_def] >>
  strip_tac >>
  drule_all lower_vyper_deploy_unit_source_unit_ok >> strip_tac >>
  drule_all lower_vyper_deploy_unit_o1_shape_extras >> strip_tac >>
  drule lower_vyper_deploy_unit_eom_none >> strip_tac >>
  `fixed_region_reserved (imm_len tops) dunit.cu_context` by
    (drule lower_vyper_deploy_unit_global_reserved >>
     rw[fixed_region_reserved_def, imm_len_def] >> gvs[]) >>
  simp[] >>
  drule o1_pipeline_global_reserved >> strip_tac >>
  drule generate_context_plan_reserved_wf >> gvs[]
QED
