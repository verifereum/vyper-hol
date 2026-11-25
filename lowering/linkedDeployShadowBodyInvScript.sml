Theory linkedDeployShadowBodyInv
Ancestors
  linkedCompiledCalleeSource linkedShadowBodyInvRuns bodyFullShadowInternalRun
  bodyFullShadowBodyInv linkedDeployConstructorRun bodyInvSplit compileUnit moduleLowering compileEnv vyperCompiler
  gasShadowDeployRunner gasShadowDeploy gasShadowState gasShadowUnit
  gasShadowModuleDefs gasShadow constSubstMods immSectionDead venomInst list pair option

Theorem deploy_shadow_body_inv_mods:
  check_contract T layouts addr mods = SOME art /\
  lower_vyper_deploy_unit_mods mods exps rp runtime_bc = SOME unit /\
  classify_functions_unit mods exps = (exts,ints,fb,SOME cf,imp_ctors) /\
  set_constructor_package_target rp.rpol_target
    (package_constructor_unit mods T (K global_nonreentrant_slot) cf) =
    (ce,args,pay,nr,key,trans,ctor_body,ret) /\
  ips = MAP (set_internal_package_target rp.rpol_target o
    package_internal_fn_unit mods T (K global_nonreentrant_slot) T
      (imm_len_mods mods))
    (order_internals_unit (deploy_internal_order_unit (SOME cf) (ints ++ imp_ctors))
      (ints ++ imp_ctors)) /\
  run_deploy_lowering T rp runtime_bc (imm_len_mods mods) args 0
    (MAP gas_shadow_internal_package ips) (gas_shadow_env T ce)
    (MAP gas_shadow_stmt ctor_body) pay nr key trans "__deploy" = SOME shadow_unit ==>
  shadow_body_inv_mods mods exps unit.cu_context shadow_unit.cu_context
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `srcs = order_internals_unit (deploy_internal_order_unit (SOME cf) (ints ++ imp_ctors))
    (ints ++ imp_ctors)` >>
  `ips = MAP (set_internal_package_target rp.rpol_target o
    package_internal_fn_unit mods T (K global_nonreentrant_slot) T (imm_len_mods mods)) srcs` by
    simp[Abbr `srcs`] >>
  `run_deploy_lowering T rp runtime_bc (imm_len_mods mods) args 0 ips ce
    ctor_body pay nr key trans "__deploy" = SOME unit` by
    (drule_all linked_deploy_constructor_run >> simp[]) >>
  qpat_assum `run_deploy_lowering T _ _ _ _ _ ips _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac deploy_internal_run_labels) >>
  disch_then (qx_choosel_then [`start`,`final`,`raw`,`data`] strip_assume_tac) >>
  qpat_assum `run_deploy_lowering T _ _ _ _ _ (MAP gas_shadow_internal_package ips)
      _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac deploy_internal_run_labels) >>
  disch_then (qx_choosel_then [`startS`,`finalS`,`rawS`,`dataS`] strip_assume_tac) >>
  `gas_shadow_state start startS` by
    (qspecl_then [`T`,`LENGTH runtime_bc`,`imm_len_mods mods`,`args`,`0`,`[]`,`ce`,
        `ctor_body`,`pay`,`nr`,`key`,`trans`] mp_tac
      (Q.INST [`sd` |-> `T`] gas_shadow_compile_generate_deploy) >>
     rewrite_tac[gas_shadow_compiles_def, MAP] >>
     disch_then (qspecl_then [`initial_compile_state "__deploy"`,
       `initial_compile_state "__deploy"`] mp_tac) >>
     asm_rewrite_tac[gas_shadow_state_refl]) >>
  `gas_shadow_context unit.cu_context shadow_unit.cu_context` by
    (qspecl_then [`T`,`rp`,`runtime_bc`,`imm_len_mods mods`,`args`,`0`,`ips`,`ce`,
       `ctor_body`,`pay`,`nr`,`key`,`trans`,`"__deploy"`] mp_tac gas_shadow_run_deploy_lowering >>
     asm_rewrite_tac[] >> simp[optionTheory.OPTREL_def, gas_shadow_unit_def]) >>
  `unit.cu_context.ctx_functions = raw.ctx_functions /\
    shadow_unit.cu_context.ctx_functions = rawS.ctx_functions` by
    simp[install_immutable_reservation_def] >>
  mp_tac (Q.INST [`is_ctor` |-> `T`, `name` |-> `"__deploy"`,
    `bc` |-> `runtime_bc`, `unit` |-> `unit`, `shadow_unit` |-> `shadow_unit`,
    `raw` |-> `raw`, `rawS` |-> `rawS`, `srcs` |-> `srcs`, `ips` |-> `ips`,
    `start` |-> `start`, `startS` |-> `startS`, `run_end` |-> `final`,
    `run_endS` |-> `finalS`, `data` |-> `data`, `dataS` |-> `dataS`]
    (SPEC_ALL shadow_body_inv_mods_from_internal_runs)) >>
  impl_tac
  >- (asm_rewrite_tac[] >> simp_tac bool_ss [] >>
     qx_genl_tac [`src`,`tops`,`mode`,`vis`,`mut`,`nr'`,`rr`,`fname`,`args'`,`dflts`,`ret'`,`ss`,`callee`] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     mp_tac (Q.INST [`is_ctor` |-> `T`, `rp` |-> `rp`, `exps` |-> `exps`,
        `ctx` |-> `unit.cu_context`, `raw` |-> `raw`,
        `name` |-> `"__deploy"`, `ips` |-> `ips`, `final` |-> `final`, `data` |-> `data`,
        `ctor` |-> `SOME cf`, `srcs` |-> `srcs`, `imp_ctors` |-> `imp_ctors`,
        `nr` |-> `nr'`, `args` |-> `args'`, `ret` |-> `ret'`]
        (SPEC_ALL linked_compiled_callee_source_member)) >>
     simp_tac bool_ss [COND_CLAUSES] >>
     asm_rewrite_tac[] >>
     impl_tac >-
       (qx_gen_tac `pkg` >> PairCases_on `pkg` >>
        qpat_assum `Abbrev (srcs = _)` (fn eq =>
          PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] eq]) >>
        disch_then (MATCH_ACCEPT_TAC o MATCH_MP order_internals_unit_mem)) >>
     simp[]) >>
  disch_then ACCEPT_TAC
QED
