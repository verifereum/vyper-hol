(* One execution fuel for a successfully lowered linked deploy unit. *)
Theory linkedDeployFuel
Ancestors
  bodyFullShadowInternalCode compileUnit compileUnitPackageShape compileVyper compileEnv ctorDeployRunBounded
  ctorDeployEntryLabels ctorDeployLoweringCode deployUnitProducers linkedFuelPackage
  moduleLowering vyperCompiler loweringShapeDefs loweringShapeProps loweringShapeSource
  fragFuel fragFuelPackage fragFuelStmtBase fragFuelStmt fragFuelContext fragFuelRuntimeBody
  emitHelper venomExecSemantics passSimulationDefs venomInst
  supportedExprTraverse list pair

val _ = Parse.hide "body";
val _ = Parse.hide "size";

fun segment_fuel_tac pat =
  qpat_x_assum pat (assume_tac o MATCH_MP fuel_ok_at) >> pop_assum irule

Triviality deploy_generator_prefix_fuel:
  (!n. cenv_ptrs_below n ce) /\
  compile_generate_deploy T size len args data_size [] ce body pay nr key trans
    (initial_compile_state "__deploy") = ((), final) ==>
  fuel_okS ((=) (initial_compile_state "__deploy")) UNIV {} {}
    (\s. ((), final))
Proof
  strip_tac >>
  qpat_x_assum `compile_generate_deploy T _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  PURE_REWRITE_TAC [compile_generate_deploy_def, COND_CLAUSES,
                    ctor_code_cond_not, ctor_lock_flag_select] >>
  simp_tac bool_ss [comp_ignore_bind_def, comp_bind_def, comp_get_def, LET_THM,
                    compile_internal_fn_bodies_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `(if pay then _ else _) (initial_compile_state "__deploy") = ((),st_pay)` >>
  rename1 `(if len > 0 then _ else _) st_pay = (imm,st1)` >>
  rename1 `compile_register_constructor_args _ args 0 data_size st1 = (reg_env,st2)` >>
  rename1 `(if nr then compile_nonreentrant_lock key trans _ else _) st2 = ((),st3)` >>
  rename1 `fresh_label "ctor_exit" st3 = (exit_lbl,sa)` >>
  rename1 `compile_stmts _ NoLoop NoneT body sa = ((),sb)` >>
  rename1 `new_block exit_lbl sj = (old_bb,st_exit)` >>
  rename1 `(if nr then compile_nonreentrant_unlock key trans _ else _)
    st_exit = ((),st_epilogue)` >>
  qpat_x_assum `_ = final` (SUBST_ALL_TAC o SYM) >>
  rename1 `compile_constructor_epilogue size len imm st_epilogue = ((),final)` >>
  `cenv_ptrs_below st2.cs_next_var reg_env` by
    (irule compile_register_constructor_args_ptrs >>
     first_assum (irule_at Any) >> simp[cenv_ptrs_below_def] >>
     metis_tac[cenv_ptrs_below_def]) >>
  `fuel_okS ((=) st1) UNIV {} {} (\s. ((),st2))` by
    (segment_fuel_tac `compile_register_constructor_args _ _ _ _ st1 = _` >>
     simp[fuel_ok_compile_register_constructor_args]) >>
  `!k t v. fuel_ok UNIV {} {}
             (if nr then compile_nonreentrant_lock k t v else comp_return ()) /\
           fuel_ok UNIV {} {}
             (if nr then compile_nonreentrant_unlock k t v else comp_return ())` by
    (Cases_on `nr` >> simp[fuel_ok_return, fuel_ok_context_storage]) >>
  `fuel_okS ((=) st2) UNIV {} {} (\s. ((),st3))` by
    (segment_fuel_tac `_ st2 = ((),st3)` >> simp[comp_return_def]) >>
  `fuel_okS ((=) st_exit) UNIV {} {} (\s. ((),st_epilogue))` by
    (segment_fuel_tac `_ st_exit = ((),st_epilogue)` >> simp[comp_return_def]) >>
  `st2.cs_next_var <= st3.cs_next_var` by
    metis_tac[fuel_ok_next, comp_return_def] >>
  `sa.cs_next_var = st3.cs_next_var` by
    (qpat_x_assum `fresh_label _ st3 = _` mp_tac >>
     rw[fresh_label_def] >> simp[]) >>
  `fuel_okS ((=) sa) UNIV {} {exit_lbl} (\s. ((),sb))` by
    (irule (INST_TYPE [alpha |-> ``:unit``] fuel_okS_at) >>
     qexistsl_tac [`\st. cenv_ptrs_below st.cs_next_var
                     (reg_env with ce_ctor_exit_label := SOME exit_lbl)`,
                   `UNIV`,
                   `compile_stmts (reg_env with ce_ctor_exit_label := SOME exit_lbl)
                      NoLoop NoneT body`, `()`] >>
     simp[] >> conj_tac
     >- (fs[cenv_ptrs_below_def] >> metis_tac[var_below_le]) >>
     irule (cj 2 fuel_okS_compile_stmt) >>
     simp[cenv_ptrs_in_def, stmt_exits_in_def]) >>
  qspecl_then [`pay`, `len`, `size`, `imm`, `exit_lbl`, `old_bb`,
    `initial_compile_state "__deploy"`, `st_pay`, `st1`, `st2`, `st3`, `sa`, `sb`,
    `sj`, `st_exit`, `st_epilogue`, `final`] mp_tac deploy_ctor_entry_fuel >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def]
QED

Triviality deploy_runner_uniform_fuel:
  run_deploy_lowering has rp bytes len args data_size ifns ce body pay nr key
    trans "__deploy" = SOME unit /\
  (~has ==> ifns = []) /\
  (has ==> !n. cenv_ptrs_below n ce) /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ifns) /\
  EVERY (\(lbl,env,params,has_buf,nr,key,trans,view,ctor,imm_len,body,ret).
           ?Wv. fuel_okS (\st. T) Wv {} {}
             (compile_internal_function env params has_buf nr key trans view ctor imm_len body ret))
    ifns ==>
  ?fuel. !n s. terminates (run_context n unit.cu_context s) ==>
               terminates (run_context fuel unit.cu_context s)
Proof
  strip_tac >>
  drule run_deploy_lowering_context_ok >> strip_tac >>
  `!fn. MEM fn unit.cu_context.ctx_functions ==>
       ?Kf. !G. callees_stable G unit.cu_context fn ==>
                fuel_stable (G + Kf) unit.cu_context fn` suffices_by
    (strip_tac >> drule_all run_context_uniform_fuel >> metis_tac[]) >>
  qpat_x_assum `run_deploy_lowering _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[run_deploy_lowering_def] >>
  pairarg_tac >> simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  qabbrev_tac `prefix = compile_generate_deploy has (LENGTH bytes) len args
      data_size [] ce body pay nr key trans` >>
  Cases_on `prefix (initial_compile_state "__deploy")` >>
  rename1 `prefix _ = (result,mid)` >> Cases_on `result` >>
  `compile_internal_fn_bodies ifns mid = ((),st1)` by
    (Cases_on `has`
     >- (qpat_x_assum `compile_generate_deploy T _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
         ONCE_REWRITE_TAC [compile_deploy_internal_suffix] >>
         simp[GSYM markerTheory.Abbrev_def, Abbr `prefix`]) >>
     gvs[Abbr `prefix`, compile_generate_deploy_def,
         compile_internal_fn_bodies_def, comp_return_def]) >>
  `fuel_okS ((=) (initial_compile_state "__deploy")) UNIV {} {} (\s. ((),mid))` by
    (Cases_on `has`
     >- (fs[Abbr `prefix`] >> drule_all_then ACCEPT_TAC deploy_generator_prefix_fuel) >>
     fs[Abbr `prefix`, compile_generate_deploy_def, comp_ignore_bind_def,
        comp_bind_def, comp_return_def, ELIM_UNCURRY] >>
     irule (INST_TYPE [alpha |-> ``:unit``] fuel_okS_at) >>
     qexistsl_tac [`K T`, `UNIV`, `compile_simple_deploy (LENGTH bytes) len`, `()`] >>
     simp[fuel_okS_of_ok, fuel_ok_compile_simple_deploy] >>
     Cases_on `compile_simple_deploy (LENGTH bytes) len (initial_compile_state "__deploy")` >>
     rename1 `compile_simple_deploy _ _ _ = (simple_result,simple_state)` >>
     Cases_on `simple_result` >> gvs[]) >>
  `ALL_DISTINCT (MAP FST (internal_fn_descriptors ifns))` by
    (drule extract_context_internal_names >> strip_tac >>
     fs[lowering_context_ok_def, ctx_fn_names_def,
        install_immutable_reservation_def]) >>
  `EVERY (\fn. ALL_DISTINCT (fn_labels fn)) ctx.ctx_functions` by
    (qpat_assum `lowering_context_ok (install_immutable_reservation _ _)`
      (mp_tac o SIMP_RULE (srw_ss ()) [lowering_context_ok_def,
        install_immutable_reservation_def]) >>
     simp[EVERY_MEM]) >>
  `EVERY (\d. internal_label_ok (FST d) /\
               ~MEM (FST d) (MAP (\bb. bb.bb_label) (all_blocks mid)))
     (internal_fn_descriptors ifns)` by
    (Cases_on `has` >> fs[internal_fn_descriptors_def] >>
     `EVERY (\bb. ~internal_label_ok bb.bb_label) (all_blocks mid)` by
       (fs[Abbr `prefix`] >> drule_then ACCEPT_TAC deploy_entry_blocks_not_internal) >>
     simp[EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  match_mp_tac (Q.SPECL [`len`, `ctx`] install_reservation_fns_fuel_stable) >>
  qspecl_then [`\s. ((),mid)`, `(=) (initial_compile_state "__deploy")`, `K T`,
    `"__deploy"`, `ifns`, `()`, `mid`, `()`, `st1`, `ctx`, `data`, `UNIV`]
    mp_tac extract_context_fuel_stable_from_labels >>
  simp[next_stable_def, combinTheory.K_DEF]
QED

Theorem lower_vyper_deploy_unit_uniform_fuel_mods:
  lower_vyper_deploy_unit_mods mods exps rpolicy bytes = SOME unit ==>
  ?fuel. !n s. terminates (run_context n unit.cu_context s) ==>
               terminates (run_context fuel unit.cu_context s)
Proof
  strip_tac >>
  qpat_x_assum `lower_vyper_deploy_unit_mods _ _ _ _ = _` mp_tac >>
  simp[lower_vyper_deploy_unit_mods_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  irule deploy_runner_uniform_fuel >>
  first_assum (irule_at Any) >>
  Cases_on `ctor_fn`
  >- simp[internal_fn_descriptors_def] >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac `run_deploy_lowering _ _ _ _ _ _ ips _ _ _ _ _ _ _ = _` >>
  simp[] >> rpt conj_tac
  >- (rename1 `set_constructor_package_target _ (package_constructor_unit _ _ _ cf) =
          (ce,_,_,_,_,_,_,_)` >>
      PairCases_on `cf` >>
      mp_tac (Q.INST [`src` |-> `NONE`, `vis` |-> `Deploy`, `mut` |-> `cf0`,
                      `fname` |-> `cf3`, `args` |-> `cf4`, `ret` |-> `cf6`,
                      `ss` |-> `cf7`, `trans` |-> `T`]
        (INST_TYPE [alpha |-> ``:string``] build_compile_env_unit_fuel_ok)) >>
      gvs[package_constructor_unit_def, set_constructor_package_target_def,
          update_cenv_nonreentrant_def, cenv_ptrs_below_def] >>
      strip_tac >> first_assum ACCEPT_TAC)
  >- (qpat_assum `Abbrev (ips = _)`
        (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
      drule (Q.INST [`static` |-> `F`] package_internal_fn_unit_shape) >>
      impl_tac >- simp[EVERY_MEM, FORALL_PROD, expr_shape_root_mode_dynamic,
                       dynamic_raw_expr_shape, dynamic_raw_stmt_shape] >>
      strip_tac >> first_assum ACCEPT_TAC) >>
  simp[Abbr `ips`, package_internal_fns_unit_fuel]
QED
