(* Constructor code containment for deploy_unit_execution_correct. *)
Theory ctorDeployLoweringCode
Ancestors
  ctorDeployLoweringDefs ctorDeployDefs ctorDeployShape immSectionDead e2eDeployDefs vyperTypeContract
  compileVyper vyperCompiler
  immSectionDead
  moduleLowering compileEnv context emitHelper loweringShapeProps
  loweringShapeDefs supportedProgram loweringShapeSource
  ctorDeployLoweringCodeShape loweringShapeRules list ctorUnitShape
  allocaFrontierBound venomInst venomWf venomExecProps fragExec rich_list
  ctorDeployEntryLabels internalBlockPackagingProps bodyFullShadowInternalCode

Theorem deploy_internal_package_shape:
  !tops use_trans nkey_map target is_ctor immutables_len src.
    runtime_bodies_shape_ok tops /\
    MEM src (FST (SND (classify_functions tops))) ==>
    internal_fn_shape_ok
      (set_internal_package_target target
        (package_internal_fn tops use_trans nkey_map is_ctor immutables_len src))
Proof
  rpt gen_tac >> PairCases_on `src` >> strip_tac >>
  `~supported_stmts_expr_exists expr_shape_root src7` by
    (gs[runtime_bodies_shape_ok_def] >> metis_tac[]) >>
  imp_res_tac runtime_bodies_shape_ok_func_defaults >>
  drule_then (qspecl_then [`Internal`, `src0`, `src3`, `src4`, `src6`, `src7`, `use_trans`]
    (strip_assume_tac o SRULE [cenv_static_ok_def])) build_compile_env_static >>
  simp[package_internal_fn_def, set_internal_package_target_def,
    update_cenv_nonreentrant_def, internal_fn_shape_ok_def, cenv_static_ok_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem deploy_build_env_no_return_pc:
  !tops mut fname args ret body ut.
    (build_compile_env tops Deploy mut fname args ret body ut).ce_return_pc = NONE
Proof
  rpt gen_tac >> simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[])
QED

(* Vyper rejects view and pure constructors, so the lock flag the
   constructor's package carries is F. *)
Theorem deploy_constructor_package_not_view:
  !tops exts ints fb cf target cenv args pay nr key ut body ret am tx.
    deploy_source_ok tops am tx /\
    classify_functions tops = (exts,ints,fb,SOME cf) /\
    set_constructor_package_target target
      (package_constructor tops T (K global_nonreentrant_slot) cf) =
      (cenv,args,pay,nr,key,ut,body,ret) ==>
    cenv.ce_nonreentrant = (nr,key,ut,F)
Proof
  rpt gen_tac >> strip_tac >> PairCases_on `cf` >>
  `SND (SND (SND (classify_functions tops))) =
    SOME (cf0,cf1,cf2,cf3,cf4,cf5,cf6,cf7)` by simp[] >>
  drule classify_functions_ctor_mem >> strip_tac >>
  `?art. check_contract T am.layouts tx.target [(NONE,tops)] = SOME art` by
    fs[deploy_source_ok_def, deploy_typing_ok_constants_ready] >>
  `check_toplevel_decl [(NONE,tops)] art NONE
     (FunctionDecl Deploy cf0 cf1 cf2 cf3 cf4 raw_defaults cf6 raw_body)` by
    (qpat_x_assum `check_contract _ _ _ _ = _` mp_tac >>
     simp[check_contract_def, check_module_def, EVERY_MEM] >>
     metis_tac[]) >>
  gvs[check_toplevel_decl_def, function_mutability_ok_def,
    package_constructor_def, set_constructor_package_target_def,
    update_cenv_nonreentrant_def]
QED

(* The reachable internal functions the deploy lowering selects are distinct
   classified internal functions. *)
Theorem deploy_order_internals_ok:
  !tops exts ints fb ctor.
    supported_program tops /\
    classify_functions tops = (exts,ints,fb,ctor) ==>
    ALL_DISTINCT (order_internals (deploy_internal_order ctor ints) ints) /\
    !x. MEM x (order_internals (deploy_internal_order ctor ints) ints) ==>
        MEM x (FST (SND (classify_functions tops)))
Proof
  rpt gen_tac >> strip_tac >>
  drule supported_program_internal_names >> strip_tac >>
  drule classified_internal_names_distinct >> gvs[] >> strip_tac >>
  simp[] >>
  drule_then (qspec_then `ctor` assume_tac) ALL_DISTINCT_order_deploy_internals >>
  imp_res_tac ALL_DISTINCT_MAP >> first_assum ACCEPT_TAC
QED

Theorem deploy_internal_package_labels:
  !tops target ut key is_ctor cap srcs ifns.
    supported_program tops /\
    ALL_DISTINCT srcs /\
    (!x. MEM x srcs ==> MEM x (FST (SND (classify_functions tops)))) /\
    ifns = MAP (set_internal_package_target target o
      package_internal_fn tops ut key is_ctor cap) srcs ==>
    EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ifns) /\
    ALL_DISTINCT (MAP FST (internal_fn_descriptors ifns))
Proof
  rpt gen_tac >> strip_tac >>
  drule supported_program_internal_names >> strip_tac >>
  drule classified_internal_names_distinct >> strip_tac >>
  drule_all internal_descriptors_sublist_ok >>
  disch_then (qspec_then `is_ctor` strip_assume_tac) >>
  gvs[GSYM MAP_MAP_o, internal_fn_descriptors_set_internal_package_target,
    internal_fn_descriptors_MAP_package_internal_fn]
QED

Theorem deploy_ctor_packaged_entry_by_labels:
  !ifns st_final post ctx data.
    compile_internal_fn_bodies ifns st_final = ((),post) /\
    EVERY (\bb. ~internal_label_ok bb.bb_label) (all_blocks st_final) /\
    EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ifns) /\
    ALL_DISTINCT (MAP FST (internal_fn_descriptors ifns)) /\
    extract_context_with_internals "__deploy" ifns post = SOME (ctx,data) ==>
    MEM (mk_raw_function "__deploy" (all_blocks st_final)) ctx.ctx_functions
Proof
  rpt gen_tac >> strip_tac >>
  drule bodyFullShadowInternalCodeTheory.compile_internal_labels >>
  strip_tac >>
  `EVERY (\d. ~isPREFIX "@" (FST d) /\
              ~MEM (FST d) (MAP (\bb. bb.bb_label) (all_blocks st_final)))
      (internal_fn_descriptors ifns)` by
    (rewrite_tac[EVERY_MEM] >> qx_gen_tac `d` >> BETA_TAC >> strip_tac >>
     `internal_label_ok (FST d)` by fs[EVERY_MEM] >>
     conj_tac
     >- (qpat_x_assum `internal_label_ok (FST d)` mp_tac >>
         rewrite_tac[internal_label_ok_def, IS_PREFIX_APPEND] >>
         strip_tac >> simp[]) >>
     simp[MEM_MAP] >> qx_gen_tac `entry_bb` >> rpt strip_tac >>
     qpat_assum `EVERY (\bb. ~internal_label_ok bb.bb_label) _`
       (mp_tac o SIMP_RULE bool_ss [EVERY_MEM]) >>
     disch_then (qspec_then `entry_bb` mp_tac) >> gvs[]) >>
  drule_all (Q.SPECL [`internal_fn_descriptors ifns`, `segments`, `all_blocks st_final`,
    `isPREFIX "@"`] package_internal_blocks_separated_segments) >> strip_tac >>
  gvs[extract_context_with_internals_def, GSYM all_blocks_def, mk_venom_context_def]
QED

Theorem ctor_code_block_inst_ids[local]:
  !bbs. MAP (\i. i.inst_id) (fn_insts_blocks bbs) =
    FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)
Proof
  Induct >> simp[fn_insts_blocks_def, MAP_APPEND]
QED

Theorem deploy_ctor_member_certificates:
  !ctx cap st_final.
    MEM (mk_raw_function "__deploy" (all_blocks st_final)) ctx.ctx_functions /\
    lowering_context_ok (install_immutable_reservation cap ctx) ==>
    MEM (mk_raw_function "__deploy" (all_blocks st_final))
      (install_immutable_reservation cap ctx).ctx_functions /\
    (mk_raw_function "__deploy" (all_blocks st_final)).fn_name = "__deploy" /\
    fn_inst_ids_distinct (mk_raw_function "__deploy" (all_blocks st_final)) /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks st_final))
Proof
  rpt gen_tac >> simp[install_immutable_reservation_def] >> strip_tac >>
  `ctx_inst_ids_distinct ctx` by fs[lowering_context_ok_def, ctx_inst_ids_distinct_def] >>
  drule_all ctx_inst_ids_distinct_fn >>
  simp[fn_insts_def, fn_inst_ids_distinct_def, MAP_FLAT, MAP_MAP_o] >>
  strip_tac >>
  `ALL_DISTINCT (fn_labels (mk_raw_function "__deploy" (all_blocks st_final)))` by
    (fs[lowering_context_ok_def, EVERY_MEM] >> metis_tac[]) >>
  gvs[fn_labels_def, mk_raw_function_def, ctor_code_block_inst_ids]
QED

Theorem ctor_code_raw_function_contains:
  !first last name.
    cs_extends first last /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks last)) ==>
    fn_has_code first last (mk_raw_function name (all_blocks last))
Proof
  rpt gen_tac >> strip_tac >>
  simp[fn_has_code_def, mk_raw_function_def] >> conj_tac
  >- (rpt strip_tac >> irule MEM_lookup_block >> simp[] >>
      fs[emitted_blocks_def, all_blocks_def] >>
      metis_tac[MEM_TAKE, MEM_REVERSE]) >>
  qexists_tac `<|bb_label := last.cs_current_bb; bb_instructions := last.cs_current_insts|>` >>
  simp[] >> irule MEM_lookup_block >> simp[all_blocks_def]
QED

Theorem ctor_code_intervals_contained:
  !first sa sb sj st_exit st_final name.
    cs_extends first sa /\ cs_extends sa sb /\ cs_extends sb sj /\
    cs_extends sj st_exit /\ cs_extends st_exit st_final /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks st_final)) ==>
    fn_has_code first sa (mk_raw_function name (all_blocks st_final)) /\
    fn_has_code sa sb (mk_raw_function name (all_blocks st_final)) /\
    fn_has_code sb sj (mk_raw_function name (all_blocks st_final)) /\
    fn_has_code st_exit st_final (mk_raw_function name (all_blocks st_final))
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends first st_final` by metis_tac[cs_extends_trans] >>
  drule_all ctor_code_raw_function_contains >>
  disch_then (qspec_then `name` assume_tac) >>
  metis_tac[fn_has_code_split, cs_extends_trans]
QED

Theorem ctor_lock_flag_select:
  !p f. (\(a:bool,b:num,c:bool,d:bool). f d) p = f (SND (SND (SND p)))
Proof
  PairCases >> simp[]
QED

Theorem deploy_ctor_lowering_trace:
  lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
  classify_functions tops = (exts, ints, fb, SOME cf) ==>
  ?cenv0 pos_args pay nr nkey ut body ret st_pay imm st1 cenv1 st2 st3
   exit_lbl sa sb sj old_bb st_exit st_epilogue st_final post ctx data.
    set_constructor_package_target rpolicy.rpol_target
      (package_constructor tops T (K global_nonreentrant_slot) cf) =
      (cenv0,pos_args,pay,nr,nkey,ut,body,ret) /\
    (if pay then comp_return () else
       comp_bind (emit_op CALLVALUE []) (\cv.
         comp_bind (emit_op ISZERO [cv]) (\v. emit_void ASSERT [v])))
      (initial_compile_state "__deploy") = ((),st_pay) /\
    (if imm_len tops > 0 then
       comp_bind (compile_fixed_region_with_id (imm_len tops))
         (\r. comp_return (SND r).buf_operand)
     else comp_return (Lit 0w)) st_pay = (imm,st1) /\
    compile_register_constructor_args
      (cenv0 with ce_imm_alloca :=
        (if imm_len tops > 0 then SOME imm else NONE)) pos_args 0 0 st1 =
      (cenv1,st2) /\
    (if nr then
       compile_nonreentrant_lock nkey ut (SND (SND (SND cenv0.ce_nonreentrant)))
     else comp_return ()) st2 = ((),st3) /\
    fresh_label "ctor_exit" st3 = (exit_lbl,sa) /\
    compile_stmts (cenv1 with ce_ctor_exit_label := SOME exit_lbl)
      NoLoop NoneT body sa = ((),sb) /\
    (if block_is_terminated sb then comp_return ()
     else emit_inst JMP [Label exit_lbl] []) sb = ((),sj) /\
    new_block exit_lbl sj = (old_bb,st_exit) /\
    (if nr then
       compile_nonreentrant_unlock nkey ut (SND (SND (SND cenv0.ce_nonreentrant)))
     else comp_return ()) st_exit = ((),st_epilogue) /\
    compile_constructor_epilogue (LENGTH runtime_bc) (imm_len tops) imm
      st_epilogue = ((),st_final) /\
    compile_internal_fn_bodies
      (MAP (set_internal_package_target rpolicy.rpol_target o
        package_internal_fn tops T (K global_nonreentrant_slot) T (imm_len tops))
        (order_internals (deploy_internal_order (SOME cf) ints) ints))
      st_final = ((),post) /\
    extract_context_with_internals "__deploy"
      (MAP (set_internal_package_target rpolicy.rpol_target o
        package_internal_fn tops T (K global_nonreentrant_slot) T (imm_len tops))
        (order_internals (deploy_internal_order (SOME cf) ints) ints))
      post = SOME (ctx,data) /\
    lowering_context_ok (install_immutable_reservation (imm_len tops) ctx) /\
    dunit = <|cu_context := install_immutable_reservation (imm_len tops) ctx;
      cu_data_segment := data ++
        [<|ds_label := "runtime_begin"; ds_items := [DataBytes runtime_bc]|>]|>
Proof
  strip_tac >>
  qpat_x_assum `lower_vyper_deploy_unit _ _ _ = _` mp_tac >>
  simp[lower_vyper_deploy_unit_def, GSYM imm_len_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  qpat_x_assum `run_deploy_lowering _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[run_deploy_lowering_def] >>
  pairarg_tac >> simp[AllCaseEqs()] >> strip_tac >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac `compile_generate_deploy T _ _ _ _ ifns` >>
  qpat_x_assum `classify_functions _ = _` kall_tac >>
  qpat_x_assum `set_constructor_package_target _ _ = _` kall_tac >>
  qpat_x_assum `EVERY _ _` kall_tac >>
  qpat_x_assum `fn_allocs_ok _ _` kall_tac >>
  qpat_x_assum `compile_generate_deploy _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  rewrite_tac [compile_generate_deploy_def, comp_ignore_bind_def,
    comp_bind_def, comp_get_def, LET_THM, ctor_lock_flag_select] >>
  rpt (pairarg_tac >> gvs[comp_bind_def, comp_get_def, LET_THM]) >>
  strip_tac >>
  Cases_on `ctor_payable` >> gvs[] >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem ctor_code_cond_not:
  !p a b. (if ~p then a else b) = (if p then b else a)
Proof
  Cases >> simp[]
QED

(* With a constructor, the deploy unit is compile_generate_deploy's, laid
   out as deploy_ctor_code names it. *)
Theorem deploy_ctor_code_exists:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx
   exts ints fb cf.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    classify_functions tops = (exts, ints, fb, SOME cf) ==>
    ?body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final func.
      deploy_ctor_code tops rpolicy runtime_bc dunit
        (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func)
Proof
  rpt gen_tac >> strip_tac >>
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit` by
    fs[deploy_phases_def] >>
  drule_all deploy_ctor_lowering_trace >> strip_tac >>
  drule_all deploy_constructor_package_not_view >> strip_tac >>
  qpat_assum `cenv0.ce_nonreentrant = _` (fn th =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [th, pairTheory.SND]) >> assume_tac th) >>
  drule_all ctor_code_setup_extension >> strip_tac >>
  drule_all ctor_code_tail_extensions >> strip_tac >>
  rename1 `set_constructor_package_target _ _ = (cenv0,pos_args,pay,nr,nkey,ut,ss,_)` >>
  `compile_generate_deploy T (LENGTH runtime_bc) (imm_len tops) pos_args 0 []
    cenv0 ss pay nr nkey ut (initial_compile_state "__deploy") = ((),st_final)` by
    (PURE_REWRITE_TAC [compile_generate_deploy_def, COND_CLAUSES,
       ctor_code_cond_not, ctor_lock_flag_select] >>
     simp_tac bool_ss [comp_ignore_bind_def, comp_bind_def, comp_get_def, LET_THM] >>
     rpt (pairarg_tac >> gvs[]) >>
     gvs[compile_internal_fn_bodies_def, comp_return_def]) >>
  drule deploy_entry_blocks_not_internal >> strip_tac >>
  `supported_program tops` by fs[deploy_source_ok_def] >>
  qmatch_asmsub_abbrev_tac `compile_internal_fn_bodies ifns st_final` >>
  `ifns = MAP (set_internal_package_target rpolicy.rpol_target o
      package_internal_fn tops T (K global_nonreentrant_slot) T (imm_len tops))
      (order_internals (deploy_internal_order (SOME cf) ints) ints)` by
    simp[Abbr `ifns`] >>
  drule_all deploy_order_internals_ok >> strip_tac >>
  drule_all deploy_internal_package_labels >> strip_tac >>
  drule_all deploy_ctor_packaged_entry_by_labels >> strip_tac >>
  drule_all deploy_ctor_member_certificates >> strip_tac >>
  `fn_has_code (initial_compile_state "__deploy") sa
      (mk_raw_function "__deploy" (all_blocks st_final)) /\
   fn_has_code sa sb (mk_raw_function "__deploy" (all_blocks st_final)) /\
   fn_has_code sb sj (mk_raw_function "__deploy" (all_blocks st_final)) /\
   fn_has_code st_exit st_final (mk_raw_function "__deploy" (all_blocks st_final))` by
    (irule ctor_code_intervals_contained >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`ss`, `cenv1 with ce_ctor_exit_label := SOME exit_lbl`,
    `nr`, `nkey`, `ut`, `imm`, `exit_lbl`, `sa`, `sb`, `sj`, `st_exit`,
    `st_epilogue`, `st_final`, `mk_raw_function "__deploy" (all_blocks st_final)`] >>
  simp[deploy_ctor_code_def] >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED
