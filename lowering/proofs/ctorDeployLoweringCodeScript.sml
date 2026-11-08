(* Constructor code containment for deploy_unit_execution_correct. *)
Theory ctorDeployLoweringCode
Ancestors
  ctorDeployLoweringDefs ctorDeployDefs immSectionDead compileVyper vyperCompiler
  moduleLowering compileEnv context emitHelper loweringShapeProps
  loweringShapeDefs supportedProgram loweringShapeSource
  ctorDeployLoweringCodeShape loweringShapeRules list ctorUnitShape
  allocaFrontierBound venomInst venomWf venomExecProps fragExec rich_list

Theorem deploy_internal_package_shape:
  !tops use_trans nkey_map target is_ctor immutables_len src.
    runtime_bodies_shape_ok tops /\
    MEM src (FST (SND (classify_functions tops))) ==>
    internal_fn_shape_ok
      (set_internal_package_target target
        (package_internal_fn tops use_trans nkey_map is_ctor immutables_len src))
Proof
  rpt gen_tac >> PairCases_on `src` >> strip_tac >>
  drule (iffLR MEM_classify_internal) >> strip_tac >>
  `~supported_stmts_expr_exists expr_shape_root src7` by
    (gs[runtime_bodies_shape_ok_def] >> first_x_assum drule >> simp[]) >>
  simp[package_internal_fn_def, set_internal_package_target_def,
    update_cenv_nonreentrant_def, internal_fn_shape_ok_def, cenv_static_ok_def] >>
  metis_tac[build_compile_env_static, cenv_static_ok_def]
QED

Theorem deploy_build_env_no_return_pc:
  !tops mut fname args ret body ut.
    (build_compile_env tops Deploy mut fname args ret body ut).ce_return_pc = NONE
Proof
  rpt gen_tac >> simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[])
QED

Theorem deploy_classify_constructor_mem:
  !tops mut nr rr fname args defaults ret body.
    SND (SND (SND (classify_functions tops))) =
      SOME (mut,nr,rr,fname,args,defaults,ret,body) ==>
    MEM (FunctionDecl Deploy mut nr rr fname args defaults ret body) tops
Proof
  Induct_on `tops` >- simp[classify_functions_def] >>
  rpt gen_tac >>
  `classify_functions (h::tops) = classify_function h (classify_functions tops)` by
    simp[classify_functions_def] >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  Cases_on `h` >> simp[classify_function_def] >>
  Cases_on `f` >> gvs[] >>
  Cases_on `s = "__default__"` >> gvs[]
QED

Theorem deploy_constructor_package_shape:
  !tops exts ints fb cf target cenv args pay nr key ut body ret am tx.
    deploy_source_ok tops am tx /\
    classify_functions tops = (exts,ints,fb,SOME cf) /\
    set_constructor_package_target target
      (package_constructor tops F (assign_nkeys tops 0) cf) =
      (cenv,args,pay,nr,key,ut,body,ret) ==>
    cenv_static_ok cenv /\ cenv.ce_return_pc = NONE /\
    ~supported_stmts_expr_exists expr_shape_root body
Proof
  rpt gen_tac >> strip_tac >> PairCases_on `cf` >>
  `MEM (FunctionDecl Deploy cf0 cf1 cf2 cf3 cf4 cf5 cf6 cf7) tops` by
    (irule deploy_classify_constructor_mem >> simp[]) >>
  `supported_program tops` by fs[deploy_source_ok_def] >>
  drule_all supported_program_function >> strip_tac >>
  drule supported_function_body_shape >> strip_tac >>
  gvs[package_constructor_def, set_constructor_package_target_def,
    update_cenv_nonreentrant_def] >>
  simp[deploy_build_env_no_return_pc, cenv_static_ok_def] >>
  metis_tac[build_compile_env_static, cenv_static_ok_def]
QED

Theorem deploy_internal_package_certificates:
  !tops target ut key is_ctor cap ifns.
    supported_program tops /\
    ifns = MAP (set_internal_package_target target o
      package_internal_fn tops ut key is_ctor cap)
      (FST (SND (classify_functions tops))) ==>
    EVERY internal_fn_shape_ok ifns /\
    EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ifns) /\
    ALL_DISTINCT (MAP FST (internal_fn_descriptors ifns))
Proof
  rpt gen_tac >> strip_tac >>
  `runtime_bodies_shape_ok tops` by
    metis_tac[supported_program_runtime_bodies_shape_ok] >>
  `ALL_DISTINCT (supported_function_names tops)` by
    fs[supported_program_def, supportedNamesTheory.supported_declaration_names_def] >>
  drule supported_names_internal_names_distinct >> strip_tac >>
  drule internal_descriptors_ok >>
  disch_then (qspec_then `is_ctor` strip_assume_tac) >>
  gvs[GSYM MAP_MAP_o, internal_fn_descriptors_set_internal_package_target,
    internal_fn_descriptors_MAP_package_internal_fn] >>
  simp[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
  irule deploy_internal_package_shape >> simp[]
QED

Theorem deploy_internal_body_certificates:
  !tops target ut key is_ctor cap ifns st_final post.
    supported_program tops /\
    ifns = MAP (set_internal_package_target target o
      package_internal_fn tops ut key is_ctor cap)
      (FST (SND (classify_functions tops))) /\
    shape_state st_final /\
    compile_internal_fn_bodies ifns st_final = ((),post) ==>
    ALL_DISTINCT (MAP FST (internal_fn_descriptors ifns)) /\
    ?segs. all_blocks post = all_blocks st_final ++ FLAT segs /\
      LIST_REL internal_segment_ok (internal_fn_descriptors ifns) segs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_internal_package_certificates >> strip_tac >>
  drule_all compile_internal_fn_bodies_shape >> simp[]
QED

Theorem deploy_ctor_packaged_entry:
  !ifns st_final post ctx data.
    compile_internal_fn_bodies ifns st_final = ((),post) /\
    shape_state st_final /\ EVERY internal_fn_shape_ok ifns /\
    EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ifns) /\
    ALL_DISTINCT (MAP FST (internal_fn_descriptors ifns)) /\
    all_blocks st_final <> [] /\
    (HD (all_blocks st_final)).bb_label = "__deploy" /\
    EVERY jump_label_ok (TL (MAP (\bb. bb.bb_label) (all_blocks st_final))) /\
    extract_context_with_internals "__deploy" ifns post = SOME (ctx,data) ==>
    MEM (mk_raw_function "__deploy" (all_blocks st_final)) ctx.ctx_functions
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\d. ~compiler_label (FST d) /\
    ~MEM (FST d) (MAP (\bb. bb.bb_label) (all_blocks st_final)))
    (internal_fn_descriptors ifns)` by
    (fs[EVERY_MEM] >> gen_tac >> strip_tac >>
     irule deploy_internal_label_separate >> simp[EVERY_MEM]) >>
  drule_all compile_internal_fn_bodies_shape >> strip_tac >>
  drule_all package_internal_blocks_segments >> strip_tac >>
  gvs[extract_context_with_internals_def, GSYM all_blocks_def,
    mk_venom_context_def]
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

Theorem deploy_ctor_lowering_trace:
  lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
  classify_functions tops = (exts, ints, fb, SOME cf) ==>
  ?cenv0 pos_args pay nr nkey ut body ret st_pay imm st1 cenv1 st2 st3
   exit_lbl sa sb sj old_bb st_exit st_epilogue st_final post ctx data.
    set_constructor_package_target rpolicy.rpol_target
      (package_constructor tops F (assign_nkeys tops 0) cf) =
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
    (if nr then compile_nonreentrant_lock nkey ut F else comp_return ()) st2 =
      ((),st3) /\
    fresh_label "ctor_exit" st3 = (exit_lbl,sa) /\
    compile_stmts (cenv1 with ce_ctor_exit_label := SOME exit_lbl)
      NoLoop NoneT body sa = ((),sb) /\
    (if block_is_terminated sb then comp_return ()
     else emit_inst JMP [Label exit_lbl] []) sb = ((),sj) /\
    new_block exit_lbl sj = (old_bb,st_exit) /\
    (if nr then compile_nonreentrant_unlock nkey ut F else comp_return ())
      st_exit = ((),st_epilogue) /\
    compile_constructor_epilogue (LENGTH runtime_bc) (imm_len tops) imm
      st_epilogue = ((),st_final) /\
    compile_internal_fn_bodies
      (MAP (set_internal_package_target rpolicy.rpol_target o
        package_internal_fn tops F (assign_nkeys tops 0) T (imm_len tops)) ints)
      st_final = ((),post) /\
    extract_context_with_internals "__deploy"
      (MAP (set_internal_package_target rpolicy.rpol_target o
        package_internal_fn tops F (assign_nkeys tops 0) T (imm_len tops)) ints)
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
    comp_bind_def, comp_get_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[comp_bind_def, comp_get_def, LET_THM]) >>
  strip_tac >>
  Cases_on `ctor_payable` >> gvs[] >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem ctor_code_cond_not[local]:
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
  drule_all deploy_constructor_package_shape >> strip_tac >>
  drule_all ctor_code_setup_extension >> strip_tac >>
  drule_all ctor_code_tail_extensions >> strip_tac >>
  rename1 `~supported_stmts_expr_exists expr_shape_root ss` >>
  `(do (if ~pay then
           do cv <- emit_op CALLVALUE []; v <- emit_op ISZERO [cv];
              emit_void ASSERT [v] od else return ());
        imm <- (if imm_len tops > 0 then
                  do p <- compile_fixed_region_with_id (imm_len tops);
                     return (SND p).buf_operand od else return (Lit 0w));
        ce <- compile_register_constructor_args
          (cenv0 with ce_imm_alloca :=
            (if imm_len tops > 0 then SOME imm else NONE)) pos_args 0 0;
        (if nr then compile_nonreentrant_lock nkey ut F else return ());
        lbl <- fresh_label "ctor_exit";
        compile_stmts (ce with ce_ctor_exit_label := SOME lbl) NoLoop NoneT ss;
        cs <- comp_get;
        (if block_is_terminated cs then return () else emit_inst JMP [Label lbl] []);
        new_block lbl;
        (if nr then compile_nonreentrant_unlock nkey ut F else return ());
        compile_constructor_epilogue (LENGTH runtime_bc) (imm_len tops) imm od)
      (initial_compile_state "__deploy") = ((),st_final)` by
    (rewrite_tac[ctor_code_cond_not] >>
     simp[comp_ignore_bind_def, comp_bind_def, comp_get_def]) >>
  drule_all ctor_code_prefix_certificates >> strip_tac >>
  qpat_x_assum `comp_ignore_bind _ _ (initial_compile_state "__deploy") = _` kall_tac >>
  `supported_program tops` by fs[deploy_source_ok_def] >>
  qmatch_asmsub_abbrev_tac `compile_internal_fn_bodies ifns st_final` >>
  `ifns = MAP (set_internal_package_target rpolicy.rpol_target o
      package_internal_fn tops F (assign_nkeys tops 0) T (imm_len tops))
      (FST (SND (classify_functions tops)))` by simp[Abbr `ifns`] >>
  drule_all deploy_internal_package_certificates >> strip_tac >>
  drule_all deploy_ctor_packaged_entry >> strip_tac >>
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
