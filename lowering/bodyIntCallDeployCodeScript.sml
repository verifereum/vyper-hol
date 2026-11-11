(* Deployment counterpart of the runtime selected internal code boundary. *)
Theory bodyIntCallDeployCode
Ancestors
  bodyIntCallExtractCode ctorDeployLoweringCode ctorDeployLoweringCodeShape
  ctorDeployShape loweringShapeProps loweringShapeDefs loweringShapeRules moduleLowering
  compileEnv compileVyper fragExec vyperCompiler venomWf venomInst list

Theorem compile_deploy_internal_start:
  compile_generate_deploy T runtime_size cap args data_size ints ce ss
    pay nr key trans (initial_compile_state "__deploy") = ((),final) /\
  cenv_static_ok ce /\ ce.ce_return_pc = NONE /\
  ~supported_stmts_expr_exists expr_shape_root ss ==>
  ?start.
    shape_state start /\
    compile_internal_fn_bodies ints start = ((),final) /\
    all_blocks start <> [] /\ (HD (all_blocks start)).bb_label = "__deploy" /\
    EVERY jump_label_ok (TL (MAP (\bb. bb.bb_label) (all_blocks start)))
Proof
  strip_tac >> drule_all ctor_code_prefix_shape >>
  disch_then (qspecl_then [`pay`, `nr`, `key`, `trans`, `runtime_size`,
                          `cap`, `args`, `data_size`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `shape_step F compiler_label (\st. T) prefix _` >>
  `compile_generate_deploy T runtime_size cap args data_size ints ce ss
     pay nr key trans = comp_ignore_bind prefix (compile_internal_fn_bodies ints)`
    by simp[compile_generate_deploy_def, Abbr `prefix`,
            comp_ignore_bind_def, comp_bind_assoc] >>
  qpat_x_assum `compile_generate_deploy _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac [] >>
  Cases_on `prefix (initial_compile_state "__deploy")` >>
  rename1 `prefix _ = (u,start)` >> Cases_on `u` >>
  simp[comp_ignore_bind_def, comp_bind_def] >> strip_tac >>
  qpat_x_assum `shape_step _ _ _ _ _` mp_tac >> simp[shape_step_def] >>
  disch_then drule >> simp[shape_state_initial_compile_state] >> strip_tac >>
  `shape_extends F jump_label_ok (initial_compile_state "__deploy") start` by
    (irule shape_extends_LP_mono >>
     qexists_tac `compiler_label` >> simp[jump_label_ok_def]) >>
  drule initial_entry_blocks_shape >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem run_deploy_lowering_selected_internal_code:
  run_deploy_lowering T policy runtime_bc cap args data_size
    (xs ++ [(label,ce,params,has_buf,nr,key,trans,view,ctor,ilen,ss,ret)] ++ ys)
    ctor_ce ctor_ss pay ctor_nr ctor_key ctor_trans "__deploy" = SOME unit /\
  cenv_static_ok ctor_ce /\ ctor_ce.ce_return_pc = NONE /\
  ~supported_stmts_expr_exists expr_shape_root ctor_ss /\
  EVERY internal_fn_shape_ok
    (xs ++ [(label,ce,params,has_buf,nr,key,trans,view,ctor,ilen,ss,ret)] ++ ys) /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors
    (xs ++ [(label,ce,params,has_buf,nr,key,trans,view,ctor,ilen,ss,ret)] ++ ys)) /\
  ALL_DISTINCT (MAP FST (internal_fn_descriptors
    (xs ++ [(label,ce,params,has_buf,nr,key,trans,view,ctor,ilen,ss,ret)] ++ ys))) ==>
  ?func before old st0 after.
    lookup_function label unit.cu_context.ctx_functions = SOME func /\
    new_block label before = (old,st0) /\
    compile_internal_function ce params has_buf nr key trans view ctor ilen
      ss ret st0 = ((),after) /\
    fn_has_code st0 after func /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks) /\
    ctx_inst_ids_distinct unit.cu_context
Proof
  strip_tac >>
  Cases_on `compile_generate_deploy T (LENGTH runtime_bc) cap args data_size
    (xs ++ [(label,ce,params,has_buf,nr,key,trans,view,ctor,ilen,ss,ret)] ++ ys)
    ctor_ce ctor_ss pay ctor_nr ctor_key ctor_trans
    (initial_compile_state "__deploy")` >>
  rename1 `_ = (u,final)` >> Cases_on `u` >>
  drule_all compile_deploy_internal_start >> strip_tac >>
  qpat_x_assum `run_deploy_lowering _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[run_deploy_lowering_def, AllCaseEqs()] >> strip_tac >>
  gvs[] >>
  `ALL_DISTINCT (MAP (\f. f.fn_name) ctx.ctx_functions) /\
   EVERY (\f. ALL_DISTINCT (MAP (\bb. bb.bb_label) f.fn_blocks)) ctx.ctx_functions /\
   ctx_inst_ids_distinct ctx` by
    (fs[lowering_context_ok_def, install_immutable_reservation_def,
        ctx_fn_names_def, fn_labels_def, ctx_inst_ids_distinct_def, EVERY_MEM] >>
     simp[]) >>
  drule extract_context_selected_internal_code >>
  disch_then (qspec_then `start` mp_tac) >> simp[] >> strip_tac >>
  simp[install_immutable_reservation_def, ctx_inst_ids_distinct_def] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> fs[ctx_inst_ids_distinct_def]
QED

Theorem lower_vyper_deploy_unit_selected_internal_code:
  supported_program tops /\ lower_vyper_deploy_unit tops policy runtime_bc = SOME unit /\
  IS_SOME (SND (SND (SND (classify_functions tops)))) /\
  MEM (FunctionDecl Internal mut isnr rr name args dflts ret ss) tops /\
  set_internal_package_target policy.rpol_target
    (package_internal_fn tops F (assign_nkeys tops 0) T
      (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) tops)
      (mut,isnr,rr,name,args,dflts,ret,ss)) =
    (label,ce,params,has_buf,nr,key,trans,view,ctor,ilen,compiled_ss,rty) ==>
  ?func before old st0 after.
    lookup_function label unit.cu_context.ctx_functions = SOME func /\
    new_block label before = (old,st0) /\
    compile_internal_function ce params has_buf nr key trans view ctor ilen
      compiled_ss rty st0 = ((),after) /\
    fn_has_code st0 after func /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks) /\
    ctx_inst_ids_distinct unit.cu_context
Proof
  strip_tac >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  rename1 `classify_functions tops = (exts,ints,fb,cf)` >>
  Cases_on `cf` >> gvs[] >> rename1 `_ = (exts,ints,fb,SOME cf)` >>
  `MEM (mut,isnr,rr,name,args,dflts,ret,ss) ints` by
    metis_tac[MEM_classify_internal, pairTheory.FST, pairTheory.SND] >>
  qpat_x_assum `lower_vyper_deploy_unit _ _ _ = _` mp_tac >>
  simp[lower_vyper_deploy_unit_def] >> pairarg_tac >> simp[] >> strip_tac >>
  `SND (SND (SND (classify_functions tops))) = SOME cf` by simp[] >>
  drule_all package_constructor_shape_ok >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_deploy_lowering T _ _ _ _ _ pkgs _ _ _ _ _ _ _` >>
  `EVERY internal_fn_shape_ok pkgs /\
   EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors pkgs) /\
   ALL_DISTINCT (MAP FST (internal_fn_descriptors pkgs))` by
    (irule deploy_internal_package_certificates >>
     qexistsl_tac [`compute_immutables_len
                     (get_struct_fields (make_struct_fields_map tops)) tops`,
                   `T`, `assign_nkeys tops 0`, `policy.rpol_target`, `tops`, `F`] >>
     simp[Abbr `pkgs`]) >>
  `MEM (label,ce,params,has_buf,nr,key,trans,view,ctor,ilen,compiled_ss,rty) pkgs` by
    (simp[Abbr `pkgs`, MEM_MAP] >>
     qexists_tac `(mut,isnr,rr,name,args,dflts,ret,ss)` >> simp[]) >>
  qpat_x_assum `MEM _ pkgs`
    (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >> gvs[] >>
  drule (PURE_REWRITE_RULE[GSYM APPEND_ASSOC, APPEND]
    run_deploy_lowering_selected_internal_code) >> simp[]
QED
