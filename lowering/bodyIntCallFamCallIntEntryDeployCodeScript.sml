(* Deployment selection keeps the installed immutable reservation. *)
Theory bodyIntCallFamCallIntEntryDeployCode
Ancestors
  bodyIntCallFamCallIntEntryRuntimeCode bodyIntCallFamCallIntEntryLookup
  bodySim ctorDeployLoweringCode ctorDeployLoweringCodeShape ctorDeployShape
  ctorUnitShape compileVyper vyperCompiler loweringShapeProps moduleLowering
  compileEnv context emitHelper supportedProgram
Libs
  monadsyntax

Theorem intcall_deploy_selected_code:
  !tops ctx caller cx mut rr name args ret ss.
    body_inv tops ctx caller cx /\ cx.in_deploy /\
    MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops ==>
    ?ut nk im lbl ce params rb nr key tr view ctor il body rt b c callee.
      set_internal_package_target caller.ce_target
        (package_internal_fn tops ut nk caller.ce_is_ctor im
          (mut,F,rr,name,args,([]:expr list),ret,ss)) =
        (lbl,ce,params,rb,nr,key,tr,view,ctor,il,body,rt) /\
      lookup_function lbl ctx.ctx_functions = SOME callee /\
      compile_internal_function ce params rb nr key tr view ctor il body rt b =
        ((),c) /\ fn_has_code b c callee
Proof
  rpt gen_tac >> simp[body_inv_def] >> strip_tac >> gvs[] >>
  Cases_on `classify_functions tops` >>
  rename1 `classify_functions tops = (ext_fns,rest)` >> PairCases_on `rest` >>
  rename1 `classify_functions tops = (ext_fns,int_fns,fb,cf)` >>
  gvs[] >> Cases_on `cf` >> gvs[] >>
  drule_all deploy_ctor_lowering_trace >> strip_tac >> gvs[] >>
  rename1 `compile_stmts _ NoLoop NoneT ctor_body _ = _` >>
  `cenv_static_ok cenv0 /\ cenv0.ce_return_pc = NONE /\
    ~supported_stmts_expr_exists expr_shape_root ctor_body` by
    (irule package_constructor_shape_ok >> goal_assum (drule_at Any) >> simp[]) >>
  qspecl_then [`cenv0`, `ctor_body`, `pay`, `nr`, `nkey`, `ut`,
    `LENGTH rbc`, `imm_len tops`, `pos_args`, `0`, `st_final`]
    mp_tac ctor_code_prefix_certificates >>
  (impl_tac >-
    (Cases_on `pay` >>
     gvs[comp_ignore_bind_def, comp_bind_def, comp_get_def, comp_return_def] >>
     qpat_x_assum `((),st_pay) = _`
       (fn th => rewrite_tac [SYM th]) >> simp[])) >>
  strip_tac >>
  qspecl_then [`tops`, `rpolicy.rpol_target`, `F`, `assign_nkeys tops 0`,
    `T`, `imm_len tops`] mp_tac intcall_package_shape_certificates >>
  simp[] >> strip_tac >>
  `EVERY (\d. ~compiler_label (FST d) /\
      ~MEM (FST d) (MAP (\bb. bb.bb_label) (all_blocks st_final)))
    (internal_fn_descriptors (MAP (set_internal_package_target rpolicy.rpol_target o
      package_internal_fn tops F (assign_nkeys tops 0) T (imm_len tops)) int_fns))` by
    (rewrite_tac[listTheory.EVERY_MEM] >> rpt gen_tac >> disch_tac >> BETA_TAC >>
     irule deploy_internal_label_separate >> simp[] >>
     gvs[listTheory.EVERY_MEM]) >>
  `MEM (mut,F,rr,name,args,[],ret,ss) int_fns` by
    (drule (iffRL MEM_classify_internal) >> simp[]) >>
  qpat_x_assum `MEM (_,F,_,_,_,[],_,_) int_fns`
    (mp_tac o REWRITE_RULE [listTheory.MEM_SPLIT]) >>
  strip_tac >> gvs[listTheory.MAP_APPEND] >>
  qmatch_asmsub_abbrev_tac `internal_fn_shape_ok pkg` >> PairCases_on `pkg` >>
  rename1 `internal_fn_shape_ok (labelx,cex,paramsx,rbx,nrx,keyx,trx,viewx,ctorx,ilx,bodyx,rtx)` >>
  rule_assum_tac (PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_at (Pat `extract_context_with_internals _ _ _ = _`)
    intcall_selected_packaged_compilation >>
  disch_then (qspecl_then [`st_final`, `imm_len tops`] mp_tac) >>
  fs[listTheory.EVERY_APPEND] >> strip_tac >>
  qexistsl [`F`, `assign_nkeys tops 0`, `imm_len tops`, `labelx`, `cex`, `paramsx`,
    `rbx`, `nrx`, `keyx`, `trx`, `viewx`, `ctorx`, `ilx`, `bodyx`, `rtx`] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED
