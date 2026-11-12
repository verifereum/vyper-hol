(* Introduction boundaries for the universal packaged-callee entry clauses. *)
Theory bodyIntCallFamCallIntEntryIntroduce
Ancestors
  compileVyper compileEnv list exprLoweringProps entryStateRel
  bodyIntCallFamCallIntSourceTyping bodyIntCallFamCallIntProvenance
  bodyIntCallFamCallIntFlags bodyIntCallFamCallIntPureStageInterface
  bodyIntCallFamCallIntEntryPackage bodyIntCallFamCallIntEntryHeadStage
  bodyIntCallFamCallIntEntryFrame bodyIntCallFamCallIntEntryModes
  bodyIntCallFamCallIntEntryRoom bodyIntCallSeamDefs

Theorem intcall_targeted_parameter_metadata:
  set_internal_package_target target
    (package_internal_fn tops tr keys ctor imm
      (mut,nr,rr,name,args,dflts,ret,code_stmts)) =
    (lbl,ce,params,rb,is_nr,nkey,use_tr,is_view,is_ctor,ilen,code_stmts',rt) /\
  ALL_DISTINCT (MAP FST args) ==>
  params = ZIP (MAP FST args,
    compute_pass_via_stack (MAP SND args)
      (returns_stack_count
        (\n. MAP (FST o SND)
          (get_struct_fields (make_struct_fields_map tops) n)) ret)) /\
  MAP FST params = MAP FST args /\
  EVERY (\a. ?off. FLOOKUP ce.ce_vars (FST a) =
    SOME (MemLoc off (type_memory_bytes ce (SND a)))) args
Proof
  simp[package_internal_fn_def, update_cenv_nonreentrant_def,
       set_internal_package_target_def] >> strip_tac >> gvs[] >>
  simp[MAP_ZIP, LENGTH_compute_pass_via_stack,
       GSYM type_mem_bytes_type_memory_bytes] >>
  irule (SRULE [GSYM type_mem_bytes_type_memory_bytes]
    intcall_build_env_parameter_slots) >> simp[]
QED

Theorem intcall_targeted_package_state:
  set_internal_package_target target
    (package_internal_fn tops tr keys caller.ce_is_ctor imm
      (mut,nr,rr,name,args,dflts,ret,code_stmts)) =
    (lbl,ce,params,rb,is_nr,nkey,use_tr,is_view,is_ctor,ilen,code_stmts',rt) /\
  cenv_module_pins tops caller /\ stmt_state_rel ctx func caller cx es s ==>
  state_rel func ce cx (es with scopes := []) s /\
  internal_immutable_regions ce cx es s.vs_alloca_next
Proof
  strip_tac >>
  `ce.ce_module_vars = caller.ce_module_vars /\
   ce.ce_module = caller.ce_module /\ ce.ce_is_ctor = caller.ce_is_ctor` by
    (qpat_x_assum `set_internal_package_target _ _ = _` mp_tac >>
     simp[package_internal_fn_def, update_cenv_nonreentrant_def,
          set_internal_package_target_def] >> strip_tac >>
     gvs[bodyIntCallJointContractTheory.cenv_module_pins_def,
         build_compile_env_def] >> rpt (pairarg_tac >> gvs[])) >>
  conj_tac
  >- (irule exprLoweringPropsTheory.state_rel_cenv_cong >>
      qexists_tac `caller` >>
      simp[vyperStateTheory.lookup_scopes_def] >>
      irule stmtSimReturnTheory.state_rel_scopes_nil >>
      fs[exprLoweringPropsTheory.stmt_state_rel_def]) >>
  drule intcall_state_immutable_regions >>
  simp[intCallCalleeTheory.internal_immutable_regions_def]
QED

(* Join source typing and syntactic tags before any target staging. *)
Theorem intcall_pure_staging_inputs:
  supported_pure_exprs tops ds /\
  (!e. MEM e ds ==> expr_body_pre ce cx env e es) /\
  expr_sim_inv ce cx env es /\ well_typed_exprs env ds /\
  call_evaluation_safe cx (int_calls_exprs ds) /\
  eval_expr_results cx ds (es with gas_obs := gs) = (INL rs,ee) /\
  read_results cx rs ee = (INL values,ee) /\
  compile_multi_vvs compile_expr ce ds a = (vs,b) /\
  (!i. i < LENGTH ds /\ EL i flags ==>
    is_word_type (expr_type (EL i ds))) ==>
  LENGTH values = LENGTH ds /\
  (!i. i < LENGTH ds ==>
    post_value_type ce (EL i ds) = expr_type (EL i ds) /\
    vv_type (EL i vs) = expr_type (EL i ds) /\
    read_result cx (EL i rs) ee = (INL (EL i values),ee) /\
    (EL i flags ==> is_word_type (expr_type (EL i ds))) /\
    ?tv. evaluate_type (get_tenv cx) (expr_type (EL i ds)) = SOME tv /\
      type_memory_bytes ce (expr_type (EL i ds)) = type_memory_size tv /\
      type_memory_size tv < 2**64 /\ value_has_type tv (EL i values) /\
      (~EL i flags ==> val_wf tv (EL i values)))
Proof
  strip_tac >> drule_all intcall_pure_source_stage_facts >> strip_tac >>
  drule_all intcall_pure_multi_vvs_tags >> disch_tac >>
  `LENGTH rs = LENGTH ds` by
    metis_tac[vyperStateTheory.read_results_length] >>
  `LENGTH vs = LENGTH ds` by
    metis_tac[listTheory.LENGTH_MAP] >>
  simp[] >> rpt strip_tac >>
  `vv_type (EL i vs) = expr_type (EL i ds)` by
    (drule (iffLR listTheory.LIST_EQ_REWRITE) >>
     simp[listTheory.EL_MAP]) >>
  `read_result cx (EL i rs) ee = (INL (EL i values),ee)` by
    (irule intcall_read_results_index >> simp[]) >>
  `EL i flags ==> is_word_type (expr_type (EL i ds))` by metis_tac[] >>
  qpat_x_assum `!j. j < LENGTH ds ==> ?tv. _`
    (qspec_then `i` mp_tac) >> simp[] >> strip_tac >> gvs[]
QED
