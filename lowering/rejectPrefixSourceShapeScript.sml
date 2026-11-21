(* Shapes of defaults and compile environments that precede runtime body entry. *)
Theory rejectPrefixSourceShape
Ancestors
  compileVyper vyperCompiler compileEnv moduleLowering loweringShapeDefs constSubst loweringShapeSource runtimePeakMemoryArity
  groupedEntryPackage loweringShapeProps loweringShapeRules vyperTypeContract vyperTypeContractContext
  vyperTypeSystem vyperAST constSubstCorrect publicGetterProps
  ctorCallFreeRules ctorCallFreeExpr whitelistCheckerConsts
  loweringGroupedOpcodes loweringRuntimeOpcodes venomInst
  supportedExprTraverse supportedStmtTraverse list rich_list pair option alist

val _ = Parse.hide "tops";
val _ = Parse.hide "body";

Theorem runtime_constant_expr_no_raw_shape[local]:
  !mods e. runtime_constant_expr mods e ==> ~supported_expr_exists expr_raw_shape_root e
Proof
  ho_match_mp_tac runtime_constant_expr_ind >>
  simp[runtime_constant_expr_def, supported_expr_exists_def, expr_raw_shape_root_def,
       supported_exprs_exists_every, supported_fields_exists_every, EVERY_MEM,
       EXISTS_MEM, MEM_MAP, combinTheory.o_DEF] >>
  metis_tac[constant_expr_raw_shape]
QED

Theorem constant_expr_has_no_call[local]:
  !mods e. constant_expr mods e ==> ~supported_expr_exists expr_call_root e
Proof
  ho_match_mp_tac constant_expr_ind >>
  simp[constant_expr_def, supported_expr_exists_def, expr_call_root_def,
    supported_exprs_exists_every, supported_fields_exists_every, EVERY_MEM,
    EXISTS_MEM, MEM_MAP, combinTheory.o_DEF] >> metis_tac[]
QED

Theorem runtime_constant_expr_has_no_call[local]:
  !mods e. runtime_constant_expr mods e ==> ~supported_expr_exists expr_call_root e
Proof
  ho_match_mp_tac runtime_constant_expr_ind >>
  simp[runtime_constant_expr_def, supported_expr_exists_def, expr_call_root_def,
    supported_exprs_exists_every, supported_fields_exists_every, EVERY_MEM,
    EXISTS_MEM, MEM_MAP, combinTheory.o_DEF] >>
  metis_tac[constant_expr_has_no_call]
QED

Theorem subst_const_runtime_constant[local]:
  (!id r. ALOOKUP env id = SOME r ==> constant_expr mods r) ==>
  !ms e. ms = mods /\ runtime_constant_expr ms e ==>
    runtime_constant_expr ms (subst_consts_expr env e)
Proof
  strip_tac >>
  `!src id ty. (declared_constant mods src id \/ declared_immutable mods src id) ==>
    runtime_constant_expr mods (subst_consts_expr env (TopLevelName ty (src,id)))` by
    (rpt gen_tac >> Cases_on `src` >>
     simp[subst_consts_expr_def, runtime_constant_expr_def] >>
     Cases_on `ALOOKUP env id` >> simp[runtime_constant_expr_def] >>
     metis_tac[constant_expr_runtime_constant]) >>
  `!e. bool_literal_expr e ==> bool_literal_expr (subst_consts_expr env e)` by
    (Cases >> simp[bool_literal_expr_def, subst_consts_expr_def]) >>
  `!es. EVERY (constant_expr mods) es ==>
    EVERY (constant_expr mods) (subst_consts_exprs env es)` by
    metis_tac[subst_consts_constant_expr] >>
  ho_match_mp_tac runtime_constant_expr_ind >>
  simp[runtime_constant_expr_def] >> rpt strip_tac >> gvs[] >>
  TRY (qpat_assum `!src id ty. _` irule >> simp[] >> NO_TAC) >>
  simp[subst_consts_expr_def, runtime_constant_expr_def,
    subst_consts_fields_maps] >>
  fs[subst_consts_exprs_map, EVERY_MAP, combinTheory.o_DEF, EVERY_MEM] >>
  rpt strip_tac >> gvs[MEM_MAP] >> res_tac >> fs[] >>
  metis_tac[]
QED

Theorem checked_substituted_defaults_call_free[local]:
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  MEM (FunctionDecl vis mut nr rr name args defaults ret body) tops /\ vis <> Deploy ==>
  EVERY (\e. ~supported_expr_exists expr_call_root e)
    (subst_consts_exprs (module_consts_env tops []) defaults)
Proof
  strip_tac >>
  `module_allocated layouts addr NONE tops` by
    (drule check_contract_main_module_allocated >> simp[]) >>
  `check_function_body layouts addr [(NONE,tops)] art NONE vis mut nr args defaults ret body` by
    (irule check_contract_runtime_function_body_MEM >> simp[] >>
     qexistsl_tac [`name`,`rr`] >> simp[]) >>
  `!id r. ALOOKUP (module_consts_env tops []) id = SOME r ==>
         constant_expr [(NONE,tops)] r` by
    (rpt strip_tac >> irule checked_module_consts_env_replacement_constant >>
     simp[] >> conj_tac
     >- (qexistsl_tac [`addr`,`art`,`layouts`,`F`] >> simp[]) >>
     qexists_tac `id` >> simp[]) >>
  `EVERY (runtime_constant_expr [(NONE,tops)]) defaults` by fs[check_function_body_def] >>
  simp[subst_consts_exprs_map, EVERY_MAP, EVERY_MEM, combinTheory.o_DEF] >>
  rpt strip_tac >> fs[MEM_MAP] >>
  `runtime_constant_expr [(NONE,tops)] (subst_consts_expr (module_consts_env tops []) y)` by
    (qpat_assum `!id r. ALOOKUP _ id = SOME r ==> _`
       (mp_tac o MATCH_MP (Q.INST [`mods` |-> `[(NONE,tops)]`] subst_const_runtime_constant)) >>
     disch_then (qspecl_then [`[(NONE,tops)]`,`y`] mp_tac) >> fs[EVERY_MEM]) >>
  metis_tac[runtime_constant_expr_has_no_call]
QED

Theorem checked_substituted_default_shape[local]:
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  MEM (FunctionDecl vis mut nr rr name args defaults ret body) tops /\ vis <> Deploy ==>
  EVERY (\e. ~supported_expr_exists expr_shape_root e)
    (subst_consts_exprs (module_consts_env tops []) defaults)
Proof
  strip_tac >>
  `module_allocated layouts addr NONE tops` by
    (drule check_contract_main_module_allocated >> simp[]) >>
  `check_function_body layouts addr [(NONE,tops)] art NONE vis mut nr args defaults ret body` by
    (irule check_contract_runtime_function_body_MEM >> simp[] >>
     qexistsl_tac [`name`,`rr`] >> simp[]) >>
  drule_all (SIMP_RULE bool_ss [] (Q.INST [`mode` |-> `F`]
    checked_source_builtin_arity)) >> strip_tac >>
  `expr_shape_root = (\e. expr_raw_shape_root e \/ short_builtin_args e)` by
    (simp[FUN_EQ_THM, expr_shape_root_def, expr_raw_shape_root_def, short_builtin_args_def] >>
     metis_tac[]) >>
  `EVERY (\e. ~supported_expr_exists expr_shape_root e) defaults` by
    (simp[supported_expr_exists_disj, EVERY_MEM] >> rpt strip_tac >>
     fs[check_function_body_def, EVERY_MEM] >> metis_tac[runtime_constant_expr_no_raw_shape]) >>
  qpat_x_assum `expr_shape_root = _` kall_tac >>
  `~supported_exprs_exists expr_shape_root
      (subst_consts_exprs (module_consts_env tops []) defaults)` by
    (irule (cj 3 subst_consts_expr_shape) >>
     simp[supported_exprs_exists_every, GSYM EVERY_NOT_EXISTS, combinTheory.o_DEF] >>
     rpt gen_tac >> strip_tac >> irule checked_module_consts_env_replacement_shape >>
     goal_assum (drule_at Any) >> qexistsl_tac [`addr`,`art`,`layouts`,`F`,`[(NONE,tops)]`] >> simp[]) >>
  fs[supported_exprs_exists_every, GSYM EVERY_NOT_EXISTS, combinTheory.o_DEF]
QED

Theorem checked_external_defaults_shape[local]:
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  MEM (mut,nr,rr,name,args,defaults,ret,body) (FST (classify_functions tops)) ==>
  EVERY (\e. ~supported_expr_exists expr_shape_root e) defaults
Proof
  strip_tac >> drule classify_functions_external_source >> strip_tac >>
  gvs[subst_consts_fn_def]
  >- (mp_tac (Q.INST [`vis` |-> `External`, `art` |-> `art`,
        `layouts` |-> `layouts`, `addr` |-> `addr`, `name` |-> `name`,
        `defaults` |-> `rawdefaults`, `body` |-> `rawbody`] checked_substituted_default_shape) >>
      simp[] >> metis_tac[]) >>
  drule public_getter_defaults >> simp[subst_consts_expr_def]
QED

Theorem checked_internal_defaults_shape[local]:
  check_contract F layouts addr [(NONE,tops)] = SOME art ==>
  EVERY (\nd. ~supported_exprs_exists expr_shape_root (SND nd)) (build_func_defaults tops)
Proof
  rw[build_func_defaults_def, EVERY_MEM] >>
  gvs[MEM_MAP] >> PairCases_on `y` >>
  gvs[MEM_classify_internal, subst_consts_fn_def] >>
  simp[supported_exprs_exists_every, GSYM EVERY_NOT_EXISTS, combinTheory.o_DEF] >>
  metis_tac[checked_substituted_default_shape, function_visibility_distinct]
QED

(* The dispatcher builds a deferred body job. Its code depends only on the
   selected entry and common environment, so body shape is irrelevant here. *)
Definition entry_group_without_body_def[local]:
  entry_group_without_body (ExternalSingle sel (lbl,ce,args,m,pay,nr,key,tr,vw,body,rt)) =
    ExternalSingle sel (lbl,ce,args,m,pay,nr,key,tr,vw,[],rt) /\
  entry_group_without_body (ExternalDefaults common entries specs off) =
    ExternalDefaults (common with ec_body := []) entries specs off
End

Theorem group_entries_body_independent[local]:
  !entries st. compile_group_entries mid entries (common with ec_body := []) vars off st =
    compile_group_entries mid entries common vars off st
Proof
  Induct >> simp[compile_group_entries_def] >> qx_gen_tac `h` >> PairCases_on `h` >>
  simp[compile_group_entries_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> fs[])
QED

Theorem external_groups_body_independent[local]:
  !groups mid st. SND (compile_external_groups mid (MAP entry_group_without_body groups) st) =
    SND (compile_external_groups mid groups st)
Proof
  Induct >> simp[compile_external_groups_def] >> Cases_on `h`
  >- (PairCases_on `p` >> PairCases_on `p0` >>
      simp[entry_group_without_body_def, compile_external_groups_def,
        comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      rpt gen_tac >> rpt (pairarg_tac >> fs[]) >> metis_tac[SND]) >>
  simp[entry_group_without_body_def, compile_external_groups_def, group_entries_body_independent,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> fs[]) >> metis_tac[SND]
QED

Theorem group_dispatch_body_independent[local]:
  SND (compile_group_dispatch_linear (MAP entry_group_without_body groups) fallback st) =
  SND (compile_group_dispatch_linear groups fallback st)
Proof
  simp[compile_group_dispatch_linear_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> fs[]) >> metis_tac[external_groups_body_independent, pairTheory.SND]
QED

Theorem checked_package_entry_metadata[local]:
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  set_external_package_target target
    (package_external_fn tops use_trans nkeys (mut,nr,rr,name,args,defaults,ret,body)) =
    (lbl,ce,pos,mincd,pay,nr',key,tr,vw,stmts,rt) ==>
  external_fn_shape_ok (lbl,ce,pos,mincd,pay,nr',key,tr,vw,[],rt)
Proof
  strip_tac >> drule checked_internal_defaults_shape >> strip_tac >>
  `cenv_static_ok (build_compile_env tops External mut name args ret body use_trans)` by
    (irule build_compile_env_static >> simp[]) >>
  Cases_on `ret = NoneT` >>
  gvs[package_external_fn_def, set_external_package_target_def, external_fn_shape_ok_def,
      update_cenv_ret_abi_def, update_cenv_nonreentrant_def, cenv_static_ok_def,
      build_compile_env_external_no_return_pc, supported_stmt_expr_exists_def,
      rich_listTheory.IS_PREFIX_APPEND] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem every_default_spec_shape[local]:
  !args defaults. EVERY (\e. ~supported_expr_exists expr_shape_root e) defaults ==>
    EVERY (\((n,ty),e). ~supported_expr_exists expr_shape_root e) (ZIP (args,defaults))
Proof
  Induct >> Cases_on `defaults` >> simp[ZIP_def] >> PairCases_on `h` >> simp[]
QED

Theorem checked_entry_group_shape[local]:
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  MEM src (FST (classify_functions tops)) ==>
  external_group_shape_ok (entry_group_without_body (package_external_group tops target trans nkeys src))
Proof
  strip_tac >> PairCases_on `src` >>
  drule_all checked_external_defaults_shape >> strip_tac >>
  simp[package_external_group_def] >> IF_CASES_TAC >>
  Cases_on `set_external_package_target target
      (package_external_fn tops trans nkeys (src0,src1,src2,src3,src4,src5,src6,src7))` >>
  PairCases_on `r` >> simp[entry_group_without_body_def] >>
  drule_all checked_package_entry_metadata >> strip_tac >-
    fs[external_group_shape_ok_def, compute_selector_def, IS_PREFIX_APPEND] >>
  fs[external_group_shape_ok_def, external_fn_shape_ok_def, external_common_shape_ok_def,
    external_common_label_def, jump_label_ok_def, IS_PREFIX_APPEND,
    EVERY_MAP, pairTheory.FORALL_PROD, external_prefix_label_def, compute_selector_def] >>
  conj_tac
  >- simp[EVERY_MEM, pairTheory.FORALL_PROD] >>
  `EVERY (\((n,ty),e). ~supported_expr_exists expr_shape_root e)
    (ZIP (DROP (LENGTH src4 - LENGTH src5) (src4 : argument list),src5))` by
    (irule every_default_spec_shape >> simp[]) >>
  fs[EVERY_MEM, pairTheory.FORALL_PROD] >> first_assum ACCEPT_TAC
QED

Theorem checked_group_dispatch_shape:
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  groups = MAP (package_external_group tops target trans nkeys) (FST (classify_functions tops)) /\
  jump_label_ok fallback /\ ~label_sfx "dispatch" fallback /\ shape_state sa /\
  compile_group_dispatch_linear groups fallback sa = (jobs,sb) ==>
  shape_extends F jump_label_ok sa sb /\ shape_state sb
Proof
  strip_tac >>
  `EVERY external_group_shape_ok (MAP entry_group_without_body groups)` by
    (qpat_assum `groups = _` SUBST1_TAC >>
     simp[EVERY_MAP, EVERY_MEM, combinTheory.o_DEF] >>
     metis_tac[checked_entry_group_shape]) >>
  `?jobs'. compile_group_dispatch_linear (MAP entry_group_without_body groups) fallback sa = (jobs',sb)` by
    (Cases_on `compile_group_dispatch_linear (MAP entry_group_without_body groups) fallback sa` >>
     mp_tac (Q.INST [`st` |-> `sa`] group_dispatch_body_independent) >> simp[]) >>
  mp_tac (Q.SPECL [`MAP entry_group_without_body groups`,`fallback`]
    compile_group_dispatch_linear_shape) >> simp[shape_step_def] >>
  disch_then (qspecl_then [`sa`,`jobs'`,`sb`] mp_tac) >> gvs[]
QED


Theorem checked_external_defaults_call_free[local]:
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  MEM (mut,nr,rr,name,args,defaults,ret,body) (FST (classify_functions tops)) ==>
  EVERY (\e. ~supported_expr_exists expr_call_root e) defaults
Proof
  strip_tac >> drule classify_functions_external_source >> strip_tac >>
  gvs[subst_consts_fn_def]
  >- (mp_tac (Q.INST [`vis` |-> `External`, `art` |-> `art`,
        `layouts` |-> `layouts`, `addr` |-> `addr`, `name` |-> `name`,
        `defaults` |-> `rawdefaults`, `body` |-> `rawbody`] checked_substituted_defaults_call_free) >>
      simp[] >> metis_tac[]) >>
  drule public_getter_defaults >> simp[subst_consts_expr_def]
QED

Theorem checked_internal_defaults_call_free[local]:
  check_contract F layouts addr [(NONE,tops)] = SOME art ==>
  EVERY (\nd. ~supported_exprs_exists expr_call_root (SND nd)) (build_func_defaults tops)
Proof
  rw[build_func_defaults_def, EVERY_MEM] >>
  gvs[MEM_MAP] >> PairCases_on `y` >>
  gvs[MEM_classify_internal, subst_consts_fn_def] >>
  simp[supported_exprs_exists_every, GSYM EVERY_NOT_EXISTS, combinTheory.o_DEF] >>
  metis_tac[checked_substituted_defaults_call_free, function_visibility_distinct]
QED

Theorem checked_group_entry_call_free[local]:
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  MEM src (FST (classify_functions tops)) ==>
  external_group_avoids (\e. expr_call_root e \/ expr_shape_root e)
    (entry_group_without_body (package_external_group tops target trans nkeys src))
Proof
  strip_tac >> PairCases_on `src` >>
  `LENGTH src5 <= LENGTH src4` by
    (drule_all checked_grouped_defaults_length >> simp[]) >>
  `LENGTH (DROP (LENGTH src4 - LENGTH src5) src4) = LENGTH src5` by
    (simp[LENGTH_DROP] >> decide_tac) >>
  drule_all checked_external_defaults_shape >> strip_tac >>
  drule_all checked_external_defaults_call_free >> strip_tac >>
  drule checked_internal_defaults_shape >> strip_tac >>
  drule checked_internal_defaults_call_free >> strip_tac >>
  `EVERY (\nd. ~supported_exprs_exists (\e. expr_call_root e \/ expr_shape_root e) (SND nd))
     (build_func_defaults tops)` by
    (fs[supported_exprs_exists_every, supported_expr_exists_disj, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  Cases_on `src6 = NoneT` >> Cases_on `NULL src5` >>
  simp[package_external_group_def, package_external_fn_def, set_external_package_target_def,
       entry_group_without_body_def, external_group_avoids_def, external_package_avoids_def,
       package_body_avoids_def, supported_stmt_expr_exists_def,
       update_cenv_ret_abi_def, update_cenv_nonreentrant_def,
       build_compile_env_ce_func_defaults] >>
  simp[kwarg_specs_avoid_def, EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD,
       supported_expr_exists_disj] >>
  rpt strip_tac >> imp_res_tac MEM_ZIP_MEM_MAP >> fs[EVERY_MEM] >> res_tac >> gvs[]
QED

Theorem checked_group_dispatch_no_invoke:
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  groups = MAP (package_external_group tops target trans nkeys) (FST (classify_functions tops)) /\
  state_insts sa = [] /\
  compile_group_dispatch_linear groups fallback sa = (jobs,sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE) (state_insts sb)
Proof
  strip_tac >>
  `EVERY (external_group_avoids (\e. expr_call_root e \/ expr_shape_root e))
      (MAP entry_group_without_body groups)` by
    (qpat_assum `groups = _` SUBST1_TAC >>
     simp[EVERY_MAP, EVERY_MEM, combinTheory.o_DEF] >>
     metis_tac[checked_group_entry_call_free]) >>
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`,
     `root` |-> `\e. expr_call_root e \/ expr_shape_root e`,
     `groups` |-> `MAP entry_group_without_body groups`, `fb` |-> `fallback`]
    opcode_every_group_dispatch_linear) >> simp[] >>
  impl_tac >- simp[supported_expr_exists_disj, compile_expr_call_free] >>
  disch_then (qspec_then `sa` mp_tac) >> simp[group_dispatch_body_independent] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem checked_group_dispatch_safe_opcodes:
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  groups = MAP (package_external_group tops target trans nkeys) (FST (classify_functions tops)) /\
  fresh_label "fallback" (initial_compile_state "__entry") = (fallback,sa) /\
  compile_group_dispatch_linear groups fallback sa = (jobs,sb) ==>
  EVERY (\i. i.inst_opcode <> DALLOCA /\ i.inst_opcode <> INVOKE) (state_insts sb)
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`F`,`jump_label_ok`,`\st. T`,`"fallback"`] shape_step_fresh_label_sfx) >>
  simp[shape_stable_def, shape_step_def] >>
  disch_then (qspecl_then [`initial_compile_state "__entry"`,`fallback`,`sa`] mp_tac) >>
  simp[shape_state_initial_compile_state] >> strip_tac >>
  `jump_label_ok fallback /\ ~label_sfx "dispatch" fallback` by
    (simp[jump_label_ok_def] >> strip_tac >>
     mp_tac (Q.INST [`s1` |-> `"fallback"`,`s2` |-> `"dispatch"`,`l1` |-> `fallback`,`l2` |-> `fallback`] label_sfx_distinct) >> simp[]) >>
  `state_insts sa = []` by
    (gvs[fresh_label_def, initial_compile_state_def, state_insts_def, all_blocks_def]) >>
  drule_all checked_group_dispatch_no_invoke >> strip_tac >>
  drule_all checked_group_dispatch_shape >> strip_tac >>
  fs[shape_extends_def, added_insts_def, EVERY_MEM, lowered_inst_ok_def] >> metis_tac[]
QED
