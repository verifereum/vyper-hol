(* CREATE-free constructor and internal packages emit no CREATE instructions. *)
Theory ctorDeployNoCreate
Ancestors
  loweringRuntimeNoCreate loweringRuntimeOpcodes loweringFunctionOpcodes loweringPackageInsts
  ctorDeployLoweringCode ctorDeployDefs ctorCallFreeRules moduleLowering compileVyper
  vyperCompiler context compileEnv loweringShapeDefs venomInst list pair
  loweringCreateSource loweringCreatePackages deployDynamicMemory e2eDeployDefs
  supportedExprTraverse supportedStmtTraverse constSubst alist

val _ = Parse.hide "tops";
val _ = Parse.hide "body";

Theorem comp_ignore_bind_return_unit[local]:
  comp_ignore_bind (m:unit compiler) (comp_return ()) = m
Proof
  simp[FUN_EQ_THM, comp_ignore_bind_def, comp_bind_def, comp_return_def,
       pairTheory.ELIM_UNCURRY, pairTheory.PAIR_FST_SND_EQ, oneTheory.one]
QED

Theorem compile_generate_deploy_prefix_split[local]:
  compile_generate_deploy has rt imm args sz ifns env ss pay nr key trans =
  comp_ignore_bind
    (compile_generate_deploy has rt imm args sz [] env ss pay nr key trans)
    (if has then compile_internal_fn_bodies ifns else comp_return ())
Proof
  Cases_on `has` >>
  simp[compile_generate_deploy_def, compile_internal_fn_bodies_def,
       comp_ignore_bind_def, comp_bind_assoc] >>
  simp[FUN_EQ_THM, comp_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt pairarg_tac >> gvs[]
QED

Theorem deploy_prefix_no_create[local]:
  (has ==> package_body_avoids create_or_short_builtin_root env ss) ==>
  !st. EVERY (\i. i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_generate_deploy has rt imm args sz [] env ss
      pay nr key trans st)))
Proof
  Cases_on `has` >>
  PURE_REWRITE_TAC [compile_generate_deploy_def, COND_CLAUSES,
    compile_internal_fn_bodies_def, comp_ignore_bind_return_unit, LET_THM,
    pairTheory.ELIM_UNCURRY] >> BETA_TAC >> rpt strip_tac
  >- (irule (BETA_RULE (Q.INST [`P` |-> `\opc. opc <> CREATE /\ opc <> CREATE2`]
        constructor_prefix_opcode_every)) >>
      fs[DISJ_IMP_THM, FORALL_AND_THM, package_body_avoids_def] >>
      metis_tac[compile_runtime_stmts_no_create]) >>
  `compile_simple_deploy rt imm =
    compile_constructor_epilogue (rt + imm) 0 (Lit 0w)` by
    simp[compile_simple_deploy_def, compile_constructor_epilogue_def] >>
  pop_assum SUBST1_TAC >>
  irule (BETA_RULE (Q.INST [`P` |-> `\opc. opc <> CREATE /\ opc <> CREATE2`]
    outcomes_free_constructor_epilogue)) >> simp[]
QED

Theorem run_deploy_lowering_no_create[local]:
  run_deploy_lowering has rp bc imm args sz ifns env ss pay nr key trans entry = SOME unit /\
  (has ==> package_body_avoids create_or_short_builtin_root env ss) /\
  EVERY (internal_package_avoids create_or_short_builtin_root) ifns ==>
  EVERY (\fn. EVERY (\i. i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (fn_insts fn)) unit.cu_context.ctx_functions
Proof
  strip_tac >>
  `!st. EVERY (\i. i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
     (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
     (state_insts (SND (compile_generate_deploy has (LENGTH bc) imm args sz
       ifns env ss pay nr key trans st)))` by
    (simp[Once compile_generate_deploy_prefix_split] >>
     ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac
     >- metis_tac[deploy_prefix_no_create] >>
     Cases_on `has` >> simp[every_state_insts_return] >>
     mp_tac (Q.INST [`P` |-> `\opc. opc <> CREATE /\ opc <> CREATE2`,
                     `root` |-> `create_or_short_builtin_root`]
       opcode_every_internal_fn_bodies) >> simp[compile_runtime_stmts_no_create]) >>
  qpat_x_assum `run_deploy_lowering _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[run_deploy_lowering_def] >> pairarg_tac >> gvs[AllCaseEqs()] >>
  rpt strip_tac >> gvs[install_immutable_reservation_def] >>
  `EVERY (\i. i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
     (state_insts st1)` by
    (qpat_x_assum `!st. EVERY _ (state_insts st) ==> _`
       (qspec_then `initial_compile_state entry` mp_tac) >>
     simp[initial_compile_state_insts]) >>
  drule_all extract_context_with_internals_every >> simp[]
QED

Theorem deploy_classified_function_avoids_create[local]:
  !layouts addr tops art mut nr rr name args dflts ret body.
  check_contract T layouts addr [(NONE,tops)] = SOME art /\
  ~deploy_dalloca_form_occurs expr_create_root tops /\
  IS_SOME (SND (SND (SND (classify_functions tops)))) /\
  (MEM (mut,nr,rr,name,args,dflts,ret,body) (FST (SND (classify_functions tops))) \/
   SND (SND (SND (classify_functions tops))) =
     SOME (mut,nr,rr,name,args,dflts,ret,body)) ==>
  ~supported_stmts_expr_exists create_or_short_builtin_root body /\
  EVERY (\e. ~supported_expr_exists create_or_short_builtin_root e) dflts
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!id r. ALOOKUP (module_consts_env tops []) id = SOME r ==>
     ~supported_expr_exists create_or_short_builtin_root r` by
    metis_tac[checked_const_replacements_avoid_create, ALOOKUP_def] >>
  `!vis mut0 nr0 rr0 name0 args0 dflts0 ret0 body0.
    MEM (FunctionDecl vis mut0 nr0 rr0 name0 args0 dflts0 ret0 body0) tops /\
    (vis = Deploy \/ vis = Internal) ==>
    ~supported_stmts_expr_exists create_or_short_builtin_root body0 /\
    EVERY (\e. ~supported_expr_exists create_or_short_builtin_root e) dflts0` by
    (rpt gen_tac >> strip_tac >>
     `~supported_stmts_expr_exists expr_create_root body0 /\
      ~EXISTS (supported_expr_exists expr_create_root) dflts0` by
       (fs[deploy_dalloca_form_occurs_def] >> metis_tac[]) >>
     metis_tac[checked_function_avoids_create]) >>
  qpat_x_assum `MEM _ _ \/ _ = SOME _` strip_assume_tac
  >- (gvs[loweringShapePropsTheory.MEM_classify_internal, subst_consts_fn_def] >>
      irule subst_consts_body_avoids_create >> simp[] >> metis_tac[]) >>
  drule classify_functions_ctor_mem >> strip_tac >>
  gvs[subst_consts_fn_def] >>
  irule subst_consts_body_avoids_create >> simp[] >> metis_tac[]
QED

Theorem deploy_classified_defaults_avoid_create[local]:
  check_contract T layouts addr [(NONE,tops)] = SOME art /\
  ~deploy_dalloca_form_occurs expr_create_root tops /\
  IS_SOME (SND (SND (SND (classify_functions tops)))) ==>
  EVERY (\nd. ~supported_exprs_exists create_or_short_builtin_root (SND nd))
    (build_func_defaults tops)
Proof
  rw[build_func_defaults_def, EVERY_MEM] >>
  gvs[MEM_MAP] >> PairCases_on `y` >> gvs[] >>
  simp[supported_exprs_exists_every, NOT_EXISTS, combinTheory.o_DEF] >>
  metis_tac[deploy_classified_function_avoids_create, EVERY_MEM]
QED

Theorem lower_vyper_deploy_unit_no_create:
  !tops am tx rp bc unit. deploy_source_ok tops am tx /\
    ~deploy_dalloca_form_occurs expr_create_root tops /\
    lower_vyper_deploy_unit tops rp bc = SOME unit ==>
    !fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
      inst.inst_opcode <> CREATE /\ inst.inst_opcode <> CREATE2
Proof
  rpt gen_tac >> strip_tac >>
  `?art. check_contract T am.layouts tx.target [(NONE,tops)] = SOME art` by
    fs[deploy_source_ok_def, deploy_typing_ok_def] >>
  qpat_x_assum `lower_vyper_deploy_unit _ _ _ = _` mp_tac >>
  simp[lower_vyper_deploy_unit_def] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `classify_functions tops = (_,ints,_,cf)` >> Cases_on `cf` >> gvs[]
  >- (drule run_deploy_lowering_no_create >> simp[EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\nd. ~supported_exprs_exists create_or_short_builtin_root (SND nd))
     (build_func_defaults tops)` by
    (drule deploy_classified_defaults_avoid_create >> fs[]) >>
  rename1 `classify_functions tops = (_,ints,_,SOME ctor)` >>
  `!f. MEM f (order_internals (deploy_internal_order (SOME ctor) ints) ints) ==>
    internal_package_avoids create_or_short_builtin_root
      (set_internal_package_target rp.rpol_target
        (package_internal_fn tops T (K global_nonreentrant_slot) T
          (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) tops) f))` by
    (rpt gen_tac >> strip_tac >> PairCases_on `f` >>
     `~supported_stmts_expr_exists create_or_short_builtin_root f7` by
       (qspecl_then [`am.layouts`, `tx.target`, `tops`, `art`,
                     `f0`, `f1`, `f2`, `f3`, `f4`, `f5`, `f6`, `f7`]
          mp_tac deploy_classified_function_avoids_create >>
        fs[] >> metis_tac[]) >>
     simp[package_internal_fn_def, set_internal_package_target_def,
          internal_package_avoids_def, package_body_avoids_def,
          update_cenv_nonreentrant_def, build_compile_env_defaults]) >>
  PairCases_on `ctor` >>
  `~supported_stmts_expr_exists create_or_short_builtin_root ctor7` by
    (qspecl_then [`am.layouts`, `tx.target`, `tops`, `art`,
                  `ctor0`, `ctor1`, `ctor2`, `ctor3`, `ctor4`, `ctor5`, `ctor6`, `ctor7`]
       mp_tac deploy_classified_function_avoids_create >> fs[]) >>
  gvs[package_constructor_def, set_constructor_package_target_def] >>
  drule run_deploy_lowering_no_create >>
  simp[EVERY_MAP, EVERY_MEM, package_body_avoids_def,
       update_cenv_nonreentrant_def, build_compile_env_defaults] >>
  fs[EVERY_MEM] >> metis_tac[]
QED
