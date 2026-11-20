(* The current source gate excludes CREATE and CREATE2 throughout deploy lowering. *)
Theory ctorDeployNoCreate
Ancestors
  loweringRuntimeNoCreate loweringRuntimeOpcodes loweringFunctionOpcodes loweringPackageInsts
  ctorDeployLoweringCode ctorDeployDefs ctorCallFreeRules moduleLowering compileVyper
  vyperCompiler context compileEnv loweringShapeDefs venomInst list pair

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
  (has ==> cenv_static_ok env /\ ~supported_stmts_expr_exists expr_shape_root ss) ==>
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
      fs[DISJ_IMP_THM, FORALL_AND_THM, loweringShapePropsTheory.cenv_static_ok_def] >>
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
  (has ==> cenv_static_ok env /\ ~supported_stmts_expr_exists expr_shape_root ss) /\
  EVERY internal_fn_shape_ok ifns ==>
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
     mp_tac (Q.INST [`P` |-> `\opc. opc <> CREATE /\ opc <> CREATE2`]
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

Theorem lower_vyper_deploy_unit_no_create:
  !tops am tx rp bc unit. deploy_source_ok tops am tx /\
    lower_vyper_deploy_unit tops rp bc = SOME unit ==>
    !fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
      inst.inst_opcode <> CREATE /\ inst.inst_opcode <> CREATE2
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `lower_vyper_deploy_unit _ _ _ = _` mp_tac >>
  simp[lower_vyper_deploy_unit_def] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `classify_functions tops = (_,_,_,cf)` >> Cases_on `cf` >> gvs[]
  >- (drule run_deploy_lowering_no_create >> simp[EVERY_MEM] >> metis_tac[]) >>
  drule_all deploy_constructor_package_shape >> strip_tac >>
  `supported_program tops` by fs[deploy_source_ok_def] >>
  rename1 `classify_functions tops = (_,ints,_,SOME ctor)` >>
  drule deploy_internal_package_certificates >>
  disch_then (qspecl_then [`rp.rpol_target`, `T`, `K global_nonreentrant_slot`,
    `T`, `compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) tops`,
    `order_internals (deploy_internal_order (SOME ctor) ints) ints`] mp_tac) >>
  simp[PERM_order_deploy_internals] >> strip_tac >>
  drule run_deploy_lowering_no_create >> simp[EVERY_MEM] >> metis_tac[]
QED
