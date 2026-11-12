(* The entry projection does not inspect uncalled internal functions. *)
Theory deployOutcomesFreeEntry
Ancestors
  vyperCompiler list venomInst deployOutcomesFreeArgs deployOutcomesFreeScaffold
  ctorUnitShape ctorGeneratorShape ctorShapeProps loweringShapeProps supportedStmtTraverse moduleLowering deployOutcomesFreeLowering loweringShapeDefs
  context emitHelper compileEnv ctorDeployLoweringCode compileVyper ctorDeployDefs stmtLowering
Libs
  monadsyntax

Theorem split_blocks_at_partition:
  !blocks label pre suf.
    split_blocks_at label blocks = SOME (pre,suf) ==>
    blocks = pre ++ suf
Proof
  Induct_on `blocks` >> simp[split_blocks_at_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem package_internal_blocks_entry_every:
  !ds blocks entry fs P.
    package_internal_blocks ds blocks = SOME (entry,fs) /\
    EVERY P blocks ==> EVERY P entry
Proof
  Cases_on `ds` >> simp[package_internal_blocks_def] >>
  rename1 `d::rest` >> PairCases_on `d` >>
  simp[package_internal_blocks_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule split_blocks_at_partition >> strip_tac >> gvs[]
QED

Theorem extract_context_entry_every:
  extract_context_with_internals label internals st = SOME (ctx,data) /\
  (!entry fs.
    package_internal_blocks (internal_fn_descriptors internals)
      (REVERSE st.cs_blocks ++
        [<|bb_label := st.cs_current_bb;
           bb_instructions := st.cs_current_insts|>]) = SOME (entry,fs) ==>
    EVERY (\bb. EVERY P bb.bb_instructions) entry) ==>
  ?fn. ctx.ctx_entry = SOME label /\
       lookup_function label ctx.ctx_functions = SOME fn /\
       EVERY P (fn_insts fn)
Proof
  simp[extract_context_with_internals_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  qexists_tac `mk_raw_function label entry_blocks` >>
  simp[mk_venom_context_def, lookup_function_def, mk_raw_function_def,
       fn_insts_def, EVERY_fn_insts_blocks, FIND_thm]
QED

Theorem compile_generate_deploy_prefix_excludes_outcomes:
  (!env s.
    EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE])
      bb.bb_instructions) (all_blocks s) ==>
    EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE])
      bb.bb_instructions)
      (all_blocks (SND (compile_stmts env NoLoop NoneT ss s)))) ==>
  !s. EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE])
      bb.bb_instructions) (all_blocks s) ==>
    EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE])
      bb.bb_instructions)
      (all_blocks (SND (compile_generate_deploy has rt imm args sz [] env ss
        pay nr key trans s)))
Proof
  strip_tac >>
  gvs[GSYM outcomes_free_all_blocks] >>
  Cases_on `has` >> simp[compile_generate_deploy_def, compile_internal_fn_bodies_def]
  >- (Cases_on `env.ce_nonreentrant` >> rename1 `env.ce_nonreentrant = (g,rest)` >>
      PairCases_on `rest` >> Cases_on `trans` >> Cases_on `rest2` >>
      asm_rewrite_tac [] >> Cases_on `imm > 0` >>
      rpt (FIRST [gen_tac, strip_tac,
        CHANGED_TAC (simp[outcomes_free_return, outcomes_free_fresh,
          outcomes_free_get, outcomes_free_new_block, outcomes_free_emit_ops,
          outcomes_free_register_constructor_args_state]),
        irule outcomes_free_bind, irule outcomes_free_ignore_bind, conj_tac,
        first_assum irule, IF_CASES_TAC]) >>
      rpt IF_CASES_TAC >>
      gvs[compile_fixed_region_with_id_def, compile_nonreentrant_lock_def,
        compile_nonreentrant_unlock_def, compile_constructor_epilogue_def,
        compile_alloc_buffer_def, emit_op_def, emit_void_def, emit_inst_def,
        fresh_id_def, fresh_var_def, emit_def, comp_bind_def,
        comp_ignore_bind_def, comp_return_def, outcomes_free_state_insts,
        mk_inst_def])
  >> simp[compile_simple_deploy_def, compile_alloc_buffer_def,
       emit_op_def, emit_void_def, emit_inst_def, fresh_id_def, fresh_var_def,
       emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       outcomes_free_state_insts, mk_inst_def]
QED

Theorem compile_generate_deploy_prefix_split:
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

Theorem compile_generate_deploy_entry_package:
  compile_generate_deploy has rt imm args sz [] env ss pay nr key trans
    (initial_compile_state "__deploy") = ((),prefix_st) /\
  compile_generate_deploy has rt imm args sz ifns env ss pay nr key trans
    (initial_compile_state "__deploy") = ((),st) /\
  (has ==> cenv_static_ok env /\ env.ce_return_pc = NONE /\
    ~supported_stmts_expr_exists expr_shape_root ss) /\
  (~has ==> ifns = []) /\
  EVERY internal_fn_shape_ok ifns /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ifns) /\
  ALL_DISTINCT (MAP FST (internal_fn_descriptors ifns)) ==>
  ?fs. package_internal_blocks (internal_fn_descriptors ifns) (all_blocks st) =
    SOME (all_blocks prefix_st,fs)
Proof
  rpt strip_tac >>
  qpat_assum `compile_generate_deploy _ _ _ _ _ [] _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac compile_generate_deploy_shape) >>
  simp[internal_fn_descriptors_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_generate_deploy _ _ _ _ _ ifns _ _ _ _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[compile_generate_deploy_prefix_split] >>
  simp[comp_ignore_bind_def, comp_bind_def] >>
  Cases_on `has` >> gvs[compile_internal_fn_bodies_def, comp_return_def,
    internal_fn_descriptors_def, package_internal_blocks_def] >>
  strip_tac >> drule_all compile_internal_fn_bodies_shape >> strip_tac >>
  asm_rewrite_tac [] >> irule_at Any package_internal_blocks_segments >> simp[] >>
  REWRITE_TAC[EVERY_MEM] >> rpt strip_tac >> BETA_TAC >>
  irule deploy_internal_label_separate >> gvs[EVERY_MEM]
QED

Theorem run_deploy_lowering_entry_excludes_outcomes:
  (!env s.
    EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE])
      bb.bb_instructions) (all_blocks s) ==>
    EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE])
      bb.bb_instructions)
      (all_blocks (SND (compile_stmts env NoLoop NoneT ss s)))) /\
  run_deploy_lowering has rp bc imm args sz ifns env ss pay nr key trans
    "__deploy" = SOME u /\
  (has ==> cenv_static_ok env /\ env.ce_return_pc = NONE /\
    ~supported_stmts_expr_exists expr_shape_root ss) /\
  (~has ==> ifns = []) /\
  EVERY internal_fn_shape_ok ifns /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ifns) /\
  ALL_DISTINCT (MAP FST (internal_fn_descriptors ifns)) ==>
  ?name fn. u.cu_context.ctx_entry = SOME name /\
    lookup_function name u.cu_context.ctx_functions = SOME fn /\
    EVERY (\i. ~MEM i.inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts fn)
Proof
  rpt strip_tac >>
  `!s. EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE])
      bb.bb_instructions) (all_blocks s) ==>
    EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE])
      bb.bb_instructions)
      (all_blocks (SND (compile_generate_deploy has (LENGTH bc) imm args sz [] env ss
        pay nr key trans s)))` by
    (rpt strip_tac >> irule compile_generate_deploy_prefix_excludes_outcomes >> simp[]) >>
  pop_assum (qspec_then `initial_compile_state "__deploy"` mp_tac) >>
  (impl_tac >- simp[all_blocks_def, initial_compile_state_def]) >> strip_tac >>
  Cases_on `compile_generate_deploy has (LENGTH bc) imm args sz [] env ss
    pay nr key trans (initial_compile_state "__deploy")` >>
  rename1 `_ = (pr,prefix_st)` >> Cases_on `pr` >>
  Cases_on `compile_generate_deploy has (LENGTH bc) imm args sz ifns env ss
    pay nr key trans (initial_compile_state "__deploy")` >>
  rename1 `compile_generate_deploy _ _ _ _ _ ifns _ _ _ _ _ _ _ = (rv,st)` >>
  Cases_on `rv` >>
  drule_all compile_generate_deploy_entry_package >> strip_tac >>
  qpat_x_assum `run_deploy_lowering _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[run_deploy_lowering_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  `?fn. ctx.ctx_entry = SOME "__deploy" /\
    lookup_function "__deploy" ctx.ctx_functions = SOME fn /\
    EVERY (\i. ~MEM i.inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts fn)` by
    (drule extract_context_entry_every >> disch_then irule >>
     gvs[all_blocks_def]) >>
  gvs[install_immutable_reservation_def] >> metis_tac[]
QED

Theorem lower_vyper_deploy_unit_entry_excludes_outcomes:
  deploy_source_ok tops am tx /\
  lower_vyper_deploy_unit tops rp bc = SOME u /\
  (!exts ints fb cf ce args pay nr key ut ss ret.
    classify_functions tops = (exts,ints,fb,SOME cf) /\
    set_constructor_package_target rp.rpol_target
      (package_constructor tops T (K global_nonreentrant_slot) cf) =
        (ce,args,pay,nr,key,ut,ss,ret) ==>
    !env s.
      EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
        [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE])
        bb.bb_instructions) (all_blocks s) ==>
      EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
        [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE])
        bb.bb_instructions)
        (all_blocks (SND (compile_stmts env NoLoop NoneT ss s)))) ==>
  ?name fn. u.cu_context.ctx_entry = SOME name /\
    lookup_function name u.cu_context.ctx_functions = SOME fn /\
    EVERY (\i. ~MEM i.inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts fn)
Proof
  strip_tac >>
  qpat_x_assum `lower_vyper_deploy_unit _ _ _ = _` mp_tac >>
  simp[lower_vyper_deploy_unit_def] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >>
  Cases_on `ctor_fn` >> gvs[]
  >- (gvs[set_constructor_package_target_def] >>
      irule (SRULE [] run_deploy_lowering_entry_excludes_outcomes) >>
      goal_assum (drule_at Any) >>
      simp[compile_stmt_def, comp_return_def, internal_fn_descriptors_def]) >>
  drule_all deploy_constructor_package_shape >> strip_tac >>
  `supported_program tops` by fs[deploy_source_ok_def] >>
  irule (SRULE [] run_deploy_lowering_entry_excludes_outcomes) >>
  goal_assum (drule_at Any) >> simp[] >>
  drule deploy_internal_package_certificates >>
  disch_then (qspecl_then [`rp.rpol_target`, `T`, `K global_nonreentrant_slot`,
    `T`, `compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) tops`]
    mp_tac) >> simp[] >> metis_tac[]
QED
