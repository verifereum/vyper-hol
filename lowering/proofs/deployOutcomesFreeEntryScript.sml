(* The entry projection does not inspect uncalled internal functions. *)
Theory deployOutcomesFreeEntry
Ancestors
  vyperCompiler list venomInst deployOutcomesFreeArgs deployOutcomesFreeScaffold
  ctorGeneratorShape moduleLowering deployOutcomesFreeLowering loweringShapeDefs
  context emitHelper compileEnv
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
