(* Without a constructor, the deploy unit is compile_simple_deploy's: an
 * ALLOCA for the runtime code and the immutables section, a CODECOPY into
 * it and a RETURN of it.  Its run is memory-safe.
 * TOP-LEVEL: deploy_no_ctor_run_mem_safe (admitted until proved).
 *)
Theory ctorDeployMemoryRunMemNoCtor
Ancestors
  ctorDeployDefs immSectionDead gasSummary memSafeRun venomInst
  moduleLowering context vyperCompiler emitHelper compileEnv compileVyper
  venomExecSemantics venomState unitTransformDefs contextCodegenRel codegenRel
  o1PassContract e2eEntry

Theorem simple_deploy_compile_shape[local]:
  compile_generate_deploy F runtime_size immutables_len args data_size int_fns
    cenv stmts payable nr nkey trans (initial_compile_state "__deploy") =
  ((), <| cs_next_var := 1; cs_next_label := 0; cs_next_id := 3;
          cs_current_bb := "__deploy";
          cs_current_insts :=
            [mk_inst 0 ALLOCA [Lit (n2w (runtime_size + immutables_len))] ["%0"];
             mk_inst 1 CODECOPY
               [Var "%0"; Label "runtime_begin";
                Lit (n2w (runtime_size + immutables_len))] [];
             mk_inst 2 RETURN
               [Var "%0"; Lit (n2w (runtime_size + immutables_len))] []];
          cs_blocks := []; cs_data_sections := [] |>)
Proof
  simp[compile_generate_deploy_def, compile_simple_deploy_def,
       compile_alloc_buffer_def, initial_compile_state_def,
       emit_op_def, emit_void_def, emit_inst_def, emit_def,
       fresh_id_def, fresh_var_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> EVAL_TAC
QED

Theorem deploy_no_ctor_entry_shape:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  classify_functions tops = (exts, ints, fb, NONE) /\
  lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl ==>
  lbl = "__deploy" /\
  fn = mk_raw_function "__deploy"
    [<| bb_label := "__deploy"; bb_instructions :=
       [mk_inst 0 ALLOCA [Lit (n2w (LENGTH runtime_bc + imm_len tops))] ["%0"];
        mk_inst 1 CODECOPY
          [Var "%0"; Label "runtime_begin";
           Lit (n2w (LENGTH runtime_bc + imm_len tops))] [];
        mk_inst 2 RETURN
          [Var "%0"; Lit (n2w (LENGTH runtime_bc + imm_len tops))] []] |>]
Proof
  strip_tac >>
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit` by
    fs[deploy_phases_def] >>
  qpat_x_assum `deploy_phases _ _ _ _` kall_tac >>
  qpat_x_assum `lower_vyper_deploy_unit _ _ _ = _` mp_tac >>
  simp[lower_vyper_deploy_unit_def] >>
  simp[set_constructor_package_target_def] >>
  simp[run_deploy_lowering_def, simple_deploy_compile_shape] >>
  simp[extract_context_with_internals_def, internal_fn_descriptors_def,
       package_internal_blocks_def, install_immutable_reservation_def,
       mk_venom_context_def] >>
  rpt strip_tac >> gvs[] >>
  gvs[lookup_function_def, listTheory.FIND_thm, mk_raw_function_def,
      fn_entry_label_def, entry_block_def, imm_len_def]
QED

Theorem simple_deploy_entry_mem_safe:
  s.vs_allocas = FEMPTY ==>
  !fuel. mem_safe_blocks fuel ctx
    (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
         [mk_inst 0 ALLOCA [Lit szword] ["%0"];
          mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit szword] [];
          mk_inst 2 RETURN [Var "%0"; Lit szword] []] |>])
    (s with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
               vs_inst_idx := 0 |> )
Proof
  strip_tac >> Cases >>
  simp[Once mem_safe_blocks_def, lookup_block_def, mk_raw_function_def,
       listTheory.FIND_thm, eval_phis_def, mk_inst_def, phi_prefix_length_def] >>
  qmatch_goalsub_abbrev_tac `mem_safe_block n ctx bb st` >>
  simp[Once mem_safe_block_def, Abbr `bb`, Abbr `st`, get_instruction_def,
       mem_safe_step_non_invoke, inst_dload_in_section_other,
       inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, step_inst_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[exec_alloca_def, eval_operand_def, update_var_def, is_terminator_def] >> conj_tac
  >- (simp[Once mem_safe_block_def, get_instruction_def,
           mem_safe_step_non_invoke, inst_dload_in_section_other,
           inst_mem_below_frontier_def, source_memory_read_ranges_def,
           source_memory_write_ranges_def, eval_operand_def, lookup_var_def,
           sized_source_write_range_def,
           wordsTheory.w2n_n2w, arithmeticTheory.MOD_LESS_EQ,
           step_inst_def] >>
      PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      simp[eval_operand_def, lookup_var_def] >>
      Cases_on `FLOOKUP s.vs_labels "runtime_begin"` >>
      simp[finite_mapTheory.FLOOKUP_UPDATE, is_terminator_def] >>
      `s.vs_alloca_next MOD dimword (:256) <= s.vs_alloca_next` by
        simp[arithmeticTheory.MOD_LESS_EQ] >>
      simp[] >>
      qmatch_goalsub_abbrev_tac `write_memory_with_expansion off bytes ast` >>
      simp[write_memory_with_expansion_def, LET_THM] >>
      qmatch_goalsub_abbrev_tac `ast with <|vs_memory := mem; vs_inst_idx := 2|>` >>
      simp[Abbr `ast`, Once mem_safe_block_def, get_instruction_def,
           mem_safe_step_non_invoke, inst_dload_in_section_other,
           inst_mem_below_frontier_def, source_memory_read_ranges_def,
           source_memory_write_ranges_def, memory_range_of_operands_def,
           eval_operand_def, lookup_var_def,
           finite_mapTheory.FLOOKUP_UPDATE, wordsTheory.w2n_n2w,
           step_inst_def] >>
      PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      simp[eval_operand_def, lookup_var_def,
           finite_mapTheory.FLOOKUP_UPDATE, is_terminator_def]) >>
  simp[Once exec_block_def, get_instruction_def, step_inst_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[exec_alloca_def, eval_operand_def, update_var_def, is_terminator_def] >>
  simp[Once exec_block_def, get_instruction_def, step_inst_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[eval_operand_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, is_terminator_def] >>
  Cases_on `FLOOKUP s.vs_labels "runtime_begin"` >> simp[] >>
  qmatch_goalsub_abbrev_tac `write_memory_with_expansion off bytes ast` >>
  simp[write_memory_with_expansion_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac `ast with <|vs_memory := mem; vs_inst_idx := 2|>` >>
  simp[Abbr `ast`, Once run_block_non_phis_def, get_instruction_def,
       step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[eval_operand_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, is_terminator_def]
QED

Theorem deploy_no_ctor_run_mem_safe:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   exts ints fb fn lbl.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    (!marks. ~deploy_source_exempt tops
               (load_contract NONE (gas_explicit marks vs.vs_gas_readings) am tx
                  [(NONE, tops)] [])) /\
    classify_functions tops = (exts, ints, fb, NONE) /\
    lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl
    ==>
    !fuel. mem_safe_blocks fuel dunit.cu_context fn
             (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                         vs_inst_idx := 0 |>)
Proof
  rpt strip_tac >>
  drule_all deploy_no_ctor_entry_shape >> strip_tac >> gvs[] >>
  `vs.vs_allocas = (deploy_entry_state prog cplan tops es).vs_allocas` by
    (fs[gas_variant_def] >>
     qpat_x_assum `deploy_entry_state _ _ _ _ = _`
       (mp_tac o Q.AP_TERM `\x. x.vs_allocas`) >> simp[]) >>
  irule simple_deploy_entry_mem_safe >>
  simp[deploy_entry_state_def, entry_venom_state_def, init_venom_state_def]
QED
