(* A piece of deploy_unit_execution_correct (ctorDeployLowering).
   ADMITTED until proved. *)
Theory ctorDeployLoweringNoCtor
Ancestors
  structFieldsProps ctorDeployLoweringDefs ctorDeployImmBudget o1PassContract gasSummary
  compileVyper vyperInterpreter e2eDeployDefs moduleLowering
  immutableDeployExecution ctorDeployDefs e2eEntry venomState vyperCompiler
  immutableEncoding immutableEncodingProofs immutableSectionRel immutableValue
  valueEncoding valueEncodingDefs vyperValue vyperTypeInitialState vyperTypeContractStaticMaps
  vyperTypeConstantCells abiCallerBuiltinInput entryStateRel
  venomPipelineData venomPipelineDriver venomPipelineRunner venomFnScheduleRunner
  unitLabelMap fcgPruning
  fcgDefs

Theorem no_ctor_lookup:
  !tops exts ints fb.
    classify_functions tops = (exts, ints, fb, NONE) ==>
    vyperInterpreter$lookup_function NONE "__init__" Deploy tops =
      SOME (Payable, F, [], [], NoneT, [])
Proof
  Induct_on `tops` >- simp[classify_functions_def, lookup_function_def] >>
  qabbrev_tac `acc = classify_functions tops` >>
  PairCases_on `acc` >>
  Cases_on `h` >>
  fs[classify_functions_def, classify_function_def, lookup_function_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  simp[Once (oneline lookup_function_def)] >>
  Cases_on `v` >> simp[]
QED

Theorem no_ctor_args:
  classify_functions tops = (exts, ints, fb, NONE) /\
  constructor_args_encode tops tx bs ==>
  tx.args = [] /\ bs = []
Proof
  strip_tac >> drule no_ctor_lookup >> strip_tac >>
  gvs[constructor_args_encode_def] >> EVAL_TAC
QED

Theorem no_ctor_simple_epilogue:
  compile_simple_deploy rt imm =
    compile_constructor_epilogue (rt + imm) 0 (Lit 0w)
Proof
  simp[compile_simple_deploy_def, compile_constructor_epilogue_def]
QED

Theorem no_ctor_simple_insts:
  compile_simple_deploy rt imm st = ((), st') ==>
  emitted_insts st st' =
    [mk_inst st.cs_next_id ALLOCA [Lit (n2w (rt + imm))]
       ["%" ++ toString st.cs_next_var];
     mk_inst (st.cs_next_id + 1) CODECOPY
       [Var ("%" ++ toString st.cs_next_var); Label "runtime_begin";
        Lit (n2w (rt + imm))] [];
     mk_inst (st.cs_next_id + 2) RETURN
       [Var ("%" ++ toString st.cs_next_var); Lit (n2w (rt + imm))] []]
Proof
  rewrite_tac[no_ctor_simple_epilogue] >>
  strip_tac >> drule compile_constructor_epilogue_zero_insts >> simp[]
QED

Theorem no_ctor_entry_code:
  deploy_state_rel tops deploy_bc am tx es /\
  classify_functions tops = (exts, ints, fb, NONE) /\
  gas_variant vs (deploy_entry_state prog cplan tops es) ==>
  vs.vs_code = deploy_bc /\
  vs.vs_labels = n2w o_f SND (compute_label_offsets prog)
Proof
  strip_tac >>
  qpat_x_assum `deploy_state_rel _ _ _ _ _` mp_tac >>
  simp[deploy_state_rel_def] >> strip_tac >>
  drule_all no_ctor_args >> strip_tac >>
  qpat_x_assum `gas_variant _ _` (mp_tac o SRULE [gas_variant_def]) >>
  disch_then (mp_tac o Q.AP_TERM `\s. (s.vs_code, s.vs_labels)`) >>
  simp[deploy_entry_state_def, entry_venom_state_def]
QED

Theorem no_ctor_simple_data:
  compile_simple_deploy rt imm st = ((), st') ==>
  st'.cs_data_sections = st.cs_data_sections
Proof
  simp[compile_simple_deploy_def, contextTheory.compile_alloc_buffer_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       emitHelperTheory.emit_inst_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.comp_return_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.emit_def] >> strip_tac >> gvs[]
QED

Theorem no_ctor_lowering_data:
  run_deploy_lowering F rpolicy bytes imm args sz [] cenv stmts pay nr
    nkey ut label = SOME unit ==>
  unit.cu_data_segment =
    [<| ds_label := "runtime_begin"; ds_items := [DataBytes bytes] |>]
Proof
  simp[run_deploy_lowering_def, compile_generate_deploy_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def] >>
  pairarg_tac >> rpt strip_tac >>
  gvs[AllCaseEqs(), extract_context_with_internals_def] >>
  pairarg_tac >> gvs[] >>
  drule no_ctor_simple_data >>
  simp[initial_compile_state_def]
QED

Theorem no_ctor_unit_data:
  classify_functions tops = (exts, ints, fb, NONE) /\
  lower_vyper_deploy_unit tops rpolicy bytes = SOME unit ==>
  unit.cu_data_segment =
    [<| ds_label := "runtime_begin"; ds_items := [DataBytes bytes] |>]
Proof
  simp[lower_vyper_deploy_unit_def, set_constructor_package_target_def] >>
  rpt strip_tac >> gvs[set_constructor_package_target_def] >>
  drule no_ctor_lowering_data >> simp[]
QED

Theorem no_ctor_resolved_data[local]:
  unit.cu_data_segment =
    [<| ds_label := label; ds_items := [DataBytes bytes] |>] ==>
  (apply_resolved_unit_label_map lm unit).cu_data_segment =
    [<| ds_label := label; ds_items := [DataBytes bytes] |>]
Proof
  simp[apply_resolved_unit_label_map_def]
QED

Theorem no_ctor_label_map_data[local]:
  apply_unit_label_map lm unit = SOME unit' /\
  unit.cu_data_segment =
    [<| ds_label := label; ds_items := [DataBytes bytes] |>] ==>
  unit'.cu_data_segment =
    [<| ds_label := label; ds_items := [DataBytes bytes] |>]
Proof
  simp[apply_unit_label_map_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> irule no_ctor_resolved_data >> simp[]
QED

Theorem no_ctor_configured_data[local]:
  run_configured_fn_passes runner rpolicy passes name unit supply =
    SOME (unit',supply') /\
  unit.cu_data_segment =
    [<| ds_label := label; ds_items := [DataBytes bytes] |>] ==>
  unit'.cu_data_segment =
    [<| ds_label := label; ds_items := [DataBytes bytes] |>]
Proof
  simp[run_configured_fn_passes_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> drule no_ctor_label_map_data >> simp[]
QED

Theorem no_ctor_named_data[local]:
  !names unit supply unit' supply'.
  run_named_fn_schedules runner rpolicy passes names unit supply =
    SOME (unit',supply') /\
  unit.cu_data_segment =
    [<| ds_label := label; ds_items := [DataBytes bytes] |>] ==>
  unit'.cu_data_segment =
    [<| ds_label := label; ds_items := [DataBytes bytes] |>]
Proof
  Induct >> simp[run_named_fn_schedules_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule no_ctor_configured_data >> disch_then drule >> strip_tac >>
  first_x_assum irule >> metis_tac[]
QED

Theorem no_ctor_mapped_data[local]:
  run_mapped_functions rpolicy pass unit supply = SOME (unit',supply') /\
  unit.cu_data_segment =
    [<| ds_label := label; ds_items := [DataBytes bytes] |>] ==>
  unit'.cu_data_segment =
    [<| ds_label := label; ds_items := [DataBytes bytes] |>]
Proof
  simp[run_mapped_functions_def] >> metis_tac[no_ctor_named_data]
QED

Theorem no_ctor_callee_data[local]:
  run_callee_first rpolicy passes names unit supply = SOME (unit',supply') /\
  unit.cu_data_segment =
    [<| ds_label := label; ds_items := [DataBytes bytes] |>] ==>
  unit'.cu_data_segment =
    [<| ds_label := label; ds_items := [DataBytes bytes] |>]
Proof
  simp[run_callee_first_def] >> metis_tac[no_ctor_named_data]
QED

Theorem no_ctor_stage_data[local]:
  run_pipeline_stage rpolicy stage unit supply = SOME (unit',supply') /\
  unit.cu_data_segment =
    [<| ds_label := label; ds_items := [DataBytes bytes] |>] ==>
  unit'.cu_data_segment =
    [<| ds_label := label; ds_items := [DataBytes bytes] |>]
Proof
  Cases_on `stage` >> simp[run_pipeline_stage_def] >>
  metis_tac[no_ctor_mapped_data]
QED

Theorem no_ctor_stages_data[local]:
  !stages unit supply unit' supply'.
  run_pipeline_stages rpolicy stages unit supply = SOME (unit',supply') /\
  unit.cu_data_segment =
    [<| ds_label := label; ds_items := [DataBytes bytes] |>] ==>
  unit'.cu_data_segment =
    [<| ds_label := label; ds_items := [DataBytes bytes] |>]
Proof
  Induct >> simp[run_pipeline_stages_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule no_ctor_stage_data >> disch_then drule >> strip_tac >>
  first_x_assum irule >> metis_tac[]
QED

Theorem no_ctor_pipeline_data:
  run_venom_pipeline mem_ok calling_ok post_ok rpolicy spec unit = SOME out /\
  unit.cu_data_segment =
    [<| ds_label := label; ds_items := [DataBytes bytes] |>] ==>
  out.po_unit.cu_data_segment =
    [<| ds_label := label; ds_items := [DataBytes bytes] |>]
Proof
  simp[run_venom_pipeline_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  `pre_unit.cu_data_segment =
    [<| ds_label := label; ds_items := [DataBytes bytes] |>]` by
    metis_tac[no_ctor_stages_data] >>
  qpat_x_assum `run_callee_first _ _ _ _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `run_callee_first _ _ _ walk_unit _` >>
  `walk_unit.cu_data_segment =
    [<| ds_label := label; ds_items := [DataBytes bytes] |>]` by
    (simp[Abbr `walk_unit`] >> Cases_on `spec.ps_prune_unreachable` >>
     simp[prune_unit_fcg_unreachable_fields]) >>
  strip_tac >> drule no_ctor_callee_data >> disch_then drule >> strip_tac >>
  drule_all no_ctor_stages_data >> simp[]
QED

Theorem no_ctor_optimized_data:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  classify_functions tops = (exts, ints, fb, NONE) ==>
  dout.po_unit.cu_data_segment =
    [<| ds_label := "runtime_begin"; ds_items := [DataBytes runtime_bc] |>]
Proof
  simp[deploy_phases_def, o1PipelineCorrectTheory.o1_pipeline_def] >>
  rpt strip_tac >> drule_all no_ctor_unit_data >> strip_tac >>
  drule_all no_ctor_pipeline_data >> simp[]
QED

Theorem no_ctor_assembly_shape:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  classify_functions tops = (exts, ints, fb, NONE) ==>
  prog = execute_plan cplan.cp_initial_fmp (context_plan_ops cplan) ++
    [AsmDataHeader "runtime_begin"; AsmDataItem runtime_bc;
     AsmDataHeader "code_end"]
Proof
  strip_tac >> drule_all no_ctor_optimized_data >> strip_tac >>
  gvs[deploy_phases_def, asmIRTheory.data_segment_asm_def,
      asmIRTheory.data_section_asm_def]
QED

Theorem no_ctor_offset_fold_size[local]:
  !prefix pc (labels:string |-> num).
  FST (FOLDL (\(pc,labels) inst.
    (pc + asm_inst_size inst,
     case inst of AsmLabel lbl => labels |+ (lbl,pc)
       | AsmDataHeader lbl => labels |+ (lbl,pc) | _ => labels))
    (pc,labels) prefix) = pc + SUM (MAP asm_inst_size prefix)
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `h` >>
  simp[arithmeticTheory.ADD_ASSOC]
QED

Theorem no_ctor_compute_size[local]:
  !prefix. FST (compute_label_offsets prefix) = SUM (MAP asm_inst_size prefix)
Proof
  simp[symbolResolveTheory.compute_label_offsets_def, no_ctor_offset_fold_size]
QED

Theorem no_ctor_singleton_suffix:
  prog = prefix ++ [AsmDataHeader "runtime_begin"; AsmDataItem bytes;
                    AsmDataHeader "code_end"] /\
  off = SUM (MAP asm_inst_size prefix) /\
  LENGTH (FLAT (MAP (encode_inst (SND (compute_label_offsets prog))) prefix)) =
    off ==>
  FLOOKUP (SND (compute_label_offsets prog)) "runtime_begin" = SOME off /\
  DROP off (assemble prog) = bytes
Proof
  rpt strip_tac
  >- (gvs[] >> qpat_x_assum `LENGTH _ = _` kall_tac >>
      qspec_then `prefix` mp_tac no_ctor_compute_size >>
      Cases_on `compute_label_offsets prefix` >> simp[] >> strip_tac >>
      pure_once_rewrite_tac[symbolResolveTheory.compute_label_offsets_def] >>
      pure_rewrite_tac[rich_listTheory.FOLDL_APPEND] >>
      pure_rewrite_tac[GSYM symbolResolveTheory.compute_label_offsets_def] >>
      simp[symbolResolveTheory.asm_inst_size_def, finite_mapTheory.FLOOKUP_UPDATE])
  >> gvs[symbolResolveTheory.assemble_def, listTheory.MAP_APPEND,
         listTheory.FLAT_APPEND, symbolResolveTheory.encode_inst_def,
         rich_listTheory.DROP_APPEND] >>
  pairarg_tac >> gvs[rich_listTheory.DROP_APPEND]
QED

Theorem no_ctor_lowering_context_shape:
  run_deploy_lowering F rpolicy bytes imm args sz [] cenv stmts pay nr
    nkey ut entry = SOME unit ==>
  unit.cu_context = install_immutable_reservation imm
    (mk_venom_context
      [mk_raw_function entry
        [<| bb_label := entry; bb_instructions :=
          [mk_inst 0 ALLOCA [Lit (n2w (LENGTH bytes + imm))] ["%0"];
           mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin";
             Lit (n2w (LENGTH bytes + imm))] [];
           mk_inst 2 RETURN [Var "%0"; Lit (n2w (LENGTH bytes + imm))] []] |>]]
      (SOME entry))
Proof
  simp[run_deploy_lowering_def, compile_generate_deploy_def,
       compile_simple_deploy_def, contextTheory.compile_alloc_buffer_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       emitHelperTheory.emit_inst_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.comp_return_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.emit_def, initial_compile_state_def,
       extract_context_with_internals_def, package_internal_blocks_def,
       internal_fn_descriptors_def] >>
  rpt strip_tac >> gvs[] >>
  `toString (0:num) = "0"` by (EVAL_TAC >> simp[]) >> simp[]
QED

Theorem no_ctor_deploy_context_shape:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  classify_functions tops = (exts, ints, fb, NONE) ==>
  dunit.cu_context = install_immutable_reservation (imm_len tops)
    (mk_venom_context
      [mk_raw_function "__deploy"
        [<| bb_label := "__deploy"; bb_instructions :=
          [mk_inst 0 ALLOCA [Lit (n2w (LENGTH runtime_bc + imm_len tops))] ["%0"];
           mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin";
             Lit (n2w (LENGTH runtime_bc + imm_len tops))] [];
           mk_inst 2 RETURN
             [Var "%0"; Lit (n2w (LENGTH runtime_bc + imm_len tops))] []] |>]]
      (SOME "__deploy"))
Proof
  simp[deploy_phases_def, lower_vyper_deploy_unit_def,
       set_constructor_package_target_def] >> rpt strip_tac >>
  gvs[set_constructor_package_target_def] >>
  drule no_ctor_lowering_context_shape >> simp[imm_len_def]
QED

Theorem no_ctor_simplify_cfg:
  simplifyCfgDefs$simplify_cfg_fn_with_labels
    (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 0 ALLOCA [Lit n] ["%0"];
         mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit n] [];
         mk_inst 2 RETURN [Var "%0"; Lit n] []] |>]) =
  (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 0 ALLOCA [Lit n] ["%0"];
         mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit n] [];
         mk_inst 2 RETURN [Var "%0"; Lit n] []] |>], [])
Proof
  EVAL_TAC
QED

Theorem no_ctor_dret_desugar:
  dretDesugarDefs$dret_desugar_function target s
    (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 0 ALLOCA [Lit n] ["%0"];
         mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit n] [];
         mk_inst 2 RETURN [Var "%0"; Lit n] []] |>]) =
  SOME (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 0 ALLOCA [Lit n] ["%0"];
         mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit n] [];
         mk_inst 2 RETURN [Var "%0"; Lit n] []] |>], s)
Proof
  EVAL_TAC
QED

Theorem no_ctor_lower_dload:
  lowerDloadDefs$lower_dload_function_supply s
    (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 0 ALLOCA [Lit n] ["%0"];
         mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit n] [];
         mk_inst 2 RETURN [Var "%0"; Lit n] []] |>]) =
  (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 0 ALLOCA [Lit n] ["%0"];
         mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit n] [];
         mk_inst 2 RETURN [Var "%0"; Lit n] []] |>], s)
Proof
  EVAL_TAC
QED

Theorem no_ctor_make_ssa:
  makeSsaDefs$make_ssa_current_fn s
    (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 0 ALLOCA [Lit n] ["%0"];
         mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit n] [];
         mk_inst 2 RETURN [Var "%0"; Lit n] []] |>]) =
  (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 0 ALLOCA [Lit n] ["%0"];
         mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit n] [];
         mk_inst 2 RETURN [Var "%0"; Lit n] []] |>], s)
Proof
  EVAL_TAC
QED

Theorem no_ctor_concretize_zero:
  concretizeMemLocDefs$concretize_function_fuel_in_context fuel ctx []
    (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 0 ALLOCA [Lit n] ["%0"];
         mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit n] [];
         mk_inst 2 RETURN [Var "%0"; Lit n] []] |>]) =
  SOME ((mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 0 ASSIGN [Lit 0w] ["%0"];
         mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit n] [];
         mk_inst 2 RETURN [Var "%0"; Lit n] []] |>]) with
    <| fn_eom := SOME (w2n n); fn_mems_used := [(Allocation 0,0,w2n n)] |>)
Proof
  EVAL_TAC >> simp[wordsTheory.w2n_lt, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem no_ctor_concretize_reserved:
  0 < m /\ 0 < w2n n /\ m + w2n n < dimword(:256) ==>
  concretizeMemLocDefs$concretize_function_fuel_in_context fuel ctx [(0,m)]
    (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 0 ALLOCA [Lit n] ["%0"];
         mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit n] [];
         mk_inst 2 RETURN [Var "%0"; Lit n] []] |>]) =
  SOME ((mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 0 ASSIGN [Lit (n2w m)] ["%0"];
         mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit n] [];
         mk_inst 2 RETURN [Var "%0"; Lit n] []] |>]) with
    <| fn_eom := SOME (m + w2n n); fn_mems_used := [(Allocation 0,m,w2n n)] |>)
Proof
  strip_tac >> `n <> 0w` by (strip_tac >> gvs[]) >> EVAL_TAC >>
  simp[wordsTheory.w2n_lt, finite_mapTheory.FLOOKUP_UPDATE,
       concretizeMemLocDefsTheory.sort_reserved_by_pos_def,
       concretizeMemLocDefsTheory.insert_reserved_by_pos_def,
       concretizeMemLocDefsTheory.checked_first_fit_scan_def,
       arithmeticTheory.MAX_DEF]
QED

Theorem no_ctor_fmp_lower:
  fn = (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 0 ASSIGN [Lit (n2w p)] ["%0"];
         mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit n] [];
         mk_inst 2 RETURN [Var "%0"; Lit n] []] |>]) with
    <| fn_eom := SOME e; fn_mems_used := [(Allocation 0,p,w2n n)] |> ==>
  fmpLowerDefs$fmp_lower_function
    ((mk_venom_context [fn] (SOME "__deploy")) with
      ctx_global_reserved := reserved) s fn =
  SOME (fn with fn_fmp_signature := SOME
    <| fms_has_fmp_param := F; fms_publishes := F |>, s)
Proof
  strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem no_ctor_empty_label_map:
  apply_unit_label_map [] unit = SOME unit
Proof
  `cfgTransform$subst_label_map_op [] = I` by
    (simp[FUN_EQ_THM] >> Cases >>
     simp[cfgTransformTheory.subst_label_map_op_def]) >>
  `cfgTransform$subst_label_map_inst [] = I` by
    simp[FUN_EQ_THM, cfgTransformTheory.subst_label_map_inst_def] >>
  `cfgTransform$subst_label_map_block [] = I` by
    simp[FUN_EQ_THM, cfgTransformTheory.subst_label_map_block_def] >>
  `cfgTransform$subst_label_map_fn [] = I` by
    simp[FUN_EQ_THM, cfgTransformTheory.subst_label_map_fn_def] >>
  `map_unit_data_item [] = I` by
    (simp[FUN_EQ_THM] >> Cases >> simp[map_unit_data_item_def]) >>
  `map_unit_data_section [] = I` by
    simp[FUN_EQ_THM, map_unit_data_section_def] >>
  simp[apply_unit_label_map_def, resolve_label_map_def,
       resolve_label_entries_def, resolved_label_endpoints_valid_def,
       apply_resolved_unit_label_map_def,
       venomCompilerTypesTheory.compilation_unit_component_equality]
QED

Theorem no_ctor_identity_pass:
  unit.cu_context.ctx_functions = [fn] /\
  execute_configured_fn_pass rpolicy pass unit s fn =
    SOME <| fpo_function := fn; fpo_label_map := []; fpo_supply := s |> /\
  run_configured_fn_passes execute_configured_fn_pass rpolicy [pass]
    fn.fn_name unit s = SOME (unit',s') ==>
  unit' = unit /\ s' = s
Proof
  strip_tac >>
  `unit_with_current_fn unit fn = SOME unit` by
    (simp[unit_with_current_fn_def, replace_unique_function_def,
          venomCompilerTypesTheory.compilation_unit_component_equality,
          venomInstTheory.venom_context_component_equality]) >>
  gvs[run_configured_fn_passes_def, lookup_unique_function_def,
      run_configured_fn_pass_fold_def, replace_unique_function_def,
      no_ctor_empty_label_map, AllCaseEqs(),
      venomCompilerTypesTheory.compilation_unit_component_equality,
      venomInstTheory.venom_context_component_equality]
QED

Theorem no_ctor_identity_mapped:
  unit.cu_context.ctx_functions = [fn] /\
  execute_configured_fn_pass rpolicy pass unit s fn =
    SOME <| fpo_function := fn; fpo_label_map := []; fpo_supply := s |> /\
  run_mapped_functions rpolicy pass unit s = SOME (unit',s') ==>
  unit' = unit /\ s' = s
Proof
  simp[run_mapped_functions_def, venomInstTheory.ctx_fn_names_def,
       run_named_fn_schedules_def] >> strip_tac >>
  gvs[run_named_fn_schedules_def, AllCaseEqs()] >>
  drule_all no_ctor_identity_pass >> simp[]
QED

Theorem no_ctor_prewalk:
  fn = mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 0 ALLOCA [Lit n] ["%0"];
         mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit n] [];
         mk_inst 2 RETURN [Var "%0"; Lit n] []] |>] /\
  unit.cu_context.ctx_functions = [fn] /\
  run_pipeline_stages rpolicy
    [PS_MapFunctions (CFP_Simple VP_SimplifyCFG);
     PS_MapFunctions (CFP_Simple VP_DretDesugar); PS_DiscardAnalyses]
    unit s = SOME (unit',s') ==>
  unit' = unit /\ s' = s
Proof
  strip_tac >>
  `execute_configured_fn_pass rpolicy (CFP_Simple VP_SimplifyCFG) unit s fn =
    SOME <| fpo_function := fn; fpo_label_map := []; fpo_supply := s |>` by
    simp[no_ctor_simplify_cfg] >>
  `execute_configured_fn_pass rpolicy (CFP_Simple VP_DretDesugar) unit s fn =
    SOME <| fpo_function := fn; fpo_label_map := []; fpo_supply := s |>` by
    simp[no_ctor_dret_desugar] >>
  gvs[run_pipeline_stages_def, run_pipeline_stage_def, AllCaseEqs(),
      Excl "execute_configured_fn_pass_simplify_cfg",
      Excl "execute_configured_fn_pass_dret"] >>
  drule_all no_ctor_identity_mapped >> strip_tac >>
  gvs[Excl "execute_configured_fn_pass_simplify_cfg",
      Excl "execute_configured_fn_pass_dret"] >>
  drule_all no_ctor_identity_mapped >> simp[]
QED

Theorem no_ctor_frozen_call_order:
  fn = mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 0 ALLOCA [Lit n] ["%0"];
         mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit n] [];
         mk_inst 2 RETURN [Var "%0"; Lit n] []] |>] /\
  ctx = (mk_venom_context [fn] (SOME "__deploy")) with
    ctx_global_reserved := reserved ==>
  fcg_postorder (fcg_analyze ctx) "__deploy" = ["__deploy"] /\
  fcg_is_reachable (fcg_analyze ctx) "__deploy"
Proof
  strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem no_ctor_pruned_unit:
  unit.cu_context.ctx_functions = [fn] /\
  fcg_is_reachable fcg fn.fn_name ==>
  prune_unit_fcg_unreachable unit fcg = unit
Proof
  strip_tac >>
  simp[prune_unit_fcg_unreachable_def,
       venomCompilerTypesTheory.compilation_unit_component_equality,
       venomInstTheory.venom_context_component_equality]
QED

Theorem no_ctor_fold_step:
  unit_with_current_fn unit fn = SOME observed /\
  execute_configured_fn_pass rpolicy pass observed s fn = SOME out /\
  run_configured_fn_pass_fold execute_configured_fn_pass rpolicy
    (pass::passes) unit s fn labels = SOME result ==>
  run_configured_fn_pass_fold execute_configured_fn_pass rpolicy
    passes unit out.fpo_supply out.fpo_function
    (labels ++ out.fpo_label_map) = SOME result
Proof
  simp[Once run_configured_fn_pass_fold_def] >> strip_tac >>
  gvs[AllCaseEqs()]
QED

Theorem no_ctor_observed_function:
  unit.cu_context.ctx_functions = [fn] /\ replacement.fn_name = fn.fn_name ==>
  unit_with_current_fn unit replacement = SOME
    (unit with cu_context := unit.cu_context with ctx_functions := [replacement])
Proof
  simp[unit_with_current_fn_def, replace_unique_function_def]
QED

Theorem no_ctor_early_fold:
  raw = mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 0 ALLOCA [Lit n] ["%0"];
         mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit n] [];
         mk_inst 2 RETURN [Var "%0"; Lit n] []] |>] /\
  fixed = (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 0 ASSIGN [Lit (n2w m)] ["%0"];
         mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit n] [];
         mk_inst 2 RETURN [Var "%0"; Lit n] []] |>]) with
    <| fn_eom := SOME (m + w2n n); fn_mems_used := [(Allocation 0,m,w2n n)] |> /\
  unit.cu_context = (mk_venom_context [raw] (SOME "__deploy")) with
    ctx_global_reserved := (if m = 0 then [] else [(0,m)]) /\
  (m = 0 \/ 0 < w2n n) /\ m + w2n n < dimword(:256) /\
  run_configured_fn_pass_fold execute_configured_fn_pass rpolicy
    [CFP_Simple VP_MakeSSA; CFP_Simple VP_LowerDload;
     CFP_Simple VP_ConcretizeMemLoc; CFP_Simple VP_FmpLowering]
    unit s raw [] = SOME (fn',labels,s') ==>
  fn' = fixed with fn_fmp_signature := SOME
    <| fms_has_fmp_param := F; fms_publishes := F |> /\
  labels = [] /\
  s' = (if MEM "code_end" s.irs_used_labels then s
        else s with irs_used_labels := "code_end"::s.irs_used_labels)
Proof
  strip_tac >>
  `unit.cu_context.ctx_functions = [raw]` by
    simp[venomInstTheory.mk_venom_context_def] >>
  `unit_with_current_fn unit raw = SOME unit` by
    simp[unit_with_current_fn_def, replace_unique_function_def,
         venomCompilerTypesTheory.compilation_unit_component_equality,
         venomInstTheory.venom_context_component_equality] >>
  `execute_configured_fn_pass rpolicy (CFP_Simple VP_MakeSSA) unit s raw =
    SOME <| fpo_function := raw; fpo_label_map := []; fpo_supply := s |>` by
    simp[no_ctor_make_ssa] >>
  drule_all no_ctor_fold_step >> simp[NoAsms] >> disch_tac >>
  qpat_x_assum `run_configured_fn_pass_fold _ _ (CFP_Simple VP_MakeSSA::_) _ _ _ _ = _` kall_tac >>
  qabbrev_tac `s1 = if MEM "code_end" s.irs_used_labels then s
    else s with irs_used_labels := "code_end"::s.irs_used_labels` >>
  `execute_configured_fn_pass rpolicy (CFP_Simple VP_LowerDload) unit s raw =
    SOME <| fpo_function := raw; fpo_label_map := []; fpo_supply := s1 |>` by
    simp[no_ctor_lower_dload, Abbr `s1`] >>
  drule_all no_ctor_fold_step >> simp[NoAsms] >> disch_tac >>
  qpat_x_assum `run_configured_fn_pass_fold _ _ (CFP_Simple VP_LowerDload::_) _ _ _ _ = _` kall_tac >>
  `execute_configured_fn_pass rpolicy (CFP_Simple VP_ConcretizeMemLoc) unit s1 raw =
    SOME <| fpo_function := fixed; fpo_label_map := []; fpo_supply := s1 |>` by
    (Cases_on `m = 0` >>
     simp[no_ctor_concretize_zero, no_ctor_concretize_reserved,
          venomInstTheory.mk_venom_context_def]) >>
  drule_all no_ctor_fold_step >> simp[NoAsms] >> disch_tac >>
  qpat_x_assum `run_configured_fn_pass_fold _ _ (CFP_Simple VP_ConcretizeMemLoc::_) _ _ _ _ = _` kall_tac >>
  qabbrev_tac `observed = unit with cu_context :=
    unit.cu_context with ctx_functions := [fixed]` >>
  `unit_with_current_fn unit fixed = SOME observed` by
    (simp[unit_with_current_fn_def, replace_unique_function_def,
          venomInstTheory.mk_raw_function_def, Abbr `observed`]) >>
  `observed.cu_context = (mk_venom_context [fixed] (SOME "__deploy")) with
     ctx_global_reserved := (if m = 0 then [] else [(0,m)])` by
    simp[Abbr `observed`, venomInstTheory.mk_venom_context_def] >>
  `execute_configured_fn_pass rpolicy (CFP_Simple VP_FmpLowering) observed s1 fixed =
    SOME <| fpo_function := fixed with fn_fmp_signature := SOME
      <| fms_has_fmp_param := F; fms_publishes := F |>;
      fpo_label_map := []; fpo_supply := s1 |>` by
    (drule no_ctor_fmp_lower >>
     disch_then (qspecl_then [`s1`, `if m = 0 then [] else [(0,m)]`] mp_tac) >>
     simp[Excl "execute_configured_fn_pass_make_ssa"]) >>
  drule_all no_ctor_fold_step >>
  simp[NoAsms, run_configured_fn_pass_fold_def] >> strip_tac >> simp[]
QED

Theorem no_ctor_late_make_ssa:
  fn = (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 0 ASSIGN [Lit p] ["%0"];
         mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit n] [];
         mk_inst 2 RETURN [Var "%0"; Lit n] []] |>]) with
    <| fn_eom := SOME e; fn_mems_used := mems;
       fn_fmp_signature := SOME
         <| fms_has_fmp_param := F; fms_publishes := F |> |> ==>
  makeSsaDefs$make_ssa_current_fn s fn = (fn,s)
Proof
  strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem no_ctor_late_simplify_cfg:
  fn = (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 0 ASSIGN [Lit p] ["%0"];
         mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit n] [];
         mk_inst 2 RETURN [Var "%0"; Lit n] []] |>]) with
    <| fn_eom := SOME e; fn_mems_used := mems;
       fn_fmp_signature := SOME
         <| fms_has_fmp_param := F; fms_publishes := F |> |> ==>
  simplifyCfgDefs$simplify_cfg_fn_with_labels fn = (fn,[])
Proof
  strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem no_ctor_late_sue:
  fn = (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 0 ASSIGN [Lit p] ["%0"];
         mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit n] [];
         mk_inst 2 RETURN [Var "%0"; Lit n] []] |>]) with
    <| fn_eom := SOME e; fn_mems_used := mems;
       fn_fmp_signature := SOME
         <| fms_has_fmp_param := F; fms_publishes := F |> |> /\
  singleUseExpansionDefs$sue_alloc_assign_supply s (Lit n) = (a1,v1,s1) /\
  singleUseExpansionDefs$sue_alloc_assign_supply s1 (Var "%0") = (a2,v2,s2) /\
  singleUseExpansionDefs$sue_alloc_assign_supply s2 (Lit n) = (a3,v3,s3) /\
  singleUseExpansionDefs$sue_alloc_assign_supply s3 (Var "%0") = (a4,v4,s4) ==>
  singleUseExpansionDefs$sue_expand_function_supply s fn =
    (fn with fn_blocks :=
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 0 ASSIGN [Lit p] ["%0"];
         a2; a1; mk_inst 1 CODECOPY [v2; Label "runtime_begin"; v1] [];
         a4; a3; mk_inst 2 RETURN [v4; v3] []] |>], s4)
Proof
  strip_tac >>
  qpat_x_assum `fn = _` SUBST_ALL_TAC >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``singleUseExpansionDefs$sue_alloc_assign_supply``]) >>
  simp[]
QED

Theorem no_ctor_sue_four_allocations:
  s.irs_next_var = 0 /\ s.irs_used_vars = ["%0"; "%0"; "%0"] ==>
  let (a1,v1,s1) = singleUseExpansionDefs$sue_alloc_assign_supply s (Lit n) in
  let (a2,v2,s2) = singleUseExpansionDefs$sue_alloc_assign_supply s1 (Var "%0") in
  let (a3,v3,s3) = singleUseExpansionDefs$sue_alloc_assign_supply s2 (Lit n) in
  let (a4,v4,s4) = singleUseExpansionDefs$sue_alloc_assign_supply s3 (Var "%0") in
    a1 = mk_inst s.irs_next_inst ASSIGN [Lit n] ["formal_var_0"] /\
    a2 = mk_inst (SUC s.irs_next_inst) ASSIGN [Var "%0"] ["formal_var_1"] /\
    a3 = mk_inst (SUC (SUC s.irs_next_inst)) ASSIGN [Lit n] ["formal_var_2"] /\
    a4 = mk_inst (SUC (SUC (SUC s.irs_next_inst))) ASSIGN [Var "%0"] ["formal_var_3"] /\
    v1 = Var "formal_var_0" /\ v2 = Var "formal_var_1" /\
    v3 = Var "formal_var_2" /\ v4 = Var "formal_var_3" /\
    s4 = s with <| irs_next_var := 4;
      irs_used_vars := ["formal_var_3"; "formal_var_2"; "formal_var_1";
                        "formal_var_0"; "%0"; "%0"; "%0"];
      irs_next_inst := SUC (SUC (SUC (SUC s.irs_next_inst)));
      irs_used_inst_ids := SUC (SUC (SUC s.irs_next_inst)) ::
        SUC (SUC s.irs_next_inst) :: SUC s.irs_next_inst ::
        s.irs_next_inst :: s.irs_used_inst_ids |>
Proof
  strip_tac >>
  simp[singleUseExpansionDefsTheory.sue_alloc_assign_supply_def,
       irSupplyTheory.fresh_ir_var_def, irSupplyTheory.fresh_inst_id_def] >>
  EVAL_TAC
QED

Theorem no_ctor_late_dft:
  fn = (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 0 ASSIGN [Lit p] ["%0"];
         mk_inst 4 ASSIGN [Var "%0"] ["formal_var_1"];
         mk_inst 3 ASSIGN [Lit n] ["formal_var_0"];
         mk_inst 1 CODECOPY [Var "formal_var_1"; Label "runtime_begin";
                             Var "formal_var_0"] [];
         mk_inst 6 ASSIGN [Var "%0"] ["formal_var_3"];
         mk_inst 5 ASSIGN [Lit n] ["formal_var_2"];
         mk_inst 2 RETURN [Var "formal_var_3"; Var "formal_var_2"] []] |>]) with
    <| fn_eom := SOME e; fn_mems_used := mems;
       fn_fmp_signature := SOME
         <| fms_has_fmp_param := F; fms_publishes := F |> |> ==>
  dftDefs$dft_fn fn = fn with fn_blocks :=
    [<| bb_label := "__deploy"; bb_instructions :=
      [mk_inst 3 ASSIGN [Lit n] ["formal_var_0"];
       mk_inst 0 ASSIGN [Lit p] ["%0"];
       mk_inst 4 ASSIGN [Var "%0"] ["formal_var_1"];
       mk_inst 1 CODECOPY [Var "formal_var_1"; Label "runtime_begin";
                           Var "formal_var_0"] [];
       mk_inst 5 ASSIGN [Lit n] ["formal_var_2"];
       mk_inst 6 ASSIGN [Var "%0"] ["formal_var_3"];
       mk_inst 2 RETURN [Var "formal_var_3"; Var "formal_var_2"] []] |>]
Proof
  strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem no_ctor_late_cfg_norm:
  fn = (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 3 ASSIGN [Lit n] ["formal_var_0"];
         mk_inst 0 ASSIGN [Lit p] ["%0"];
         mk_inst 4 ASSIGN [Var "%0"] ["formal_var_1"];
         mk_inst 1 CODECOPY [Var "formal_var_1"; Label "runtime_begin";
                             Var "formal_var_0"] [];
         mk_inst 5 ASSIGN [Lit n] ["formal_var_2"];
         mk_inst 6 ASSIGN [Var "%0"] ["formal_var_3"];
         mk_inst 2 RETURN [Var "formal_var_3"; Var "formal_var_2"] []] |>]) with
    <| fn_eom := SOME e; fn_mems_used := mems;
       fn_fmp_signature := SOME
         <| fms_has_fmp_param := F; fms_publishes := F |> |> ==>
  cfgNormDefs$cfg_norm_function_supply s fn = (fn,s)
Proof
  strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem no_ctor_singleton_reorder:
  ps.ps_stack = [Lit n] /\ ps.ps_spilled = FEMPTY ==>
  stackPlanOps$reorder_plan dfg [Lit n] ps = ([],ps)
Proof
  strip_tac >>
  simp[stackPlanOpsTheory.reorder_plan_def,
       stackPlanOpsTheory.reorder_one_def,
       stackModelTheory.stack_get_unfixed_depth_def,
       stackModelTheory.stack_get_depth_def,
       stackModelTheory.stack_find_def]
QED

Theorem no_ctor_first_assign_plan:
  fn = (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 3 ASSIGN [Lit n] ["formal_var_0"];
         mk_inst 0 ASSIGN [Lit p] ["%0"];
         mk_inst 4 ASSIGN [Var "%0"] ["formal_var_1"];
         mk_inst 1 CODECOPY [Var "formal_var_1"; Label "runtime_begin";
                             Var "formal_var_0"] [];
         mk_inst 5 ASSIGN [Lit n] ["formal_var_2"];
         mk_inst 6 ASSIGN [Var "%0"] ["formal_var_3"];
         mk_inst 2 RETURN [Var "formal_var_3"; Var "formal_var_2"] []] |>]) with
    <| fn_eom := SOME e; fn_mems_used := mems;
       fn_fmp_signature := SOME
         <| fms_has_fmp_param := F; fms_publishes := F |> |> ==>
  stackPlanGen$generate_inst_plan (livenessDefs$liveness_analyze fn)
    (dfgDefs$dfg_build_function fn) (cfgDefs$cfg_analyze fn) fn
    (mk_inst 3 ASSIGN [Lit n] ["formal_var_0"])
    (livenessDefs$live_vars_at (livenessDefs$liveness_analyze fn) "__deploy" 1)
    T F "__deploy" (stackPlanGen$init_cleanup_plan_state ch growth spill 0) =
  SOME ([SOPush (Lit n)],
    (stackPlanGen$init_cleanup_plan_state ch growth spill 0) with
      ps_stack := [Var "formal_var_0"])
Proof
  strip_tac >> gvs[] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``stackPlanOps$reorder_plan``]) >>
  simp[no_ctor_singleton_reorder]
QED

Theorem no_ctor_pair_reorder:
  ps.ps_stack = [Var v; Lit n] /\ ps.ps_spilled = FEMPTY ==>
  stackPlanOps$reorder_plan dfg [Lit n] ps = ([],ps)
Proof
  strip_tac >>
  simp[stackPlanOpsTheory.reorder_plan_def,
       stackPlanOpsTheory.reorder_one_def,
       stackModelTheory.stack_get_unfixed_depth_def,
       stackModelTheory.stack_get_depth_def,
       stackModelTheory.stack_find_def]
QED

Theorem no_ctor_second_assign_plan:
  fn = (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 3 ASSIGN [Lit n] ["formal_var_0"];
         mk_inst 0 ASSIGN [Lit p] ["%0"];
         mk_inst 4 ASSIGN [Var "%0"] ["formal_var_1"];
         mk_inst 1 CODECOPY [Var "formal_var_1"; Label "runtime_begin";
                             Var "formal_var_0"] [];
         mk_inst 5 ASSIGN [Lit n] ["formal_var_2"];
         mk_inst 6 ASSIGN [Var "%0"] ["formal_var_3"];
         mk_inst 2 RETURN [Var "formal_var_3"; Var "formal_var_2"] []] |>]) with
    <| fn_eom := SOME e; fn_mems_used := mems;
       fn_fmp_signature := SOME
         <| fms_has_fmp_param := F; fms_publishes := F |> |> ==>
  stackPlanGen$generate_inst_plan (livenessDefs$liveness_analyze fn)
    (dfgDefs$dfg_build_function fn) (cfgDefs$cfg_analyze fn) fn
    (mk_inst 0 ASSIGN [Lit p] ["%0"])
    (livenessDefs$live_vars_at (livenessDefs$liveness_analyze fn) "__deploy" 2)
    T F "__deploy" ((stackPlanGen$init_cleanup_plan_state ch growth spill 0) with
      ps_stack := [Var "formal_var_0"]) =
  SOME (if p = n then
    ([SOPush (Lit p)],
     (stackPlanGen$init_cleanup_plan_state ch growth spill 0) with
       ps_stack := [Var "formal_var_0"; Var "%0"])
    else
    ([SOPush (Lit p); SOSwap 1],
     (stackPlanGen$init_cleanup_plan_state ch growth spill 0) with
       ps_stack := [Var "%0"; Var "formal_var_0"]))
Proof
  strip_tac >> gvs[] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``stackPlanOps$reorder_plan``]) >>
  simp[no_ctor_pair_reorder] >>
  Cases_on `p = n` >> simp[] >> EVAL_TAC >> simp[]
QED

Theorem no_ctor_dup_reorder:
  ps.ps_stack = [a; b; Var v] /\ ps.ps_spilled = FEMPTY ==>
  stackPlanOps$reorder_plan dfg [Var v] ps = ([],ps)
Proof
  strip_tac >>
  simp[stackPlanOpsTheory.reorder_plan_def,
       stackPlanOpsTheory.reorder_one_def,
       stackModelTheory.stack_get_unfixed_depth_def,
       stackModelTheory.stack_get_depth_def,
       stackModelTheory.stack_find_def]
QED

Theorem no_ctor_third_assign_plan:
  fn = (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 3 ASSIGN [Lit n] ["formal_var_0"];
         mk_inst 0 ASSIGN [Lit p] ["%0"];
         mk_inst 4 ASSIGN [Var "%0"] ["formal_var_1"];
         mk_inst 1 CODECOPY [Var "formal_var_1"; Label "runtime_begin";
                             Var "formal_var_0"] [];
         mk_inst 5 ASSIGN [Lit n] ["formal_var_2"];
         mk_inst 6 ASSIGN [Var "%0"] ["formal_var_3"];
         mk_inst 2 RETURN [Var "formal_var_3"; Var "formal_var_2"] []] |>]) with
    <| fn_eom := SOME e; fn_mems_used := mems;
       fn_fmp_signature := SOME
         <| fms_has_fmp_param := F; fms_publishes := F |> |> ==>
  stackPlanGen$generate_inst_plan (livenessDefs$liveness_analyze fn)
    (dfgDefs$dfg_build_function fn) (cfgDefs$cfg_analyze fn) fn
    (mk_inst 4 ASSIGN [Var "%0"] ["formal_var_1"])
    (livenessDefs$live_vars_at (livenessDefs$liveness_analyze fn) "__deploy" 3)
    T F "__deploy" ((stackPlanGen$init_cleanup_plan_state ch growth spill 0) with
      ps_stack := (if p = n then [Var "formal_var_0"; Var "%0"]
                   else [Var "%0"; Var "formal_var_0"])) =
  SOME ([SODup (if p = n then 1 else 2)],
    (stackPlanGen$init_cleanup_plan_state ch growth spill 0) with
      ps_stack := (if p = n then
        [Var "formal_var_0"; Var "%0"; Var "formal_var_1"]
        else [Var "%0"; Var "formal_var_0"; Var "formal_var_1"]))
Proof
  strip_tac >> gvs[] >>
  Cases_on `p = n` >> simp[] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``stackPlanOps$reorder_plan``]) >>
  simp[no_ctor_dup_reorder] >> EVAL_TAC >> simp[]
QED

Theorem no_ctor_reorder_three:
  stackPlanOps$reorder_plan dfg [a;b;c] ps =
  let (ops0,ps0) = stackPlanOps$reorder_one dfg [a;b;c] 0 a ps in
  let (ops1,ps1) = stackPlanOps$reorder_one dfg [a;b;c] 1 b ps0 in
  let (ops2,ps2) = stackPlanOps$reorder_one dfg [a;b;c] 2 c ps1 in
  (ops0 ++ ops1 ++ ops2,ps2)
Proof
  Cases_on `stackPlanOps$reorder_one dfg [a;b;c] 0 a ps` >>
  rename1 `_ = (ops0,ps0)` >>
  Cases_on `stackPlanOps$reorder_one dfg [a;b;c] 1 b ps0` >>
  rename1 `_ = (ops1,ps1)` >>
  Cases_on `stackPlanOps$reorder_one dfg [a;b;c] 2 c ps1` >>
  simp[stackPlanOpsTheory.reorder_plan_def]
QED

Theorem no_ctor_codecopy_reorder_first_equal:
  ps.ps_stack = [Var "formal_var_0"; Var "%0"; Var "formal_var_1";
                  Label "runtime_begin"] /\ ps.ps_spilled = FEMPTY /\
  dfgDefs$operand_equiv dfg (Var "formal_var_0") (Var "%0") ==>
  stackPlanOps$reorder_one dfg
    [Var "formal_var_0"; Label "runtime_begin"; Var "formal_var_1"]
    0 (Var "formal_var_0") ps =
  ([], ps with ps_stack := [Var "%0"; Var "formal_var_0";
                            Var "formal_var_1"; Label "runtime_begin"])
Proof
  strip_tac >>
  simp[stackPlanOpsTheory.reorder_one_def,
       stackModelTheory.stack_get_unfixed_depth_def,
       stackModelTheory.stack_get_depth_def,
       stackModelTheory.stack_find_def,
       stackModelTheory.stack_peek_def,
       stackModelTheory.stack_poke_def] >> EVAL_TAC
QED

Theorem no_ctor_codecopy_reorder_first_distinct:
  ps.ps_stack = [Var "%0"; Var "formal_var_0"; Var "formal_var_1";
                  Label "runtime_begin"] /\ ps.ps_spilled = FEMPTY ==>
  stackPlanOps$reorder_one dfg
    [Var "formal_var_0"; Label "runtime_begin"; Var "formal_var_1"]
    0 (Var "formal_var_0") ps = ([],ps)
Proof
  strip_tac >>
  simp[stackPlanOpsTheory.reorder_one_def,
       stackModelTheory.stack_get_unfixed_depth_def,
       stackModelTheory.stack_get_depth_def,
       stackModelTheory.stack_find_def]
QED

Theorem no_ctor_codecopy_label_depth:
  stackModel$stack_get_unfixed_depth (Label "runtime_begin") 1 3
    [Var "%0"; Var "formal_var_0"; Var "formal_var_1"; Label "runtime_begin"] = SOME 0
Proof
  simp[stackModelTheory.stack_get_unfixed_depth_def,
       stackModelTheory.stack_peek_def, listTheory.FIND_thm]
QED

Theorem no_ctor_codecopy_reorder_second:
  ps.ps_stack = [Var "%0"; Var "formal_var_0"; Var "formal_var_1";
                  Label "runtime_begin"] /\ ps.ps_spilled = FEMPTY /\
  ~dfgDefs$operand_equiv dfg (Label "runtime_begin") (Var "formal_var_1") ==>
  stackPlanOps$reorder_one dfg
    [Var "formal_var_0"; Label "runtime_begin"; Var "formal_var_1"]
    1 (Label "runtime_begin") ps =
  ([SOSwap 1], ps with ps_stack := [Var "%0"; Var "formal_var_0";
                                    Label "runtime_begin"; Var "formal_var_1"])
Proof
  strip_tac >>
  simp[stackPlanOpsTheory.reorder_one_def, no_ctor_codecopy_label_depth,
       stackModelTheory.stack_peek_def,
       stackPlanOpsTheory.do_swap_def,
       stackModelTheory.stack_swap_def] >> EVAL_TAC
QED

Theorem no_ctor_codecopy_reorder_third:
  ps.ps_stack = [Var "%0"; Var "formal_var_0"; Label "runtime_begin";
                  Var "formal_var_1"] /\ ps.ps_spilled = FEMPTY ==>
  stackPlanOps$reorder_one dfg
    [Var "formal_var_0"; Label "runtime_begin"; Var "formal_var_1"]
    2 (Var "formal_var_1") ps = ([],ps)
Proof
  strip_tac >>
  simp[stackPlanOpsTheory.reorder_one_def,
       stackModelTheory.stack_get_unfixed_depth_def,
       stackModelTheory.stack_get_depth_def,
       stackModelTheory.stack_find_def, listTheory.FIND_thm,
       stackModelTheory.stack_peek_def]
QED

Theorem no_ctor_codecopy_reorder:
  ((ps.ps_stack =
     [Var "formal_var_0"; Var "%0"; Var "formal_var_1"; Label "runtime_begin"] /\
    dfgDefs$operand_equiv dfg (Var "formal_var_0") (Var "%0")) \/
   ps.ps_stack =
     [Var "%0"; Var "formal_var_0"; Var "formal_var_1"; Label "runtime_begin"]) /\
  ps.ps_spilled = FEMPTY /\
  ~dfgDefs$operand_equiv dfg (Label "runtime_begin") (Var "formal_var_1") ==>
  stackPlanOps$reorder_plan dfg
    [Var "formal_var_0"; Label "runtime_begin"; Var "formal_var_1"] ps =
  ([SOSwap 1], ps with ps_stack := [Var "%0"; Var "formal_var_0";
                                    Label "runtime_begin"; Var "formal_var_1"])
Proof
  strip_tac >>
  simp[no_ctor_reorder_three, no_ctor_codecopy_reorder_first_equal,
       no_ctor_codecopy_reorder_first_distinct, no_ctor_codecopy_reorder_second,
       no_ctor_codecopy_reorder_third]
QED

Theorem no_ctor_codecopy_plan:
  fn = (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 3 ASSIGN [Lit n] ["formal_var_0"];
         mk_inst 0 ASSIGN [Lit p] ["%0"];
         mk_inst 4 ASSIGN [Var "%0"] ["formal_var_1"];
         mk_inst 1 CODECOPY [Var "formal_var_1"; Label "runtime_begin";
                             Var "formal_var_0"] [];
         mk_inst 5 ASSIGN [Lit n] ["formal_var_2"];
         mk_inst 6 ASSIGN [Var "%0"] ["formal_var_3"];
         mk_inst 2 RETURN [Var "formal_var_3"; Var "formal_var_2"] []] |>]) with
    <| fn_eom := SOME e; fn_mems_used := mems;
       fn_fmp_signature := SOME
         <| fms_has_fmp_param := F; fms_publishes := F |> |> ==>
  stackPlanGen$generate_inst_plan (livenessDefs$liveness_analyze fn)
    (dfgDefs$dfg_build_function fn) (cfgDefs$cfg_analyze fn) fn
    (mk_inst 1 CODECOPY [Var "formal_var_1"; Label "runtime_begin";
                         Var "formal_var_0"] [])
    (livenessDefs$live_vars_at (livenessDefs$liveness_analyze fn) "__deploy" 4)
    T F "__deploy" ((stackPlanGen$init_cleanup_plan_state ch growth spill 0) with
      ps_stack := (if p = n then
        [Var "formal_var_0"; Var "%0"; Var "formal_var_1"]
        else [Var "%0"; Var "formal_var_0"; Var "formal_var_1"])) =
  SOME ([SOPushLabel "runtime_begin"; SOSwap 1; SOEmit "CODECOPY"],
    (stackPlanGen$init_cleanup_plan_state ch growth spill 0) with
      ps_stack := [Var "%0"])
Proof
  strip_tac >> gvs[] >>
  Cases_on `p = n` >> simp[] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``stackPlanOps$reorder_plan``]) >>
  dep_rewrite.DEP_REWRITE_TAC [no_ctor_codecopy_reorder] >>
  simp[dfgDefsTheory.operand_equiv_def, dfgDefsTheory.normalize_operand_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem no_ctor_fourth_assign_plan:
  fn = (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 3 ASSIGN [Lit n] ["formal_var_0"];
         mk_inst 0 ASSIGN [Lit p] ["%0"];
         mk_inst 4 ASSIGN [Var "%0"] ["formal_var_1"];
         mk_inst 1 CODECOPY [Var "formal_var_1"; Label "runtime_begin";
                             Var "formal_var_0"] [];
         mk_inst 5 ASSIGN [Lit n] ["formal_var_2"];
         mk_inst 6 ASSIGN [Var "%0"] ["formal_var_3"];
         mk_inst 2 RETURN [Var "formal_var_3"; Var "formal_var_2"] []] |>]) with
    <| fn_eom := SOME e; fn_mems_used := mems;
       fn_fmp_signature := SOME
         <| fms_has_fmp_param := F; fms_publishes := F |> |> ==>
  stackPlanGen$generate_inst_plan (livenessDefs$liveness_analyze fn)
    (dfgDefs$dfg_build_function fn) (cfgDefs$cfg_analyze fn) fn
    (mk_inst 5 ASSIGN [Lit n] ["formal_var_2"])
    (livenessDefs$live_vars_at (livenessDefs$liveness_analyze fn) "__deploy" 5)
    T F "__deploy" ((stackPlanGen$init_cleanup_plan_state ch growth spill 0) with
      ps_stack := [Var "%0"]) =
  SOME (if p = n then
    ([SOPush (Lit n)],
     (stackPlanGen$init_cleanup_plan_state ch growth spill 0) with
       ps_stack := [Var "%0"; Var "formal_var_2"])
    else
    ([SOPush (Lit n); SOSwap 1],
     (stackPlanGen$init_cleanup_plan_state ch growth spill 0) with
       ps_stack := [Var "formal_var_2"; Var "%0"]))
Proof
  strip_tac >> gvs[] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``stackPlanOps$reorder_plan``]) >>
  simp[no_ctor_pair_reorder] >> Cases_on `p = n` >> simp[] >> EVAL_TAC >> simp[]
QED

Theorem no_ctor_final_assign_reorder:
  ((ps.ps_stack = [Var "%0"; Var "formal_var_2"] /\
    dfgDefs$operand_equiv dfg (Var "%0") (Var "formal_var_2")) \/
   ps.ps_stack = [Var "formal_var_2"; Var "%0"]) /\
  ps.ps_spilled = FEMPTY ==>
  stackPlanOps$reorder_plan dfg [Var "%0"] ps =
  ([],ps with ps_stack := [Var "formal_var_2"; Var "%0"])
Proof
  strip_tac >>
  simp[stackPlanOpsTheory.reorder_plan_def, stackPlanOpsTheory.reorder_one_def,
       stackModelTheory.stack_get_unfixed_depth_def,
       stackModelTheory.stack_get_depth_def, stackModelTheory.stack_find_def,
       stackModelTheory.stack_peek_def, stackModelTheory.stack_poke_def] >>
  EVAL_TAC >> gvs[] >> simp[stackPlanTypesTheory.plan_state_component_equality]
QED

Theorem no_ctor_fifth_assign_plan:
  fn = (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 3 ASSIGN [Lit n] ["formal_var_0"];
         mk_inst 0 ASSIGN [Lit p] ["%0"];
         mk_inst 4 ASSIGN [Var "%0"] ["formal_var_1"];
         mk_inst 1 CODECOPY [Var "formal_var_1"; Label "runtime_begin";
                             Var "formal_var_0"] [];
         mk_inst 5 ASSIGN [Lit n] ["formal_var_2"];
         mk_inst 6 ASSIGN [Var "%0"] ["formal_var_3"];
         mk_inst 2 RETURN [Var "formal_var_3"; Var "formal_var_2"] []] |>]) with
    <| fn_eom := SOME e; fn_mems_used := mems;
       fn_fmp_signature := SOME
         <| fms_has_fmp_param := F; fms_publishes := F |> |> ==>
  stackPlanGen$generate_inst_plan (livenessDefs$liveness_analyze fn)
    (dfgDefs$dfg_build_function fn) (cfgDefs$cfg_analyze fn) fn
    (mk_inst 6 ASSIGN [Var "%0"] ["formal_var_3"])
    (livenessDefs$live_vars_at (livenessDefs$liveness_analyze fn) "__deploy" 6)
    T T "__deploy" ((stackPlanGen$init_cleanup_plan_state ch growth spill 0) with
      ps_stack := (if p = n then [Var "%0"; Var "formal_var_2"]
                   else [Var "formal_var_2"; Var "%0"])) =
  SOME ([], (stackPlanGen$init_cleanup_plan_state ch growth spill 0) with
    ps_stack := [Var "formal_var_2"; Var "formal_var_3"])
Proof
  strip_tac >> gvs[] >> Cases_on `p = n` >> simp[] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``stackPlanOps$reorder_plan``]) >>
  dep_rewrite.DEP_REWRITE_TAC [no_ctor_final_assign_reorder] >>
  simp[dfgDefsTheory.operand_equiv_def, dfgDefsTheory.normalize_operand_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem no_ctor_return_reorder:
  ps.ps_stack = [Var "formal_var_2"; Var "formal_var_3"] /\
  ps.ps_spilled = FEMPTY ==>
  stackPlanOps$reorder_plan dfg [Var "formal_var_2"; Var "formal_var_3"] ps =
  ([],ps)
Proof
  strip_tac >>
  simp[stackPlanOpsTheory.reorder_plan_def, stackPlanOpsTheory.reorder_one_def,
       stackModelTheory.stack_get_unfixed_depth_def,
       stackModelTheory.stack_get_depth_def, stackModelTheory.stack_find_def,
       stackModelTheory.stack_peek_def, listTheory.FIND_thm]
QED

Theorem no_ctor_return_plan:
  fn = (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 3 ASSIGN [Lit n] ["formal_var_0"];
         mk_inst 0 ASSIGN [Lit p] ["%0"];
         mk_inst 4 ASSIGN [Var "%0"] ["formal_var_1"];
         mk_inst 1 CODECOPY [Var "formal_var_1"; Label "runtime_begin";
                             Var "formal_var_0"] [];
         mk_inst 5 ASSIGN [Lit n] ["formal_var_2"];
         mk_inst 6 ASSIGN [Var "%0"] ["formal_var_3"];
         mk_inst 2 RETURN [Var "formal_var_3"; Var "formal_var_2"] []] |>]) with
    <| fn_eom := SOME e; fn_mems_used := mems;
       fn_fmp_signature := SOME
         <| fms_has_fmp_param := F; fms_publishes := F |> |> ==>
  stackPlanGen$generate_inst_plan (livenessDefs$liveness_analyze fn)
    (dfgDefs$dfg_build_function fn) (cfgDefs$cfg_analyze fn) fn
    (mk_inst 2 RETURN [Var "formal_var_3"; Var "formal_var_2"] [])
    (livenessDefs$live_vars_at (livenessDefs$liveness_analyze fn) "__deploy" 7)
    T F "__deploy" ((stackPlanGen$init_cleanup_plan_state ch growth spill 0) with
      ps_stack := [Var "formal_var_2"; Var "formal_var_3"]) =
  SOME ([SOEmit "RETURN"],
    (stackPlanGen$init_cleanup_plan_state ch growth spill 0) with ps_stack := [])
Proof
  strip_tac >> gvs[] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``stackPlanOps$reorder_plan``]) >>
  simp[no_ctor_return_reorder]
QED

Theorem no_ctor_insts_plan:
  fn = (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 3 ASSIGN [Lit n] ["formal_var_0"];
         mk_inst 0 ASSIGN [Lit p] ["%0"];
         mk_inst 4 ASSIGN [Var "%0"] ["formal_var_1"];
         mk_inst 1 CODECOPY [Var "formal_var_1"; Label "runtime_begin";
                             Var "formal_var_0"] [];
         mk_inst 5 ASSIGN [Lit n] ["formal_var_2"];
         mk_inst 6 ASSIGN [Var "%0"] ["formal_var_3"];
         mk_inst 2 RETURN [Var "formal_var_3"; Var "formal_var_2"] []] |>]) with
    <| fn_eom := SOME e; fn_mems_used := mems;
       fn_fmp_signature := SOME
         <| fms_has_fmp_param := F; fms_publishes := F |> |> ==>
  stackPlanGen$generate_block_insts_plan (livenessDefs$liveness_analyze fn)
    (dfgDefs$dfg_build_function fn) (cfgDefs$cfg_analyze fn) fn "__deploy"
    T 0 7 0
    [mk_inst 3 ASSIGN [Lit n] ["formal_var_0"];
     mk_inst 0 ASSIGN [Lit p] ["%0"];
     mk_inst 4 ASSIGN [Var "%0"] ["formal_var_1"];
     mk_inst 1 CODECOPY [Var "formal_var_1"; Label "runtime_begin";
                         Var "formal_var_0"] [];
     mk_inst 5 ASSIGN [Lit n] ["formal_var_2"];
     mk_inst 6 ASSIGN [Var "%0"] ["formal_var_3"];
     mk_inst 2 RETURN [Var "formal_var_3"; Var "formal_var_2"] []]
    (stackPlanGen$init_cleanup_plan_state ch growth spill 0) =
  SOME ((if p = n then
     [SOPush (Lit n); SOPush (Lit n); SODup 1]
     else [SOPush (Lit n); SOPush (Lit p); SOSwap 1; SODup 2]) ++
     [SOPushLabel "runtime_begin"; SOSwap 1; SOEmit "CODECOPY";
      SOPush (Lit n)] ++ (if p = n then [] else [SOSwap 1]) ++
     [SOEmit "RETURN"],
    (stackPlanGen$init_cleanup_plan_state ch growth spill 0) with ps_stack := [])
Proof
  strip_tac >>
  drule no_ctor_first_assign_plan >> disch_then assume_tac >>
  drule no_ctor_second_assign_plan >> disch_then assume_tac >>
  drule no_ctor_third_assign_plan >> disch_then assume_tac >>
  drule no_ctor_codecopy_plan >> disch_then assume_tac >>
  drule no_ctor_fourth_assign_plan >> disch_then assume_tac >>
  drule no_ctor_fifth_assign_plan >> disch_then assume_tac >>
  drule no_ctor_return_plan >> disch_then assume_tac >>
  qpat_x_assum `fn = _` kall_tac >>
  Cases_on `p = n` >> gvs[venomInstTheory.mk_inst_def] >>
  simp[stackPlanGenTheory.generate_block_insts_plan_def,
       venomInstTheory.is_terminator_def]
QED

Theorem no_ctor_block_plan:
  fn = (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 3 ASSIGN [Lit n] ["formal_var_0"];
         mk_inst 0 ASSIGN [Lit p] ["%0"];
         mk_inst 4 ASSIGN [Var "%0"] ["formal_var_1"];
         mk_inst 1 CODECOPY [Var "formal_var_1"; Label "runtime_begin";
                             Var "formal_var_0"] [];
         mk_inst 5 ASSIGN [Lit n] ["formal_var_2"];
         mk_inst 6 ASSIGN [Var "%0"] ["formal_var_3"];
         mk_inst 2 RETURN [Var "formal_var_3"; Var "formal_var_2"] []] |>]) with
    <| fn_eom := SOME e; fn_mems_used := mems;
       fn_fmp_signature := SOME
         <| fms_has_fmp_param := F; fms_publishes := F |> |> ==>
  stackPlanGen$generate_block_plan (livenessDefs$liveness_analyze fn)
    (dfgDefs$dfg_build_function fn) (cfgDefs$cfg_analyze fn) fn (HD fn.fn_blocks)
    (stackPlanGen$init_cleanup_plan_state ch growth spill 0) =
  SOME ([SOLabel "__deploy"] ++ (if p = n then
     [SOPush (Lit n); SOPush (Lit n); SODup 1]
     else [SOPush (Lit n); SOPush (Lit p); SOSwap 1; SODup 2]) ++
     [SOPushLabel "runtime_begin"; SOSwap 1; SOEmit "CODECOPY";
      SOPush (Lit n)] ++ (if p = n then [] else [SOSwap 1]) ++
     [SOEmit "RETURN"],
    (stackPlanGen$init_cleanup_plan_state ch growth spill 0) with ps_stack := [])
Proof
  strip_tac >>
  drule no_ctor_insts_plan >> disch_then assume_tac >>
  qpat_x_assum `fn = _` SUBST_ALL_TAC >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``stackPlanGen$generate_block_insts_plan``,
     ``livenessDefs$liveness_analyze``, ``dfgDefs$dfg_build_function``]) >>
  rule_assum_tac (CONV_RULE (computeLib.RESTR_EVAL_CONV
    [``stackPlanGen$generate_block_insts_plan``,
     ``livenessDefs$liveness_analyze``, ``dfgDefs$dfg_build_function``])) >>
  simp[]
QED

Theorem no_ctor_function_plan:
  fn = (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 3 ASSIGN [Lit n] ["formal_var_0"];
         mk_inst 0 ASSIGN [Lit p] ["%0"];
         mk_inst 4 ASSIGN [Var "%0"] ["formal_var_1"];
         mk_inst 1 CODECOPY [Var "formal_var_1"; Label "runtime_begin";
                             Var "formal_var_0"] [];
         mk_inst 5 ASSIGN [Lit n] ["formal_var_2"];
         mk_inst 6 ASSIGN [Var "%0"] ["formal_var_3"];
         mk_inst 2 RETURN [Var "formal_var_3"; Var "formal_var_2"] []] |>]) with
    <| fn_eom := SOME e; fn_mems_used := mems;
       fn_fmp_signature := SOME
         <| fms_has_fmp_param := F; fms_publishes := F |> |> ==>
  stackPlanGen$generate_fn_plan_with_cleanup ch growth fn spill 0 =
  SOME ([SOLabel "__deploy"] ++ (if p = n then
     [SOPush (Lit n); SOPush (Lit n); SODup 1]
     else [SOPush (Lit n); SOPush (Lit p); SOSwap 1; SODup 2]) ++
     [SOPushLabel "runtime_begin"; SOSwap 1; SOEmit "CODECOPY";
      SOPush (Lit n)] ++ (if p = n then [] else [SOSwap 1]) ++
     [SOEmit "RETURN"],
    (stackPlanGen$init_cleanup_plan_state ch growth spill 0) with ps_stack := [])
Proof
  strip_tac >>
  drule no_ctor_block_plan >> disch_then assume_tac >>
  qpat_x_assum `fn = _` SUBST_ALL_TAC >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``stackPlanGen$generate_block_plan``]) >>
  rule_assum_tac (CONV_RULE (computeLib.RESTR_EVAL_CONV
    [``stackPlanGen$generate_block_plan``])) >>
  simp[]
QED

Theorem no_ctor_singleton_context_ops:
  ctx.ctx_functions = [fn] /\
  (!ch growth spill.
    stackPlanGen$generate_fn_plan_with_cleanup ch growth fn spill 0 =
    SOME (ops, (stackPlanGen$init_cleanup_plan_state ch growth spill 0) with
      ps_stack := [])) /\
  stackPlanGen$generate_context_plan ctx = SOME cplan ==>
  stackPlanGen$context_plan_ops cplan = ops ++ stackPlanGen$revert_postamble
Proof
  strip_tac >>
  gvs[stackPlanGenTheory.generate_context_plan_def,
      stackPlanGenTheory.generate_context_plan_with_def,
      stackPlanGenTheory.generate_context_regions_def,
      stackPlanGenTheory.finish_context_plan_def,
      stackPlanGenTheory.init_cleanup_plan_state_def,
      stackPlanTypesTheory.init_plan_state_def,
      stackPlanTypesTheory.init_spill_alloc_def, AllCaseEqs()] >>
  simp[stackPlanGenTheory.context_plan_ops_def]
QED

Theorem no_ctor_context_plan_ops:
  fn = (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 3 ASSIGN [Lit n] ["formal_var_0"];
         mk_inst 0 ASSIGN [Lit p] ["%0"];
         mk_inst 4 ASSIGN [Var "%0"] ["formal_var_1"];
         mk_inst 1 CODECOPY [Var "formal_var_1"; Label "runtime_begin";
                             Var "formal_var_0"] [];
         mk_inst 5 ASSIGN [Lit n] ["formal_var_2"];
         mk_inst 6 ASSIGN [Var "%0"] ["formal_var_3"];
         mk_inst 2 RETURN [Var "formal_var_3"; Var "formal_var_2"] []] |>]) with
    <| fn_eom := SOME e; fn_mems_used := mems;
       fn_fmp_signature := SOME
         <| fms_has_fmp_param := F; fms_publishes := F |> |> /\
  ctx.ctx_functions = [fn] /\
  stackPlanGen$generate_context_plan ctx = SOME cplan ==>
  stackPlanGen$context_plan_ops cplan =
    ([SOLabel "__deploy"] ++ (if p = n then
     [SOPush (Lit n); SOPush (Lit n); SODup 1]
     else [SOPush (Lit n); SOPush (Lit p); SOSwap 1; SODup 2]) ++
     [SOPushLabel "runtime_begin"; SOSwap 1; SOEmit "CODECOPY";
      SOPush (Lit n)] ++ (if p = n then [] else [SOSwap 1]) ++
     [SOEmit "RETURN"]) ++ stackPlanGen$revert_postamble
Proof
  strip_tac >>
  drule no_ctor_function_plan >> disch_then assume_tac >>
  irule no_ctor_singleton_context_ops >> qexistsl_tac [`ctx`, `fn`] >> simp[]
QED

Theorem no_ctor_prefix_assembly:
  planExec$execute_plan fmp
    (([SOLabel "__deploy"] ++ (if p = n then
       [SOPush (Lit n); SOPush (Lit n); SODup 1]
       else [SOPush (Lit n); SOPush (Lit p); SOSwap 1; SODup 2]) ++
       [SOPushLabel "runtime_begin"; SOSwap 1; SOEmit "CODECOPY";
        SOPush (Lit n)] ++ (if p = n then [] else [SOSwap 1]) ++
       [SOEmit "RETURN"]) ++ stackPlanGen$revert_postamble) =
    [AsmLabel "__deploy";
     AsmPush (encode_num_bytes_fuel 32 (w2n n));
     AsmPush (encode_num_bytes_fuel 32 (w2n p))] ++
    (if p = n then [AsmOp "DUP1"] else [AsmOp "SWAP1"; AsmOp "DUP2"]) ++
    [AsmPushLabel "runtime_begin"; AsmOp "SWAP1"; AsmOp "CODECOPY";
     AsmPush (encode_num_bytes_fuel 32 (w2n n))] ++
    (if p = n then [] else [AsmOp "SWAP1"]) ++
    [AsmOp "RETURN"; AsmLabel "revert"; AsmPush []; AsmOp "DUP1"; AsmOp "REVERT"]
Proof
  Cases_on `p = n` >>
  simp[planExecTheory.execute_plan_def, planExecTheory.exec_stack_op_def,
       planExecTheory.swap_name_def, planExecTheory.dup_name_def,
       stackPlanGenTheory.revert_postamble_def] >> EVAL_TAC
QED

Theorem no_ctor_fuel_bytes_bound:
  !fuel n. LENGTH (encode_num_bytes_fuel fuel n) <= fuel
Proof
  Induct >> simp[asmIRTheory.encode_num_bytes_fuel_def] >>
  gen_tac >> Cases_on `n = 0` >> simp[asmIRTheory.encode_num_bytes_fuel_def] >>
  first_x_assum (qspec_then `n DIV 256` mp_tac) >> simp[]
QED

Theorem no_ctor_short_symbol_bytes:
  n < 65536 ==> LENGTH (encode_num_bytes n) <= symbol_size
Proof
  rw[Once asmIRTheory.encode_num_bytes_def, symbolResolveTheory.symbol_size_def] >>
  rw[Once asmIRTheory.encode_num_bytes_def] >>
  `n DIV 256 < 256` by simp[arithmeticTheory.DIV_LT_X] >>
  `n DIV 256 DIV 256 = 0` by simp[arithmeticTheory.DIV_EQ_0] >>
  simp[Once asmIRTheory.encode_num_bytes_def]
QED

Theorem no_ctor_opcode_bytes[local]:
  evm_opcode_byte "CODECOPY" = SOME 0x39w /\
  evm_opcode_byte "SWAP1" = SOME 0x90w /\
  evm_opcode_byte "DUP1" = SOME 0x80w /\
  evm_opcode_byte "DUP2" = SOME 0x81w /\
  evm_opcode_byte "RETURN" = SOME 0xF3w /\
  evm_opcode_byte "REVERT" = SOME 0xFDw
Proof
  EVAL_TAC
QED

Theorem no_ctor_prefix_encode_length:
  prefix =
    [AsmLabel "__deploy"; AsmPush a; AsmPush b] ++
    (if same then [AsmOp "DUP1"] else [AsmOp "SWAP1"; AsmOp "DUP2"]) ++
    [AsmPushLabel "runtime_begin"; AsmOp "SWAP1"; AsmOp "CODECOPY";
     AsmPush a] ++ (if same then [] else [AsmOp "SWAP1"]) ++
    [AsmOp "RETURN"; AsmLabel "revert"; AsmPush []; AsmOp "DUP1"; AsmOp "REVERT"] /\
  FLOOKUP offsets "runtime_begin" = SOME off /\ off < 65536 ==>
  LENGTH (FLAT (MAP (encode_inst offsets) prefix)) =
    SUM (MAP asm_inst_size prefix)
Proof
  strip_tac >> drule no_ctor_short_symbol_bytes >> strip_tac >>
  Cases_on `same` >> gvs[] >>
  simp[symbolResolveTheory.encode_inst_def, symbolResolveTheory.asm_inst_size_def,
       symbolResolveTheory.pad_bytes_def, no_ctor_opcode_bytes] >>
  Cases_on `a` >> Cases_on `b` >> simp[symbolResolveTheory.encode_inst_def] >>
  Cases_on `LENGTH (encode_num_bytes off) >= symbol_size` >> simp[]
QED

Theorem no_ctor_runtime_offset:
  prog = prefix ++ [AsmDataHeader "runtime_begin"; AsmDataItem bytes;
                    AsmDataHeader "code_end"] ==>
  FLOOKUP (SND (compute_label_offsets prog)) "runtime_begin" =
    SOME (SUM (MAP asm_inst_size prefix))
Proof
  strip_tac >> gvs[] >>
  qspec_then `prefix` mp_tac no_ctor_compute_size >>
  Cases_on `compute_label_offsets prefix` >> simp[] >> strip_tac >>
  pure_once_rewrite_tac[symbolResolveTheory.compute_label_offsets_def] >>
  pure_rewrite_tac[rich_listTheory.FOLDL_APPEND] >>
  pure_rewrite_tac[GSYM symbolResolveTheory.compute_label_offsets_def] >>
  simp[symbolResolveTheory.asm_inst_size_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem no_ctor_prefix_size_bound:
  prefix =
    [AsmLabel "__deploy"; AsmPush a; AsmPush b] ++
    (if same then [AsmOp "DUP1"] else [AsmOp "SWAP1"; AsmOp "DUP2"]) ++
    [AsmPushLabel "runtime_begin"; AsmOp "SWAP1"; AsmOp "CODECOPY";
     AsmPush a] ++ (if same then [] else [AsmOp "SWAP1"]) ++
    [AsmOp "RETURN"; AsmLabel "revert"; AsmPush []; AsmOp "DUP1"; AsmOp "REVERT"] /\
  LENGTH a <= 32 /\ LENGTH b <= 32 ==>
  SUM (MAP asm_inst_size prefix) <= 128
Proof
  strip_tac >> Cases_on `same` >>
  gvs[symbolResolveTheory.asm_inst_size_def, symbolResolveTheory.symbol_size_def] >>
  Cases_on `a = []` >> Cases_on `b = []` >> gvs[]
QED

Theorem no_ctor_prefix_width:
  prefix =
    [AsmLabel "__deploy"; AsmPush a; AsmPush b] ++
    (if same then [AsmOp "DUP1"] else [AsmOp "SWAP1"; AsmOp "DUP2"]) ++
    [AsmPushLabel "runtime_begin"; AsmOp "SWAP1"; AsmOp "CODECOPY";
     AsmPush a] ++ (if same then [] else [AsmOp "SWAP1"]) ++
    [AsmOp "RETURN"; AsmLabel "revert"; AsmPush []; AsmOp "DUP1"; AsmOp "REVERT"] /\
  LENGTH a <= 32 /\ LENGTH b <= 32 /\
  prog = prefix ++ [AsmDataHeader "runtime_begin"; AsmDataItem bytes;
                    AsmDataHeader "code_end"] ==>
  LENGTH (FLAT (MAP (encode_inst (SND (compute_label_offsets prog))) prefix)) =
    SUM (MAP asm_inst_size prefix)
Proof
  strip_tac >>
  drule_all no_ctor_prefix_size_bound >> strip_tac >>
  drule no_ctor_runtime_offset >> strip_tac >>
  irule no_ctor_prefix_encode_length >>
  conj_tac >- (qexistsl_tac [`a`, `b`, `same`] >> simp[]) >>
  qexists_tac `SUM (MAP asm_inst_size prefix)` >>
  qpat_x_assum `prefix = _` kall_tac >> simp[] >> decide_tac
QED

Theorem no_ctor_lowering_reservation_cases:
  run_deploy_lowering F rpolicy bytes imm args sz [] cenv stmts pay nr
    nkey ut entry = SOME unit ==>
  (imm = 0 ==> unit.cu_context.ctx_global_reserved = []) /\
  (0 < imm ==> unit.cu_context.ctx_global_reserved = [(0,imm)])
Proof
  strip_tac >> drule run_deploy_lowering_global_reserved >>
  Cases_on `imm = 0` >> simp[]
QED

Theorem no_ctor_pipeline_singleton_walk:
  run_venom_pipeline mem_ok calling_ok post_ok rpolicy o1_pipeline_spec unit =
    SOME out /\
  run_pipeline_stages rpolicy
    [PS_MapFunctions (CFP_Simple VP_SimplifyCFG);
     PS_MapFunctions (CFP_Simple VP_DretDesugar); PS_DiscardAnalyses]
    unit (init_ir_supply unit) = SOME (unit,init_ir_supply unit) /\
  unit.cu_context.ctx_entry = SOME name /\
  fcg_postorder (fcg_analyze unit.cu_context) name = [name] /\
  prune_unit_fcg_unreachable unit (fcg_analyze unit.cu_context) = unit ==>
  ?unit' s'.
    run_configured_fn_passes execute_configured_fn_pass rpolicy o1_fn_passes
      name unit (init_ir_supply unit) = SOME (unit',s') /\
    out.po_unit = unit'
Proof
  simp[run_venom_pipeline_def, venomPassScheduleTheory.o1_pipeline_spec_def,
       run_callee_first_def, run_named_fn_schedules_def,
       run_pipeline_stages_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[run_named_fn_schedules_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem no_ctor_singleton_schedule:
  unit.cu_context.ctx_functions = [fn] /\ fn.fn_name = name /\
  run_configured_fn_passes runner rpolicy passes name unit s = SOME (unit',s') ==>
  ?fn' labels.
    run_configured_fn_pass_fold runner rpolicy passes unit s fn [] =
      SOME (fn',labels,s') /\
    apply_unit_label_map labels
      (unit with cu_context := unit.cu_context with ctx_functions := [fn']) =
      SOME unit'
Proof
  simp[run_configured_fn_passes_def, lookup_unique_function_def,
       replace_unique_function_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem no_ctor_actual_schedule:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  classify_functions tops = (exts, ints, fb, NONE) /\
  raw = mk_raw_function "__deploy"
    [<| bb_label := "__deploy"; bb_instructions :=
      [mk_inst 0 ALLOCA [Lit (n2w (LENGTH runtime_bc + imm_len tops))] ["%0"];
       mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin";
                          Lit (n2w (LENGTH runtime_bc + imm_len tops))] [];
       mk_inst 2 RETURN [Var "%0";
                         Lit (n2w (LENGTH runtime_bc + imm_len tops))] []] |>] ==>
  ?fn' labels s'.
    run_configured_fn_pass_fold execute_configured_fn_pass rpolicy o1_fn_passes
      dunit (init_ir_supply dunit) raw [] = SOME (fn',labels,s') /\
    apply_unit_label_map labels
      (dunit with cu_context := dunit.cu_context with ctx_functions := [fn']) =
      SOME dout.po_unit
Proof
  strip_tac >>
  drule_all no_ctor_deploy_context_shape >> disch_tac >>
  `dunit.cu_context = (mk_venom_context [raw] (SOME "__deploy")) with
    ctx_global_reserved := (if imm_len tops = 0 then [] else [(0,imm_len tops)])` by
    simp[install_immutable_reservation_def] >>
  qpat_x_assum `dunit.cu_context = install_immutable_reservation _ _` kall_tac >>
  `dunit.cu_context.ctx_functions = [raw]` by
    simp[venomInstTheory.mk_venom_context_def] >>
  `raw.fn_name = "__deploy"` by simp[venomInstTheory.mk_raw_function_def] >>
  `?pre_unit pre_supply. run_pipeline_stages rpolicy
    [PS_MapFunctions (CFP_Simple VP_SimplifyCFG);
     PS_MapFunctions (CFP_Simple VP_DretDesugar); PS_DiscardAnalyses]
    dunit (init_ir_supply dunit) = SOME (pre_unit,pre_supply)` by
    (qpat_x_assum `deploy_phases _ _ _ _` mp_tac >>
     simp[deploy_phases_def, o1PipelineCorrectTheory.o1_pipeline_def,
          run_venom_pipeline_def, venomPassScheduleTheory.o1_pipeline_spec_def,
          AllCaseEqs()] >> metis_tac[]) >>
  drule_all no_ctor_prewalk >> strip_tac >>
  qpat_x_assum `pre_unit = _` SUBST_ALL_TAC >>
  qpat_x_assum `pre_supply = _` SUBST_ALL_TAC >>
  `fcg_postorder (fcg_analyze dunit.cu_context) "__deploy" = ["__deploy"] /\
   fcg_is_reachable (fcg_analyze dunit.cu_context) "__deploy"` by
    (irule no_ctor_frozen_call_order >> simp[IgnAsm `raw = _`] >> metis_tac[]) >>
  `prune_unit_fcg_unreachable dunit (fcg_analyze dunit.cu_context) = dunit` by
    metis_tac[no_ctor_pruned_unit] >>
  `dunit.cu_context.ctx_entry = SOME "__deploy"` by
    simp[venomInstTheory.mk_venom_context_def] >>
  `run_venom_pipeline (K T) (K T) (K T) rpolicy o1_pipeline_spec dunit = SOME dout` by
    gvs[deploy_phases_def, o1PipelineCorrectTheory.o1_pipeline_def] >>
  drule_all no_ctor_pipeline_singleton_walk >> strip_tac >>
  drule_all no_ctor_singleton_schedule >> metis_tac[]
QED

Theorem no_ctor_fold_append:
  !passes rest s fn labels.
  run_configured_fn_pass_fold runner rpolicy (passes ++ rest) unit s fn labels =
  case run_configured_fn_pass_fold runner rpolicy passes unit s fn labels of
    NONE => NONE
  | SOME (fn1, labels1, s1) =>
      run_configured_fn_pass_fold runner rpolicy rest unit s1 fn1 labels1
Proof
  Induct_on `passes` >>
  simp[Once run_configured_fn_pass_fold_def] >>
  rpt gen_tac >>
  simp[Once run_configured_fn_pass_fold_def] >>
  rpt CASE_TAC >> simp[]
QED

Theorem no_ctor_initial_supply:
  unit.cu_context = install_immutable_reservation m
    (mk_venom_context
      [mk_raw_function "__deploy"
        [<| bb_label := "__deploy"; bb_instructions :=
          [mk_inst 0 ALLOCA [Lit n] ["%0"];
           mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit n] [];
           mk_inst 2 RETURN [Var "%0"; Lit n] []] |>]]
      (SOME "__deploy")) ==>
  (init_ir_supply unit).irs_next_inst = 3 /\
  (init_ir_supply unit).irs_next_var = 0 /\
  (init_ir_supply unit).irs_used_vars = ["%0"; "%0"; "%0"]
Proof
  strip_tac >>
  simp[irSupplyTheory.init_ir_supply_def,
       irSupplyTheory.unit_ir_inst_ids_def, irSupplyTheory.unit_ir_vars_def,
       irSupplyTheory.fn_ir_inst_ids_def, irSupplyTheory.fn_ir_vars_def,
       irSupplyTheory.block_ir_inst_ids_def, irSupplyTheory.block_ir_vars_def,
       irSupplyTheory.inst_ir_vars_def, install_immutable_reservation_def,
       venomInstTheory.mk_venom_context_def, venomInstTheory.mk_raw_function_def,
       venomInstTheory.mk_inst_def, venomInstTheory.inst_uses_def,
       venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def]
QED

Theorem no_ctor_actual_alloca_bound:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  classify_functions tops = (exts, ints, fb, NONE) ==>
  imm_len tops + w2n (n2w (LENGTH runtime_bc + imm_len tops) : bytes32) <
    dimword(:256)
Proof
  strip_tac >>
  drule_all no_ctor_deploy_context_shape >> disch_tac >>
  `unit_alloca_budget dunit.cu_context =
     w2n (n2w (LENGTH runtime_bc + imm_len tops) : bytes32)` by
    simp[unit_alloca_budget_def, install_immutable_reservation_def,
         venomInstTheory.mk_venom_context_def, venomInstTheory.mk_raw_function_def,
         venomInstTheory.fn_insts_def, venomInstTheory.fn_insts_blocks_def,
         venomInstTheory.mk_inst_def, alloca_size_def] >>
  drule deploy_imm_budget_ok >> decide_tac
QED

Theorem no_ctor_late_sue_concrete:
  fn = (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 0 ASSIGN [Lit p] ["%0"];
         mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit n] [];
         mk_inst 2 RETURN [Var "%0"; Lit n] []] |>]) with
    <| fn_eom := SOME e; fn_mems_used := mems;
       fn_fmp_signature := SOME
         <| fms_has_fmp_param := F; fms_publishes := F |> |> /\
  s.irs_next_inst = 3 /\ s.irs_next_var = 0 /\
  s.irs_used_vars = ["%0"; "%0"; "%0"] ==>
  ?s'. singleUseExpansionDefs$sue_expand_function_supply s fn =
    (fn with fn_blocks :=
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 0 ASSIGN [Lit p] ["%0"];
         mk_inst 4 ASSIGN [Var "%0"] ["formal_var_1"];
         mk_inst 3 ASSIGN [Lit n] ["formal_var_0"];
         mk_inst 1 CODECOPY [Var "formal_var_1"; Label "runtime_begin";
                             Var "formal_var_0"] [];
         mk_inst 6 ASSIGN [Var "%0"] ["formal_var_3"];
         mk_inst 5 ASSIGN [Lit n] ["formal_var_2"];
         mk_inst 2 RETURN [Var "formal_var_3"; Var "formal_var_2"] []] |>], s')
Proof
  strip_tac >>
  drule_all no_ctor_sue_four_allocations >>
  disch_then (qspec_then `n` mp_tac) >>
  pure_rewrite_tac [LET_THM] >> ntac 4 (pairarg_tac >> simp[]) >> strip_tac >>
  drule_all no_ctor_late_sue >> simp[] >> metis_tac[]
QED

Theorem no_ctor_fold_context_free_step:
  (!observed. execute_configured_fn_pass rpolicy pass observed s fn = SOME out) /\
  run_configured_fn_pass_fold execute_configured_fn_pass rpolicy
    (pass::passes) unit s fn labels = SOME result ==>
  run_configured_fn_pass_fold execute_configured_fn_pass rpolicy
    passes unit out.fpo_supply out.fpo_function
    (labels ++ out.fpo_label_map) = SOME result
Proof
  simp[Once run_configured_fn_pass_fold_def] >>
  strip_tac >> gvs[AllCaseEqs()]
QED

Theorem no_ctor_late_fold:
  makeSsaDefs$make_ssa_current_fn s fn = (fn,s) /\
  simplifyCfgDefs$simplify_cfg_fn_with_labels fn = (fn,[]) /\
  singleUseExpansionDefs$sue_expand_function_supply s fn = (expanded,t) /\
  dftDefs$dft_fn expanded = ordered /\
  cfgNormDefs$cfg_norm_function_supply t ordered = (ordered,t) /\
  run_configured_fn_pass_fold execute_configured_fn_pass rpolicy
    [CFP_Simple VP_MakeSSA; CFP_Simple VP_SimplifyCFG;
     CFP_Simple VP_SingleUseExpansion; CFP_Simple VP_DFT;
     CFP_Simple VP_CFGNormalization] unit s fn [] = SOME (last,labels,final) ==>
  last = ordered /\ labels = [] /\ final = t
Proof
  strip_tac >>
  `!observed. execute_configured_fn_pass rpolicy (CFP_Simple VP_MakeSSA)
     observed s fn = SOME <| fpo_function := fn; fpo_label_map := [];
                            fpo_supply := s |>` by simp[] >>
  drule_all no_ctor_fold_context_free_step >> simp[NoAsms] >> disch_tac >>
  qpat_x_assum `run_configured_fn_pass_fold _ _ (CFP_Simple VP_MakeSSA::_) _ _ _ _ = _` kall_tac >>
  `!observed. execute_configured_fn_pass rpolicy (CFP_Simple VP_SimplifyCFG)
     observed s fn = SOME <| fpo_function := fn; fpo_label_map := [];
                            fpo_supply := s |>` by simp[] >>
  drule_all no_ctor_fold_context_free_step >> simp[NoAsms] >> disch_tac >>
  qpat_x_assum `run_configured_fn_pass_fold _ _ (CFP_Simple VP_SimplifyCFG::_) _ _ _ _ = _` kall_tac >>
  `!observed. execute_configured_fn_pass rpolicy (CFP_Simple VP_SingleUseExpansion)
     observed s fn = SOME <| fpo_function := expanded; fpo_label_map := [];
                            fpo_supply := t |>` by simp[] >>
  drule_all no_ctor_fold_context_free_step >> simp[NoAsms] >> disch_tac >>
  qpat_x_assum `run_configured_fn_pass_fold _ _ (CFP_Simple VP_SingleUseExpansion::_) _ _ _ _ = _` kall_tac >>
  `!observed. execute_configured_fn_pass rpolicy (CFP_Simple VP_DFT)
     observed t expanded = SOME <| fpo_function := ordered; fpo_label_map := [];
                                  fpo_supply := t |>` by
    simp[venomPassDispatcherTheory.execute_configured_fn_pass_def] >>
  drule_all no_ctor_fold_context_free_step >> simp[NoAsms] >> disch_tac >>
  qpat_x_assum `run_configured_fn_pass_fold _ _ (CFP_Simple VP_DFT::_) _ _ _ _ = _` kall_tac >>
  `!observed. execute_configured_fn_pass rpolicy (CFP_Simple VP_CFGNormalization)
     observed t ordered = SOME <| fpo_function := ordered; fpo_label_map := [];
                                 fpo_supply := t |>` by
    simp[venomPassDispatcherTheory.execute_configured_fn_pass_def] >>
  drule_all no_ctor_fold_context_free_step >>
  simp[NoAsms, run_configured_fn_pass_fold_def] >> metis_tac[]
QED

Theorem no_ctor_o1_split:
  run_configured_fn_pass_fold runner rpolicy o1_fn_passes unit s raw [] =
    SOME result ==>
  ?early labels s1.
    run_configured_fn_pass_fold runner rpolicy
      [CFP_Simple VP_MakeSSA; CFP_Simple VP_LowerDload;
       CFP_Simple VP_ConcretizeMemLoc; CFP_Simple VP_FmpLowering]
      unit s raw [] = SOME (early,labels,s1) /\
    run_configured_fn_pass_fold runner rpolicy
      [CFP_Simple VP_MakeSSA; CFP_Simple VP_SimplifyCFG;
       CFP_Simple VP_SingleUseExpansion; CFP_Simple VP_DFT;
       CFP_Simple VP_CFGNormalization]
      unit s1 early labels = SOME result
Proof
  qspec_then `[CFP_Simple VP_MakeSSA; CFP_Simple VP_LowerDload;
       CFP_Simple VP_ConcretizeMemLoc; CFP_Simple VP_FmpLowering]`
    mp_tac no_ctor_fold_append >>
  disch_then (qspec_then `[CFP_Simple VP_MakeSSA; CFP_Simple VP_SimplifyCFG;
       CFP_Simple VP_SingleUseExpansion; CFP_Simple VP_DFT;
       CFP_Simple VP_CFGNormalization]` mp_tac) >>
  disch_then (qspecl_then [`s`, `raw`, `[]`] mp_tac) >>
  simp[venomPassScheduleTheory.o1_fn_passes_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem no_ctor_fixed_late_result:
  fn = (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 0 ASSIGN [Lit p] ["%0"];
         mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit n] [];
         mk_inst 2 RETURN [Var "%0"; Lit n] []] |>]) with
    <| fn_eom := SOME e; fn_mems_used := mems;
       fn_fmp_signature := SOME
         <| fms_has_fmp_param := F; fms_publishes := F |> |> /\
  ordered = (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 3 ASSIGN [Lit n] ["formal_var_0"];
         mk_inst 0 ASSIGN [Lit p] ["%0"];
         mk_inst 4 ASSIGN [Var "%0"] ["formal_var_1"];
         mk_inst 1 CODECOPY [Var "formal_var_1"; Label "runtime_begin";
                             Var "formal_var_0"] [];
         mk_inst 5 ASSIGN [Lit n] ["formal_var_2"];
         mk_inst 6 ASSIGN [Var "%0"] ["formal_var_3"];
         mk_inst 2 RETURN [Var "formal_var_3"; Var "formal_var_2"] []] |>]) with
    <| fn_eom := SOME e; fn_mems_used := mems;
       fn_fmp_signature := SOME
         <| fms_has_fmp_param := F; fms_publishes := F |> |> /\
  s.irs_next_inst = 3 /\ s.irs_next_var = 0 /\
  s.irs_used_vars = ["%0"; "%0"; "%0"] /\
  run_configured_fn_pass_fold execute_configured_fn_pass rpolicy
    [CFP_Simple VP_MakeSSA; CFP_Simple VP_SimplifyCFG;
     CFP_Simple VP_SingleUseExpansion; CFP_Simple VP_DFT;
     CFP_Simple VP_CFGNormalization] unit s fn [] = SOME (last,labels,final) ==>
  last = ordered /\ labels = []
Proof
  strip_tac >>
  drule_all no_ctor_late_sue_concrete >> strip_tac >>
  qmatch_asmsub_abbrev_tac `sue_expand_function_supply s fn = (expanded,t)` >>
  `make_ssa_current_fn s fn = (fn,s)` by metis_tac[no_ctor_late_make_ssa] >>
  `simplify_cfg_fn_with_labels fn = (fn,[])` by metis_tac[no_ctor_late_simplify_cfg] >>
  `dft_fn expanded = ordered` by
    (irule EQ_TRANS >> irule_at Any no_ctor_late_dft >>
     simp[Abbr `expanded`, venomInstTheory.mk_raw_function_def] >>
     metis_tac[]) >>
  `cfg_norm_function_supply t ordered = (ordered,t)` by
    metis_tac[no_ctor_late_cfg_norm] >>
  drule_all no_ctor_late_fold >> simp[]
QED

Theorem no_ctor_optimized_context_shape:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  classify_functions tops = (exts, ints, fb, NONE) ==>
  ?p e mems fn.
    dout.po_unit.cu_context.ctx_functions = [fn] /\
    fn = (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 3 ASSIGN [Lit (n2w (LENGTH runtime_bc + imm_len tops))] ["formal_var_0"];
         mk_inst 0 ASSIGN [Lit p] ["%0"];
         mk_inst 4 ASSIGN [Var "%0"] ["formal_var_1"];
         mk_inst 1 CODECOPY [Var "formal_var_1"; Label "runtime_begin";
                             Var "formal_var_0"] [];
         mk_inst 5 ASSIGN [Lit (n2w (LENGTH runtime_bc + imm_len tops))] ["formal_var_2"];
         mk_inst 6 ASSIGN [Var "%0"] ["formal_var_3"];
         mk_inst 2 RETURN [Var "formal_var_3"; Var "formal_var_2"] []] |>]) with
    <| fn_eom := SOME e; fn_mems_used := mems;
       fn_fmp_signature := SOME
         <| fms_has_fmp_param := F; fms_publishes := F |> |>
Proof
  strip_tac >>
  drule_all no_ctor_deploy_context_shape >> disch_tac >>
  qabbrev_tac `n = n2w (LENGTH runtime_bc + imm_len tops) : bytes32` >>
  qabbrev_tac `m = imm_len tops` >>
  qabbrev_tac `raw = mk_raw_function "__deploy"
    [<| bb_label := "__deploy"; bb_instructions :=
      [mk_inst 0 ALLOCA [Lit n] ["%0"];
       mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit n] [];
       mk_inst 2 RETURN [Var "%0"; Lit n] []] |>]` >>
  `dunit.cu_context = install_immutable_reservation m
     (mk_venom_context [raw] (SOME "__deploy"))` by
    simp[Abbr `raw`, Abbr `n`, Abbr `m`] >>
  `?last labels final.
    run_configured_fn_pass_fold execute_configured_fn_pass rpolicy o1_fn_passes
      dunit (init_ir_supply dunit) raw [] = SOME (last,labels,final) /\
    apply_unit_label_map labels
      (dunit with cu_context := dunit.cu_context with ctx_functions := [last]) =
      SOME dout.po_unit` by
    (irule no_ctor_actual_schedule >> simp[Abbr `raw`, Abbr `n`, Abbr `m`] >>
     metis_tac[]) >>
  drule_all no_ctor_o1_split >> strip_tac >>
  qabbrev_tac `fixed = (mk_raw_function "__deploy"
    [<| bb_label := "__deploy"; bb_instructions :=
      [mk_inst 0 ASSIGN [Lit (n2w m)] ["%0"];
       mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit n] [];
       mk_inst 2 RETURN [Var "%0"; Lit n] []] |>]) with
    <| fn_eom := SOME (m + w2n n); fn_mems_used := [(Allocation 0,m,w2n n)] |>` >>
  `m + w2n n < dimword(:256)` by
    (drule_all no_ctor_actual_alloca_bound >> simp[Abbr `m`, Abbr `n`]) >>
  `LENGTH runtime_bc + imm_len tops < dimword(:256)` by
    (drule deploy_imm_budget_ok >> decide_tac) >>
  `m <> 0 ==> 0 < w2n n` by
    (simp[Abbr `m`, Abbr `n`, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
     decide_tac) >>
  `early = fixed with fn_fmp_signature := SOME
      <| fms_has_fmp_param := F; fms_publishes := F |> /\
   labels' = [] /\
   s1 = (if MEM "code_end" (init_ir_supply dunit).irs_used_labels then
      init_ir_supply dunit else (init_ir_supply dunit) with irs_used_labels :=
      "code_end" :: (init_ir_supply dunit).irs_used_labels)` by
    (`dunit.cu_context = (mk_venom_context [raw] (SOME "__deploy")) with
       ctx_global_reserved := (if m = 0 then [] else [(0,m)])` by
       (qpat_assum `dunit.cu_context = install_immutable_reservation _ _` mp_tac >>
        simp[NoAsms, install_immutable_reservation_def]) >>
     qpat_assum `Abbrev (raw = _)`
       (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `Abbrev (fixed = _)`
       (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     irule no_ctor_early_fold >> qexistsl_tac [`m`, `n`] >>
     goal_assum (drule_at Any) >>
     simp[IgnAsm `raw = _`, IgnAsm `fixed = _`,
          IgnAsm `Abbrev (raw = _)`, IgnAsm `Abbrev (fixed = _)`] >>
     metis_tac[]) >>
  `(init_ir_supply dunit).irs_next_inst = 3 /\
   (init_ir_supply dunit).irs_next_var = 0 /\
   (init_ir_supply dunit).irs_used_vars = ["%0"; "%0"; "%0"]` by
    (irule no_ctor_initial_supply >> qexistsl_tac [`m`, `n`] >>
     simp[Abbr `raw`]) >>
  `s1.irs_next_inst = 3 /\ s1.irs_next_var = 0 /\
   s1.irs_used_vars = ["%0"; "%0"; "%0"]` by
    (Cases_on `MEM "code_end" (init_ir_supply dunit).irs_used_labels` >> simp[]) >>
  qpat_x_assum `labels' = []` SUBST_ALL_TAC >>
  qabbrev_tac `ordered = (mk_raw_function "__deploy"
      [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 3 ASSIGN [Lit n] ["formal_var_0"];
         mk_inst 0 ASSIGN [Lit (n2w m)] ["%0"];
         mk_inst 4 ASSIGN [Var "%0"] ["formal_var_1"];
         mk_inst 1 CODECOPY [Var "formal_var_1"; Label "runtime_begin";
                             Var "formal_var_0"] [];
         mk_inst 5 ASSIGN [Lit n] ["formal_var_2"];
         mk_inst 6 ASSIGN [Var "%0"] ["formal_var_3"];
         mk_inst 2 RETURN [Var "formal_var_3"; Var "formal_var_2"] []] |>]) with
    <| fn_eom := SOME (m + w2n n); fn_mems_used := [(Allocation 0,m,w2n n)];
       fn_fmp_signature := SOME
         <| fms_has_fmp_param := F; fms_publishes := F |> |>` >>
  `last = ordered /\ labels = []` by
    (irule no_ctor_fixed_late_result >>
     goal_assum (drule_at (Pat `run_configured_fn_pass_fold _ _ _ _ _ _ _ = _`)) >>
     qexistsl_tac [`m + w2n n`, `[(Allocation 0,m,w2n n)]`, `n`, `n2w m`] >>
     simp[Abbr `ordered`, Abbr `fixed`]) >>
  qpat_x_assum `apply_unit_label_map _ _ = _` mp_tac >>
  simp[no_ctor_empty_label_map] >> disch_tac >>
  qexistsl_tac [`n2w m`, `m + w2n n`, `[(Allocation 0,m,w2n n)]`] >>
  qpat_x_assum `_ = dout.po_unit` (SUBST_ALL_TAC o SYM) >>
  simp[Abbr `ordered`]
QED

Theorem no_ctor_actual_prefix:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  classify_functions tops = (exts, ints, fb, NONE) ==>
  ?p:bytes32. prog =
    ([AsmLabel "__deploy";
      AsmPush (encode_num_bytes_fuel 32 (w2n (n2w (LENGTH runtime_bc + imm_len tops) : bytes32)));
      AsmPush (encode_num_bytes_fuel 32 (w2n p))] ++
    (if p = n2w (LENGTH runtime_bc + imm_len tops) then [AsmOp "DUP1"]
     else [AsmOp "SWAP1"; AsmOp "DUP2"]) ++
    [AsmPushLabel "runtime_begin"; AsmOp "SWAP1"; AsmOp "CODECOPY";
     AsmPush (encode_num_bytes_fuel 32 (w2n (n2w (LENGTH runtime_bc + imm_len tops) : bytes32)))] ++
    (if p = n2w (LENGTH runtime_bc + imm_len tops) then [] else [AsmOp "SWAP1"]) ++
    [AsmOp "RETURN"; AsmLabel "revert"; AsmPush []; AsmOp "DUP1"; AsmOp "REVERT"]) ++
    [AsmDataHeader "runtime_begin"; AsmDataItem runtime_bc; AsmDataHeader "code_end"]
Proof
  strip_tac >> drule_all no_ctor_optimized_context_shape >> strip_tac >>
  `generate_context_plan dout.po_unit.cu_context = SOME cplan` by
    gvs[deploy_phases_def] >>
  drule_all no_ctor_context_plan_ops >> disch_tac >>
  drule_all no_ctor_assembly_shape >> disch_tac >>
  qexists_tac `p` >> pure_asm_rewrite_tac[no_ctor_prefix_assembly] >> REFL_TAC
QED

Theorem no_ctor_actual_runtime_suffix:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  classify_functions tops = (exts, ints, fb, NONE) ==>
  ?off. FLOOKUP (SND (compute_label_offsets prog)) "runtime_begin" = SOME off /\
        off <= 128 /\ DROP off deploy_bc = runtime_bc
Proof
  strip_tac >> drule_all no_ctor_actual_prefix >> strip_tac >>
  qmatch_asmsub_abbrev_tac `prog = prefix ++
    [AsmDataHeader "runtime_begin"; AsmDataItem runtime_bc; AsmDataHeader "code_end"]` >>
  `LENGTH (encode_num_bytes_fuel 32 (w2n p)) <= 32` by
    simp[no_ctor_fuel_bytes_bound] >>
  `LENGTH (encode_num_bytes_fuel 32
     (w2n (n2w (LENGTH runtime_bc + imm_len tops) : bytes32))) <= 32` by
    simp[no_ctor_fuel_bytes_bound] >>
  qpat_assum `Abbrev (prefix = _)`
    (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all no_ctor_prefix_size_bound >> disch_tac >>
  drule_all no_ctor_prefix_width >> disch_tac >>
  `FLOOKUP (SND (compute_label_offsets prog)) "runtime_begin" =
      SOME (SUM (MAP asm_inst_size prefix)) /\
   DROP (SUM (MAP asm_inst_size prefix)) (assemble prog) = runtime_bc` by
    (irule no_ctor_singleton_suffix >> qexists_tac `prefix` >>
     simp[IgnAsm `prefix = _`, IgnAsm `Abbrev (prefix = _)`]) >>
  `deploy_bc = assemble prog` by
    (qpat_assum `deploy_phases _ _ _ _` mp_tac >>
     simp[NoAsms, deploy_phases_def]) >>
  qpat_x_assum `prefix = _` kall_tac >>
  qpat_x_assum `Abbrev (prefix = _)` kall_tac >>
  qpat_x_assum `prog = _` kall_tac >>
  qexists_tac `SUM (MAP asm_inst_size prefix)` >>
  asm_rewrite_tac[]
QED

Theorem no_ctor_runtime_suffix:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  classify_functions tops = (exts, ints, fb, NONE) ==>
  ?off. FLOOKUP (SND (compute_label_offsets prog)) "runtime_begin" = SOME off /\
        off < dimword(:256) /\ DROP off deploy_bc = runtime_bc
Proof
  strip_tac >> drule_all no_ctor_actual_runtime_suffix >> strip_tac >>
  qexists_tac `off` >> simp[] >>
  fs[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``]
QED

Theorem no_ctor_fresh_sequence:
  FLOOKUP s.vs_allocas id = NONE /\
  FLOOKUP s.vs_labels "runtime_begin" = SOME (n2w codepos) /\
  TAKE (LENGTH bytes)
    (DROP codepos s.vs_code ++ REPLICATE (LENGTH bytes) 0w) = bytes /\
  s.vs_alloca_next < dimword(:256) /\
  LENGTH bytes < dimword(:256) /\ codepos < dimword(:256) ==>
  ?ss. run_inst_seq
    [mk_inst id ALLOCA [Lit (n2w (LENGTH bytes))] [buf];
     mk_inst (id + 1) CODECOPY
       [Var buf; Label "runtime_begin"; Lit (n2w (LENGTH bytes))] [];
     mk_inst (id + 2) RETURN [Var buf; Lit (n2w (LENGTH bytes))] []] s = Halt ss /\
    ss.vs_returndata = bytes /\ ss.vs_halted /\
    ss.vs_accounts = s.vs_accounts /\ ss.vs_transient = s.vs_transient /\
    ss.vs_logs = s.vs_logs
Proof
  strip_tac >>
  qabbrev_tac `t = update_var buf (n2w s.vs_alloca_next)
    (s with <| vs_allocas := s.vs_allocas |+ (id, (s.vs_alloca_next, LENGTH bytes));
               vs_alloca_next := s.vs_alloca_next + LENGTH bytes |>)` >>
  `step_inst_base (mk_inst id ALLOCA [Lit (n2w (LENGTH bytes))] [buf]) s = OK t` by
    (PURE_ONCE_REWRITE_TAC[venomExecSemanticsTheory.step_inst_base_def] >>
     simp[Abbr `t`, venomInstTheory.mk_inst_def,
          venomExecSemanticsTheory.exec_alloca_def,
          eval_operand_def, wordsTheory.w2n_n2w]) >>
  `eval_operand (Var buf) t = SOME (n2w s.vs_alloca_next) /\
   FLOOKUP t.vs_labels "runtime_begin" = SOME (n2w codepos) /\
   TAKE (LENGTH bytes)
     (DROP codepos t.vs_code ++ REPLICATE (LENGTH bytes) 0w) = bytes` by
    simp[Abbr `t`, update_var_def, eval_operand_def, lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  drule_all immutable_deploy_runtime_only_tail >>
  disch_then (qspec_then `id + 1` strip_assume_tac) >>
  qexists_tac `s'` >>
  simp[Once exprLoweringPropsTheory.run_inst_seq_def] >>
  fs[Abbr `t`, update_var_def, arithmeticTheory.ADD_ASSOC]
QED

Theorem no_ctor_entry_sequence:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  deploy_state_rel tops deploy_bc am tx es /\
  gas_variant vs (deploy_entry_state prog cplan tops es) /\
  classify_functions tops = (exts, ints, fb, NONE) ==>
  ?ss. run_inst_seq
    [mk_inst 0 ALLOCA [Lit (n2w (LENGTH runtime_bc + imm_len tops))] ["%0"];
     mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin";
       Lit (n2w (LENGTH runtime_bc + imm_len tops))] [];
     mk_inst 2 RETURN [Var "%0"; Lit (n2w (LENGTH runtime_bc + imm_len tops))] []] vs = Halt ss /\
    ss.vs_returndata = runtime_bc ++ REPLICATE (imm_len tops) 0w /\ ss.vs_halted /\
    ss.vs_accounts = vs.vs_accounts /\ ss.vs_transient = vs.vs_transient /\
    ss.vs_logs = vs.vs_logs
Proof
  strip_tac >> drule_all no_ctor_runtime_suffix >> strip_tac >>
  drule_all no_ctor_entry_code >> strip_tac >>
  drule deploy_imm_budget_ok >> strip_tac >>
  `imm_len tops < dimword(:256) /\
   LENGTH runtime_bc + imm_len tops < dimword(:256)` by decide_tac >>
  `vs.vs_allocas = FEMPTY /\ vs.vs_alloca_next = imm_len tops` by
    (qpat_x_assum `gas_variant _ _` (mp_tac o SRULE [gas_variant_def]) >>
     disch_then (mp_tac o Q.AP_TERM `\s. (s.vs_allocas, s.vs_alloca_next)`) >>
     simp[deploy_entry_state_def, entry_venom_state_def, init_venom_state_def]) >>
  irule (no_ctor_fresh_sequence |>
    Q.INST [`bytes` |-> `runtime_bc ++ REPLICATE (imm_len tops) 0w`, `id` |-> `0`] |>
    SRULE [listTheory.LENGTH_APPEND, rich_listTheory.LENGTH_REPLICATE]) >>
  simp[] >> qexists_tac `off` >>
  asm_rewrite_tac[finite_mapTheory.FLOOKUP_o_f] >>
  simp[rich_listTheory.TAKE_APPEND, listTheory.TAKE_LENGTH_TOO_LONG,
       rich_listTheory.REPLICATE_GENLIST, listTheory.TAKE_GENLIST,
       arithmeticTheory.MIN_DEF]
QED

Theorem no_ctor_simple_context_execution:
  FLOOKUP s.vs_allocas 0 = NONE /\
  FLOOKUP s.vs_labels "runtime_begin" = SOME (n2w codepos) /\
  TAKE (LENGTH bytes)
    (DROP codepos s.vs_code ++ REPLICATE (LENGTH bytes) 0w) = bytes /\
  s.vs_alloca_next < dimword(:256) /\
  LENGTH bytes < dimword(:256) /\ codepos < dimword(:256) ==>
  ?ss. run_context 1
    (install_immutable_reservation imm (mk_venom_context
      [mk_raw_function "__deploy" [<| bb_label := "__deploy"; bb_instructions :=
        [mk_inst 0 ALLOCA [Lit (n2w (LENGTH bytes))] ["%0"];
         mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit (n2w (LENGTH bytes))] [];
         mk_inst 2 RETURN [Var "%0"; Lit (n2w (LENGTH bytes))] []] |>]]
      (SOME "__deploy"))) s = Halt ss /\
    ss.vs_returndata = bytes /\ ss.vs_halted /\
    ss.vs_accounts = s.vs_accounts /\ ss.vs_transient = s.vs_transient /\
    ss.vs_logs = s.vs_logs
Proof
  strip_tac >>
  qabbrev_tac `t = s with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                            vs_inst_idx := 0 |>` >>
  `?ss. run_inst_seq
    [mk_inst 0 ALLOCA [Lit (n2w (LENGTH bytes))] ["%0"];
     mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit (n2w (LENGTH bytes))] [];
     mk_inst 2 RETURN [Var "%0"; Lit (n2w (LENGTH bytes))] []] t = Halt ss /\
    ss.vs_returndata = bytes /\ ss.vs_halted /\
    ss.vs_accounts = t.vs_accounts /\ ss.vs_transient = t.vs_transient /\
    ss.vs_logs = t.vs_logs` by
    (irule (no_ctor_fresh_sequence |> Q.INST [`id` |-> `0`] |> SRULE []) >>
     simp[Abbr `t`] >> qexists_tac `codepos` >> simp[]) >>
  qmatch_goalsub_abbrev_tac `run_context 1 ctx s` >>
  qmatch_asmsub_abbrev_tac `mk_raw_function "__deploy" [bb]` >>
  drule_at (Pat `run_inst_seq _ _ = _`)
    (immutable_deploy_block_terminal_bridge |>
     Q.INST [`pre` |->
       `[mk_inst 0 ALLOCA [Lit (n2w (LENGTH bytes))] ["%0"];
         mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin";
           Lit (n2w (LENGTH bytes))] []]`] |> SRULE []) >>
  disch_then (qspecl_then [`0`, `ctx`, `bb`] mp_tac) >>
  (impl_tac >-
    (simp[Abbr `bb`, Abbr `t`, venomInstTheory.mk_inst_def,
          venomInstTheory.is_terminator_def] >>
     PURE_ONCE_REWRITE_TAC[venomExecSemanticsTheory.step_inst_base_def] >>
     simp[venomExecSemanticsTheory.exec_alloca_def, AllCaseEqs()])) >>
  strip_tac >> qexists_tac `final'` >>
  `run_context 1 ctx s = Halt final'` by
    (qpat_assum `run_block_non_phis 0 ctx bb t = _` mp_tac >>
     simp[NoAsms, venomExecSemanticsTheory.run_context_def,
          venomExecSemanticsTheory.run_function_def,
          Abbr `ctx`, install_immutable_reservation_def,
          venomInstTheory.mk_venom_context_def, venomInstTheory.mk_raw_function_def,
          venomInstTheory.lookup_function_def, venomInstTheory.fn_entry_label_def,
          listTheory.FIND_thm, venomInstTheory.entry_block_def,
          Once venomExecSemanticsTheory.run_blocks_def,
          venomInstTheory.lookup_block_def, Abbr `bb`,
          venomExecSemanticsTheory.run_block_def,
          venomExecSemanticsTheory.eval_phis_def,
          venomExecSemanticsTheory.phi_prefix_length_def,
          venomInstTheory.mk_inst_def, Abbr `t`]) >>
  fs[Abbr `t`]
QED

Theorem no_ctor_target_execution:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  deploy_state_rel tops deploy_bc am tx es /\
  gas_variant vs (deploy_entry_state prog cplan tops es) /\
  classify_functions tops = (exts, ints, fb, NONE) ==>
  ?fuel ss. run_context fuel dunit.cu_context vs = Halt ss /\
    ss.vs_returndata = runtime_bc ++ REPLICATE (imm_len tops) 0w /\
    ss.vs_accounts = vs.vs_accounts /\ ss.vs_transient = vs.vs_transient /\
    ss.vs_logs = vs.vs_logs
Proof
  strip_tac >> drule_all no_ctor_deploy_context_shape >> disch_tac >>
  drule_all no_ctor_runtime_suffix >> strip_tac >>
  drule_all no_ctor_entry_code >> strip_tac >>
  drule deploy_imm_budget_ok >> strip_tac >>
  `imm_len tops < dimword(:256) /\
   LENGTH runtime_bc + imm_len tops < dimword(:256)` by decide_tac >>
  `vs.vs_allocas = FEMPTY /\ vs.vs_alloca_next = imm_len tops` by
    (qpat_x_assum `gas_variant _ _` (mp_tac o SRULE [gas_variant_def]) >>
     disch_then (mp_tac o Q.AP_TERM `\s. (s.vs_allocas, s.vs_alloca_next)`) >>
     simp[deploy_entry_state_def, entry_venom_state_def, init_venom_state_def]) >>
  qexists_tac `1` >> asm_rewrite_tac[] >>
  mp_tac (no_ctor_simple_context_execution |>
    Q.INST [`bytes` |-> `runtime_bc ++ REPLICATE (imm_len tops) 0w`,
            `s` |-> `vs`, `imm` |-> `imm_len tops`, `codepos` |-> `off`] |>
    SRULE [listTheory.LENGTH_APPEND, rich_listTheory.LENGTH_REPLICATE]) >>
  (impl_tac >-
    (asm_rewrite_tac[finite_mapTheory.FLOOKUP_o_f] >>
     simp[rich_listTheory.TAKE_APPEND, listTheory.TAKE_LENGTH_TOO_LONG,
          rich_listTheory.REPLICATE_GENLIST, listTheory.TAKE_GENLIST,
          arithmeticTheory.MIN_DEF])) >>
  metis_tac[]
QED

Theorem no_ctor_zero_section:
  (!pre vis name ty slot post.
    tops = pre ++ VariableDecl vis Immutable name ty slot :: post ==>
    ?tv. FLOOKUP (get_source_immutables NONE imms) name =
      SOME (tv, default_value tv) /\
      immutable_value_admissible tv (default_value tv) /\
      type_memory_size tv =
        type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty) ==>
  immutables_section_rel tops imms (REPLICATE (imm_len tops) 0w)
Proof
  strip_tac >> rewrite_tac[immutables_section_rel_def] >>
  conj_tac >- simp[imm_len_def] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `imm_len tops =
     compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre +
     type_memory_size tv +
     compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) post` by
    simp[imm_len_def, compute_immutables_len_append, compute_immutables_len_def] >>
  qpat_x_assum `tops = _` kall_tac >>
  qexistsl [`tv`, `default_value tv`] >> asm_rewrite_tac[] >>
  qmatch_goalsub_abbrev_tac `compute_immutables_len sf pre` >>
  qmatch_goalsub_abbrev_tac `compute_immutables_len sf post` >>
  qpat_x_assum `type_memory_size tv = _`
    (fn th => rewrite_tac[GSYM th]) >>
  rewrite_tac[GSYM rich_listTheory.REPLICATE_APPEND,
              listTheory.APPEND_ASSOC] >>
  conj_tac
  >- (qspec_then `tv` mp_tac (cj 1 immutable_default_zero_decodes_mutual) >>
      disch_then (qspecl_then
        [`REPLICATE (compute_immutables_len sf pre) 0w`,
         `REPLICATE (compute_immutables_len sf post) 0w`] mp_tac) >> simp[]) >>
  simp[mem_bytes_at_def, rich_listTheory.DROP_APPEND,
       rich_listTheory.TAKE_APPEND, GSYM no_ctor_default_encoding] >>
  `type_memory_size tv -
     (type_memory_size tv + compute_immutables_len sf post) = 0` by decide_tac >>
  simp[listTheory.TAKE_LENGTH_TOO_LONG, encode_immutable_value_length,
       immutable_value_bytes_encoded]
QED

Theorem no_ctor_initial_module_defaults:
  !env src ts acc imms.
    initial_immutables_module env src ts acc = SOME imms ==>
    ((!id tv v. FLOOKUP (get_source_immutables src acc) id = SOME (tv,v) ==>
                  v = default_value tv) ==>
     (!id tv v. FLOOKUP (get_source_immutables src imms) id = SOME (tv,v) ==>
                  v = default_value tv))
Proof
  recInduct initial_immutables_module_ind >>
  simp[initial_immutables_module_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  gen_tac >> strip_tac >>
  first_x_assum drule >> disch_then drule >>
  disch_then assume_tac >> strip_tac >>
  `!key ty value.
     FLOOKUP (get_source_immutables src_id_opt
       (update_immutable src_id_opt id tv (default_value tv) acc)) key =
       SOME (ty,value) ==> value = default_value ty`
    suffices_by metis_tac[] >>
  rpt gen_tac >>
  simp[vyperStateTheory.update_immutable_def,
       get_source_immutables_set_same, finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `key = id` >> simp[] >> metis_tac[]
QED

Theorem no_ctor_initial_defaults:
  initial_immutables env [(NONE,tops)] = SOME imms /\
  FLOOKUP (get_source_immutables NONE imms) id = SOME (tv,v) ==>
  v = default_value tv
Proof
  simp[initial_immutables_def] >> strip_tac >>
  drule no_ctor_initial_module_defaults >>
  gvs[vyperStateTheory.empty_immutables_def,
      vyperStateTheory.get_source_immutables_def] >>
  metis_tac[]
QED

Theorem no_ctor_singleton_type_env:
  type_env_all_modules [(NONE,tops)] = type_env tops
Proof
  simp[vyperContextTheory.type_env_all_modules_def,
       vyperContextTheory.type_env_def]
QED

Theorem no_ctor_checked_decl:
  check_contract T layouts addr [(NONE,tops)] = SOME art /\
  MEM (VariableDecl vis Immutable name ty slot) tops ==>
  assignable_type (type_env tops) ty /\
  contract_namespaces_ok T [(NONE,tops)]
Proof
  strip_tac >>
  `check_toplevel_decl [(NONE,tops)] art NONE
     (VariableDecl vis Immutable name ty slot)` by
    (irule check_contract_toplevel_decl_MEM_checked >>
     simp[] >> metis_tac[]) >>
  gvs[vyperTypeContractTheory.check_toplevel_decl_def,
      no_ctor_singleton_type_env] >>
  metis_tac[check_contract_artifact_fields]
QED

Theorem no_ctor_checked_bare_lookup:
  check_contract T layouts addr [(NONE,tops)] = SOME art /\
  MEM (VariableDecl vis Immutable name ty slot) tops ==>
  FLOOKUP art.cta_bare_globals (NONE,name) = SOME ty
Proof
  strip_tac >> drule check_contract_artifact_fields >> strip_tac >>
  gvs[build_contract_type_artifact_nonsig_mode_irrelevant] >>
  irule build_contract_type_artifact_bare_globals_complete >>
  simp[] >> metis_tac[contract_namespaces_ok_deploy_implies_runtime]
QED

Theorem no_ctor_checked_immutable_types:
  check_contract T layouts addr [(NONE,tops)] = SOME art /\
  MEM (VariableDecl vis Immutable name ty slot) tops ==>
  !vis' ty' slot'.
    MEM (VariableDecl vis' Immutable name ty' slot') tops ==> ty' = ty
Proof
  strip_tac >> drule_all no_ctor_checked_bare_lookup >> strip_tac >>
  qpat_x_assum `MEM (VariableDecl vis Immutable name ty slot) tops` kall_tac >>
  rpt strip_tac >> drule_all no_ctor_checked_bare_lookup >> simp[]
QED

Theorem no_ctor_checked_decl_keys:
  check_contract T layouts addr [(NONE,tops)] = SOME art ==>
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))
Proof
  strip_tac >> drule check_contract_artifact_fields >> strip_tac >>
  irule contract_namespaces_ok_module_toplevel_vtype_keys >>
  qexists `[(NONE,tops)]` >> simp[] >>
  metis_tac[contract_namespaces_ok_deploy_implies_runtime]
QED

Theorem no_ctor_checked_initial_lookup:
  check_contract T layouts addr [(NONE,tops)] = SOME art /\
  MEM (VariableDecl vis Immutable name ty slot) tops /\
  initial_immutables (type_env_all_modules [(NONE,tops)]) [(NONE,tops)] = SOME imms ==>
  ?tv v. FLOOKUP (get_source_immutables NONE imms) name = SOME (tv,v) /\
         evaluate_type (type_env tops) ty = SOME tv
Proof
  strip_tac >>
  `is_immutable_decl name tops` by
    metis_tac[is_immutable_decl_MEM] >>
  `find_var_decl_by_name name tops = NONE` by
    (irule find_var_decl_by_name_NONE_Immutable >>
     metis_tac[no_ctor_checked_decl_keys]) >>
  `IS_SOME (FLOOKUP (get_source_immutables NONE imms) name)` by
    (irule initial_immutables_contains_decl >>
     qexistsl [`[(NONE,tops)]`, `type_env_all_modules [(NONE,tops)]`, `tops`] >>
     simp[]) >>
  Cases_on `FLOOKUP (get_source_immutables NONE imms) name` >> gvs[] >>
  PairCases_on `x` >> simp[] >>
  irule initial_immutables_all_bare_global_type >>
  qexistsl [`name`, `imms`, `[(NONE,tops)]`, `NONE`, `tops`, `x1`] >>
  gvs[no_ctor_singleton_type_env] >>
  metis_tac[no_ctor_checked_immutable_types]
QED

Theorem no_ctor_checked_constants_no_clobber:
  check_contract T layouts addr [(NONE,tops)] = SOME art /\
  MEM (VariableDecl vis Immutable name ty slot) tops ==>
  constants_do_not_clobber_bare_globals [(NONE,tops)]
    (FEMPTY |+ ((NONE,name),ty))
Proof
  strip_tac >>
  drule no_ctor_checked_decl_keys >> strip_tac >>
  rw[constants_do_not_clobber_bare_globals_def,
     finite_mapTheory.FLOOKUP_UPDATE] >>
  gvs[] >>
  metis_tac[module_immutable_constant_names_distinct]
QED


Theorem no_ctor_address_default_admissible:
  immutable_value_admissible (BaseTV AddressT)
     (default_value (BaseTV AddressT))
Proof
  simp[default_value_def, immutable_value_admissible_def,
       no_ctor_zero_address_bytes]
QED

Theorem no_ctor_default_admissible:
  (!tv. well_formed_type_value tv ==>
        immutable_value_admissible tv (default_value tv)) /\
  (!tvs. EVERY well_formed_type_value tvs ==>
         immutable_tuple_admissible tvs (MAP default_value tvs)) /\
  (!fts. EVERY (well_formed_type_value o SND) fts ==>
         immutable_fields_admissible fts
           (MAP (\(id,t). (id, default_value t)) fts))
Proof
  ho_match_mp_tac type_memory_size_ind >>
  rw[vyperTypingTheory.well_formed_type_value_def,
     default_value_def, default_value_tuple_MAP, default_value_struct_MAP,
     immutable_value_admissible_def, no_ctor_zero_address_bytes] >>
  gvs[ETA_THM]
QED

Theorem no_ctor_compile_struct_fields[local]:
  (build_compile_env tops vis mut name args ret (code_stmts:stmt list) trans).ce_struct_fields =
    make_struct_fields_map tops
Proof
  simp[build_compile_env_def] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[]
QED

Theorem no_ctor_checked_type_size:
  check_contract T layouts addr [(NONE,tops)] = SOME art /\
  MEM (VariableDecl vis Immutable name ty slot) tops /\
  evaluate_type (type_env tops) ty = SOME tv ==>
  type_memory_size tv =
    type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty
Proof
  strip_tac >> drule_all no_ctor_checked_decl >> strip_tac >>
  `abi_decoder_coherent
    (build_compile_env tops External Payable "" [] NoneT [] F) (type_env tops)
    (build_compile_env tops External Payable "" [] NoneT [] F).ce_struct_fields
    ty tv` by
    (irule abi_caller_coherent >> metis_tac[]) >>
  drule abiDecoderCoherenceTheory.abi_decoder_coherent_header >>
  simp[abiDecoderCoherenceTheory.abi_decoder_header_def,
       GSYM type_mem_bytes_type_memory_bytes] >>
  simp[no_ctor_compile_struct_fields]
QED

Theorem no_ctor_evaluated_default_admissible:
  evaluate_type env ty = SOME tv ==>
  immutable_value_admissible tv (default_value tv)
Proof
  strip_tac >> irule (cj 1 no_ctor_default_admissible) >>
  metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value]
QED

Theorem no_ctor_constants_preserve_lookup:
  check_contract T layouts addr [(NONE,tops)] = SOME art /\
  MEM (VariableDecl vis Immutable name ty slot) tops /\
  evaluate_all_constants cx am addr [(NONE,tops)] = SOME am_c /\
  FLOOKUP (get_source_immutables NONE
    (case ALOOKUP am.immutables addr of SOME m => m | NONE => [])) name = SOME x ==>
  FLOOKUP (get_source_immutables NONE
    (case ALOOKUP am_c.immutables addr of SOME m => m | NONE => [])) name = SOME x
Proof
  strip_tac >>
  drule_all no_ctor_checked_constants_no_clobber >> strip_tac >>
  irule evaluate_all_constants_preserves_bare_global_lookup_type >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`FEMPTY |+ ((NONE,name),ty)`, `ty`] >>
  gvs[constants_do_not_clobber_bare_globals_def,
      finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem no_ctor_initialized_zero_section:
  deploy_typing_ok tops am tx /\
  initial_immutables (type_env_all_modules [(NONE,tops)]) [(NONE,tops)] = SOME imms /\
  evaluate_all_constants (deploy_evaluation_context tops am tx)
    (am with <| immutables updated_by CONS (tx.target,imms);
                exports updated_by CONS (tx.target,[]) |>)
    tx.target [(NONE,tops)] = SOME am_c ==>
  immutables_section_rel tops
    (case ALOOKUP am_c.immutables tx.target of SOME m => m | NONE => [])
    (REPLICATE (imm_len tops) 0w)
Proof
  strip_tac >>
  `?art. check_contract T am.layouts tx.target [(NONE,tops)] = SOME art` by
    gvs[deploy_typing_ok_def] >>
  pop_assum strip_assume_tac >>
  irule no_ctor_zero_section >> rpt gen_tac >> strip_tac >>
  `MEM (VariableDecl vis Immutable name ty slot) tops` by simp[] >>
  drule_all no_ctor_checked_initial_lookup >> strip_tac >>
  `v = default_value tv` by
    metis_tac[no_ctor_initial_defaults] >>
  gvs[] >>
  qexists `tv` >>
  conj_tac
  >- (irule no_ctor_constants_preserve_lookup >>
      goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  conj_tac
  >- metis_tac[no_ctor_evaluated_default_admissible] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  drule no_ctor_checked_type_size >>
  disch_then irule >>
  conj_tac
  >- (qpat_x_assum `evaluate_type _ _ = SOME tv` mp_tac >>
      pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >> simp[]) >>
  qexistsl [`name`, `slot`, `vis`] >> simp[]
QED

Theorem no_ctor_gas_marks:
  gas_explicit [] readings = []
Proof
  simp[gas_explicit_def]
QED

Theorem no_ctor_constants_ready:
  deploy_typing_ok tops am tx ==>
  ?imms am_c.
    initial_immutables (type_env_all_modules [(NONE,tops)]) [(NONE,tops)] = SOME imms /\
    evaluate_all_constants (deploy_evaluation_context tops am tx)
      (am with <| immutables updated_by CONS (tx.target,imms);
                  exports updated_by CONS (tx.target,[]) |>)
      tx.target [(NONE,tops)] = SOME am_c
Proof
  strip_tac >> gvs[deploy_typing_ok_def] >>
  drule vyperTypeEntryReadinessTheory.checked_deployment_constants_ready_setup >>
  metis_tac[]
QED

Theorem no_ctor_empty_external:
  cx.in_deploy /\
  evaluate_all_constants cx am cx.txn.target mods = SOME am_c /\
  send_call_value Payable cx
    (initial_state am_c [FEMPTY] with
      <| outcomes := orc; requests := []; gas_obs := gobs |>) = (INL (),st) ==>
  call_external_function orc gobs am cx F Payable (tops:toplevel list) mods [] [] [] [] NoneT =
    (INL NoneV,
     abstract_machine_from_state am_c.sources am_c.exports am_c.layouts
       (st with scopes := [FEMPTY]), st.requests)
Proof
  strip_tac >>
  simp[call_external_function_def, bind_arguments_def,
       lock_if_nr_def, unlock_if_nr_def, is_view_mut_def,
       vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.return_def, vyperStateTheory.set_scopes_def,
       evaluate_def]
QED

Theorem no_ctor_send_value:
  value_transfer_ok cx.txn st.accounts ==>
  send_call_value Payable cx st =
    (INL (), st with accounts := accounts_after_transfer cx.txn st.accounts)
Proof
  rw[send_call_value_def, e2eDefsTheory.value_transfer_ok_def,
     e2eDefsTheory.accounts_after_transfer_def,
     vyperStateTheory.return_def, vyperStateTheory.bind_def,
     vyperStateTheory.ignore_bind_def, vyperStateTheory.check_def,
     vyperStateTheory.assert_def, transfer_value_def,
     vyperStateTheory.get_accounts_def, vyperStateTheory.update_accounts_def] >>
  gvs[vyperStateTheory.evaluation_state_component_equality]
QED

Theorem no_ctor_load_reduce:
  classify_functions tops = (exts,ints,fb,NONE) /\
  tx.function_name = "__init__" /\ tx.args = [] /\
  initial_immutables (type_env_all_modules [(NONE,tops)]) [(NONE,tops)] = SOME imms /\
  call_external_function NONE gobs
    (am with <| immutables updated_by CONS (tx.target,imms);
                exports updated_by CONS (tx.target,[]) |>)
    (deploy_evaluation_context tops am tx) F Payable tops [(NONE,tops)]
    [] [] [] [] NoneT = (INL v, am_out, rqs) ==>
  load_contract NONE gobs am tx [(NONE,tops)] [] =
    INL (finalize_pending_deletions
      (am_out with sources updated_by CONS (tx.target,[(NONE,tops)])), rqs)
Proof
  strip_tac >> drule no_ctor_lookup >> strip_tac >>
  gvs[deploy_evaluation_context_def] >> simp[load_contract_def]
QED

Theorem no_ctor_constants_frame:
  evaluate_all_constants cx am addr [(NONE,tops)] = SOME am_c ==>
  am_c.accounts = am.accounts /\ am_c.tStorage = am.tStorage /\
  am_c.logs = am.logs /\ am_c.pending_deletions = am.pending_deletions /\
  am_c.sources = am.sources /\ am_c.exports = am.exports /\
  am_c.layouts = am.layouts
Proof
  simp[evaluate_all_constants_def, constants_order_def,
       evaluate_module_constants_def] >>
  strip_tac >> gvs[AllCaseEqs(), merge_constants_def]
QED

Theorem no_ctor_source_success:
  classify_functions tops = (exts,ints,fb,NONE) /\
  tx.function_name = "__init__" /\ tx.args = [] /\
  initial_immutables (type_env_all_modules [(NONE,tops)]) [(NONE,tops)] = SOME imms /\
  evaluate_all_constants (deploy_evaluation_context tops am tx)
    (am with <| immutables updated_by CONS (tx.target,imms);
                exports updated_by CONS (tx.target,[]) |>)
    tx.target [(NONE,tops)] = SOME am_c /\
  value_transfer_ok tx am.accounts ==>
  load_contract NONE gobs am tx [(NONE,tops)] [] =
    INL (finalize_pending_deletions
      (am_c with <| accounts := accounts_after_transfer tx am.accounts;
                    sources updated_by CONS (tx.target,[(NONE,tops)]) |>), [])
Proof
  strip_tac >> drule no_ctor_constants_frame >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `evaluate_all_constants cx installed` >>
  `cx.in_deploy /\ cx.txn = tx` by
    simp[Abbr `cx`, deploy_evaluation_context_def,
         initial_evaluation_context_def] >>
  `evaluate_all_constants cx installed cx.txn.target [(NONE,tops)] = SOME am_c` by
    gvs[Abbr `cx`, Abbr `installed`] >>
  qabbrev_tac `st0 = initial_state am_c [FEMPTY] with
    <| outcomes := NONE; requests := []; gas_obs := gobs |>` >>
  `value_transfer_ok cx.txn st0.accounts` by simp[Abbr `st0`, initial_state_def] >>
  drule no_ctor_send_value >> strip_tac >>
  `call_external_function NONE gobs installed cx F Payable tops [(NONE,tops)]
    [] [] [] [] NoneT =
    (INL NoneV, am_c with accounts := accounts_after_transfer tx am.accounts, [])` by
    (gvs[Abbr `st0`] >> drule_all no_ctor_empty_external >>
     disch_then (qspec_then `tops` mp_tac) >>
     simp[initial_state_def, abstract_machine_from_state_def,
          abstract_machine_component_equality]) >>
  gvs[Abbr `installed`, Abbr `cx`] >>
  drule no_ctor_load_reduce >> simp[abstract_machine_component_equality]
QED

Theorem no_ctor_source_observations:
  classify_functions tops = (exts,ints,fb,NONE) /\
  deploy_typing_ok tops am tx /\
  tx.function_name = "__init__" /\ tx.args = [] /\
  value_transfer_ok tx am.accounts /\ am.pending_deletions = [] ==>
  ?am'. load_contract NONE gobs am tx [(NONE,tops)] [] = INL (am',[]) /\
    am'.accounts = accounts_after_transfer tx am.accounts /\
    am'.tStorage = am.tStorage /\ am'.logs = am.logs /\
    immutables_section_rel tops (account_immutables am' tx.target)
      (REPLICATE (imm_len tops) 0w)
Proof
  strip_tac >> drule no_ctor_constants_ready >> strip_tac >>
  drule no_ctor_constants_frame >> strip_tac >> gvs[] >>
  drule no_ctor_source_success >> simp[] >>
  disch_then (qspecl_then [`tx`, `gobs`, `am_c`, `am`] mp_tac) >> simp[] >>
  strip_tac >>
  drule no_ctor_initialized_zero_section >> simp[] >>
  strip_tac >>
  gvs[finalize_pending_deletions_def, e2eDefsTheory.account_immutables_def,
      vfmExecutionTheory.process_deletions_def, vyperStateTheory.empty_immutables_def]
QED

Theorem no_ctor_entry_frame:
  deploy_state_rel tops deploy_bc am tx es /\
  gas_variant vs (deploy_entry_state prog cplan tops es) ==>
  vs.vs_accounts = accounts_after_transfer tx am.accounts /\
  vs.vs_transient = am.tStorage /\ vs.vs_logs = []
Proof
  strip_tac >>
  qpat_x_assum `deploy_state_rel _ _ _ _ _` mp_tac >>
  simp[deploy_state_rel_def] >> strip_tac >>
  qpat_x_assum `gas_variant _ _` (mp_tac o SRULE [gas_variant_def]) >>
  disch_then (mp_tac o Q.AP_TERM `\s. (s.vs_accounts, s.vs_transient, s.vs_logs)`) >>
  simp[deploy_entry_state_def, entry_venom_state_def, init_venom_state_def] >>
  metis_tac[]
QED

Theorem no_ctor_source_halt:
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es /\
  gas_variant vs (deploy_entry_state prog cplan tops es) /\
  classify_functions tops = (exts,ints,fb,NONE) /\
  ss.vs_returndata = runtime_bc ++ REPLICATE (imm_len tops) 0w /\
  ss.vs_accounts = vs.vs_accounts /\
  ss.vs_transient = vs.vs_transient /\ ss.vs_logs = vs.vs_logs ==>
  ?marks. deploy_venom_result_rel tops runtime_bc tx
    (load_contract NONE (gas_explicit marks vs.vs_gas_readings) am tx [(NONE,tops)] [])
    (Halt ss)
Proof
  strip_tac >> drule_all no_ctor_entry_frame >> strip_tac >>
  `tx.args = []` by
    (gvs[deploy_state_rel_def] >> drule_all no_ctor_args >> simp[]) >>
  `deploy_typing_ok tops am tx /\ tx.function_name = "__init__" /\
    value_transfer_ok tx am.accounts /\ am.pending_deletions = [] /\ am.logs = []` by
    gvs[deploy_source_ok_def, deploy_state_rel_def] >>
  drule no_ctor_source_observations >> simp[] >>
  disch_then (qspecl_then [`tx`, `[]`, `am`] mp_tac) >> simp[] >> strip_tac >>
  qexists `[]` >>
  simp[no_ctor_gas_marks, deploy_venom_result_rel_def] >>
  gvs[loweringStateRelDefsTheory.storage_agree_def, loweringStateRelDefsTheory.transient_agree_def,
      e2eDefsTheory.logs_correspond_def,
      vfmStateTheory.account_state_component_equality]
QED

(* Without a constructor, load_contract runs the synthetic empty one, and the
   unit is compile_simple_deploy's. *)
Theorem deploy_no_ctor_correct:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs exts ints fb.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    classify_functions tops = (exts, ints, fb, NONE)
    ==>
    ?marks.
      deploy_source_exempt tops
        (load_contract NONE (gas_explicit marks vs.vs_gas_readings) am tx
           [(NONE, tops)] []) \/
      ?fuel. deploy_venom_result_rel tops runtime_bc tx
               (load_contract NONE (gas_explicit marks vs.vs_gas_readings) am tx
                  [(NONE, tops)] [])
               (run_context fuel dunit.cu_context vs)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all no_ctor_target_execution >> strip_tac >>
  drule_all no_ctor_source_halt >> strip_tac >>
  qexists_tac `marks` >> disj2_tac >> qexists_tac `fuel` >>
  asm_rewrite_tac[]
QED
