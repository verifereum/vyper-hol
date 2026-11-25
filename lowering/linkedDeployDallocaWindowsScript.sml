(* The generator covers the main constructor and the actual ordered
   internal packages, including imported constructors. *)
Theory linkedDeployDallocaWindows
Ancestors
  runtimePeakMemoryStmtAll runtimePeakMemoryRuntime deployPeakMemoryBound
  runtimePeakMemoryCode compileUnit compileVyper moduleLowering
  vyperCompiler stmtLowering compileEnv venomInst list pair option

Theorem lower_vyper_deploy_unit_dalloca_windows_mods:
  (!chunk. raw_call_dalloca_chunk chunk 1 ==> window chunk 1) /\
  (!chunk. create_copy_dalloca_chunk chunk 5 ==> window chunk 5) /\
  (!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) /\
  lower_vyper_deploy_unit_mods mods exps rp runtime_bc = SOME unit ==>
  !fn bb. MEM fn unit.cu_context.ctx_functions /\ MEM bb fn.fn_blocks ==>
    dalloca_windows window bb.bb_instructions
Proof
  strip_tac >>
  `!ce lc ty ss. preserves_dalloca_windows window (compile_stmts ce lc ty ss)` by
    (qspec_then `window` mp_tac (GEN_ALL dalloca_windows_compile_stmts_all) >>
     simp[]) >>
  `!has sz ilen args data_size ints ce ss pay nr key tr.
     preserves_dalloca_windows window
       (compile_generate_deploy has sz ilen args data_size ints ce ss pay nr key tr)` by
    (rpt gen_tac >> irule dalloca_windows_generate_deploy >>
     simp[EVERY_MEM] >> disch_tac >> qx_gen_tac `pkg` >> PairCases_on `pkg` >>
     simp[] >> strip_tac >> irule dalloca_windows_internal_function >> simp[]) >>
  qpat_x_assum `lower_vyper_deploy_unit_mods _ _ _ _ = _` mp_tac >>
  simp[lower_vyper_deploy_unit_mods_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[bool_case_eq] >>
  rpt strip_tac >>
  irule run_deploy_lowering_dalloca_windows >>
  qpat_assum `run_deploy_lowering _ _ _ _ _ _ _ _ _ _ _ _ _ _ = SOME _`
    (irule_at Any) >> qexists_tac `fn` >> simp[]
QED
