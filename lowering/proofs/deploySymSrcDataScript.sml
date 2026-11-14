Theory deploySymSrcData
Ancestors
  runtimeSymSrcData runtimeSymSrcDataModule runtimeSymSrcDataABI
  runtimeSymSrcDataContext runtimeSymSrcDataFrame moduleLowering
  compileVyper vyperCompiler compileEnv

Theorem runtime_data_frame_register_constructor_args:
  !args cenv off sz.
    runtime_data_frame (compile_register_constructor_args cenv args off sz)
Proof
  Induct >> simp[compile_register_constructor_args_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_register_constructor_args_def] >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >> simp[] >>
  Cases_on `var_location_memory_size x` >> simp[comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- simp[] >>
       gen_tac >> BETA_TAC) >>
  simp[runtime_data_frame_decode_args, runtime_data_frame_abi_decode_to_buf]
QED

Theorem runtime_data_frame_constructor_epilogue[simp]:
  runtime_data_frame (compile_constructor_epilogue sz len buf)
Proof
  simp[compile_constructor_epilogue_def, comp_ignore_bind_def] >>
  IF_CASES_TAC >> simp[] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- simp[] >>
       gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_simple_deploy[simp]:
  runtime_data_frame (compile_simple_deploy sz len)
Proof
  simp[compile_simple_deploy_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- simp[] >>
       gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_generate_deploy:
  runtime_data_frame
    (compile_generate_deploy ctor sz len args ds int cenv stmts payable nr key trans)
Proof
  Cases_on `ctor` >> simp[compile_generate_deploy_def, comp_ignore_bind_def] >>
  Cases_on `cenv.ce_nonreentrant` >> PairCases_on `r` >> simp[] >>
  rpt (FIRST
    [match_mp_tac runtime_data_frame_bind >> conj_tac >- simp[comp_ignore_bind_def,
       runtime_data_frame_register_constructor_args,
       runtime_data_frame_statements, runtime_data_frame_internal_fn_bodies,
       runtime_data_frame_internal_function] >> gen_tac >> BETA_TAC,
     IF_CASES_TAC >> simp[comp_ignore_bind_def]]) >>
  simp[runtime_data_frame_register_constructor_args,
       runtime_data_frame_statements, runtime_data_frame_internal_fn_bodies,
       runtime_data_frame_internal_function]
QED

Theorem run_deploy_lowering_data:
  run_deploy_lowering ctor policy bc len args ds int cenv stmts payable nr key trans entry = SOME u ==>
  u.cu_data_segment =
    [<| ds_label := "runtime_begin"; ds_items := [DataBytes bc] |>]
Proof
  simp[run_deploy_lowering_def] >> strip_tac >>
  qpat_x_assum `_ = SOME u` mp_tac >>
  pairarg_tac >> gvs[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule extract_context_with_internals_data >> strip_tac >>
  mp_tac (REWRITE_RULE [runtime_data_frame_def]
    (runtime_data_frame_generate_deploy |> Q.INST [`sz` |-> `LENGTH (bc:word8 list)`])) >>
  disch_then (qspec_then `initial_compile_state entry` mp_tac) >>
  simp[initial_compile_state_def] >> gvs[]
QED

Theorem lower_vyper_deploy_unit_data_bytes:
  lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME unit ==>
  EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                       ds.ds_items) unit.cu_data_segment
Proof
  simp[lower_vyper_deploy_unit_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> rpt strip_tac >>
  drule run_deploy_lowering_data >> simp[]
QED
