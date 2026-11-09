Theory entryRegistrationOpen
Ancestors
  exprOpenTerminals exprOpenPrimitives moduleLowering abiEncoder compileEnv
  emitHelper venomInst list pair

Theorem registration_clamp_open[local]:
  !cl op a x b. ~block_is_terminated a /\
    compile_abi_clamp_basetype op cl a = (x,b) ==> ~block_is_terminated b
Proof
  Cases >> rpt gen_tac >>
  TRY (rename1 `IntClamp bits signed` >> Cases_on `signed`) >>
  simp[compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
       compile_abi_bytes_clamp_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, LET_THM, COND_RAND] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac emit_void_terminated >> gvs[is_terminator_def]
QED

Theorem registration_decode_open[local]:
  !args ce off a x b. ~block_is_terminated a /\
    compile_decode_args ce args off CALLDATALOAD (Lit 0w) 4 a = (x,b) ==>
    ~block_is_terminated b
Proof
  Induct >> simp[compile_decode_args_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_decode_args_def, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  rpt strip_tac >> Cases_on `h1` >> Cases_on `h2` >>
  Cases_on `FLOOKUP ce.ce_vars h0` >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  TRY (rename1 `var_location_decode_operand loc` >>
       Cases_on `var_location_decode_operand loc`) >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac emit_op_nonterminator_open >>
  imp_res_tac registration_clamp_open >>
  imp_res_tac compile_abi_decode_to_buf_open >>
  imp_res_tac emit_void_terminated >>
  gvs[is_terminator_def] >> metis_tac[]
QED

Theorem registration_preserves_open:
  !pos ce off a cef b. ~block_is_terminated a /\
    compile_register_positional_args ce pos off a = (cef,b) ==>
    ~block_is_terminated b
Proof
  Induct >> simp[compile_register_positional_args_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_register_positional_args_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt strip_tac >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> gvs[]
  >- metis_tac[] >>
  Cases_on `var_location_memory_size x` >> gvs[]
  >- metis_tac[] >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[registration_decode_open, compile_alloc_buffer_open]
QED

Theorem entry_checks_preserve_open:
  !mincd pay a b. ~block_is_terminated a /\
    compile_entry_checks mincd pay a = ((),b) ==>
    ~block_is_terminated b
Proof
  rpt gen_tac >> Cases_on `pay` >> Cases_on `mincd > 4` >>
  simp[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac emit_void_terminated >> gvs[is_terminator_def]
QED

Theorem entry_checks_registration_open:
  !checks mincd pay start ce pos cenv registered.
    ~block_is_terminated checks /\
    compile_entry_checks mincd pay checks = ((),start) /\
    compile_register_positional_args ce pos 4 start = (cenv,registered) ==>
    ~block_is_terminated registered
Proof
  metis_tac[entry_checks_preserve_open, registration_preserves_open]
QED
