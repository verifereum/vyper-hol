(* Entry checks and registration leave an open body-start block. *)
Theory entryRegistrationOpen
Ancestors
  moduleLowering exprOpenTerminals exprOpenPrimitives stmtSimDeclMem abiEncoder compileEnv venomInst list

Theorem entry_checks_open:
  compile_entry_checks mc pay sa = ((),sb) /\ ~block_is_terminated sa ==>
  ~block_is_terminated sb
Proof
  simp[compile_entry_checks_def, comp_ignore_bind_def, comp_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >>
  Cases_on `pay` >> Cases_on `mc > 4` >>
  gvs[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[emit_void_nonterminator_open, is_terminator_def]
QED

Theorem abi_clamp_open[local]:
  !clamp op sa u sb.
  ~block_is_terminated sa /\ compile_abi_clamp_basetype op clamp sa = (u,sb) ==>
  ~block_is_terminated sb
Proof
  Cases >> simp[compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
    compile_abi_bytes_clamp_def, comp_return_def] >> rpt gen_tac >>
  simp[comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  gvs[AllCaseEqs(), comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  all_tac
  >~ [`(if signed then _ else _) sa = _`]
  >- (Cases_on `signed` >> gvs[comp_bind_def, comp_ignore_bind_def] >>
      rpt (pairarg_tac >> gvs[]) >>
      metis_tac[emit_void_nonterminator_open, is_terminator_def]) >>
  metis_tac[emit_void_nonterminator_open, is_terminator_def]
QED

Theorem decode_args_open[local]:
  !args ce off hi base sa u sb.
  compile_decode_args ce args off CALLDATALOAD hi base sa = (u,sb) ==>
  ~block_is_terminated sa ==>
  ~block_is_terminated sb
Proof
  Induct >> simp[compile_decode_args_def, comp_return_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[compile_decode_args_def] >>
  Cases_on `h1` >> Cases_on `h2` >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  gvs[AllCaseEqs(), comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> gvs[comp_return_def] >>
  Cases_on `var_location_decode_operand x` >> gvs[comp_return_def] >>
  gvs[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  first_x_assum drule >> disch_then irule >>
  imp_res_tac emit_op_nonterminator_open >> gvs[is_terminator_def] >>
  metis_tac[abi_clamp_open, emit_void_nonterminator_open,
    compile_abi_decode_to_buf_open, is_terminator_def]
QED

Theorem register_positional_args_open:
  !args ce off sa cef sb.
  ~block_is_terminated sa /\
  compile_register_positional_args ce args off sa = (cef,sb) ==>
  ~block_is_terminated sb
Proof
  Induct >> simp[compile_register_positional_args_def, comp_return_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[compile_register_positional_args_def] >> strip_tac >>
  gvs[AllCaseEqs(), comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> gvs[]
  >- metis_tac[] >>
  Cases_on `var_location_memory_size x` >>
  gvs[comp_ignore_bind_def, comp_bind_def, comp_return_def]
  >- metis_tac[] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule compile_alloc_buffer_open >> strip_tac >>
  drule_all decode_args_open >> strip_tac >>
  metis_tac[]
QED
