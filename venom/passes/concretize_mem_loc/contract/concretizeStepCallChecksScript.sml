Theory concretizeStepCallChecks
Ancestors
  concretizeStepStructure fmpStepCallEnvironment fmpStepFlagTransport
  dftCallChecks unitShapeDefs venomEffects
  concretizeMemLocDefs passSharedDefs passSimulationDefs venomInst venomWf list
  passTransform

Theorem concretize_positions_not_invoke:
  i.inst_opcode <> INVOKE ==>
  (concretize_inst_with_positions p i).inst_opcode <> INVOKE
Proof
  rw[concretize_inst_with_positions_def] >> rpt CASE_TAC >>
  simp[mk_assign_inst_def, mk_nop_inst_def]
QED

Theorem concretize_positions_revert_path:
  wf_function fn ==>
  !n l. revert_path fn.fn_blocks n l ==>
    revert_path (concretize_function_with_positions p fn).fn_blocks n l
Proof
  strip_tac >> match_mp_tac revert_path_block_witness_transport >>
  rpt gen_tac >> disch_tac >>
  qexists `clear_nops_block
    (block_map_transform (concretize_inst_with_positions p) bb)` >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  simp[concretize_positions_blocks, MEM_MAP, concretize_positions_block_label,
       concretize_positions_block_last] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[concretize_positions_block_terminal_decomp] >>
  simp[clear_nops_block_def, block_map_transform_def, EVERY_FILTER, EVERY_MAP] >>
  fs[EVERY_MEM] >> metis_tac[concretize_positions_not_invoke]
QED

Theorem concretize_positions_flag_fails_environment:
  wf_function fn ==>
  !vs i. flag_fails fn.fn_blocks vs i ==>
    flag_fails (concretize_function_with_positions p fn).fn_blocks vs i
Proof
  strip_tac >> match_mp_tac flag_fails_revert_environment >>
  simp[concretize_positions_block_count, concretize_positions_revert_path]
QED

Theorem concretize_positions_flag_step:
  (concretize_inst_with_positions p i).inst_opcode <> NOP ==>
  flag_step (concretize_inst_with_positions p i) vs = flag_step i vs
Proof
  rw[concretize_inst_with_positions_def] >> rpt CASE_TAC >>
  gvs[mk_assign_inst_def, mk_nop_inst_def, flag_step_def,
      write_effects_def]
QED

Theorem concretize_positions_deleted_flag_step:
  (concretize_inst_with_positions p i).inst_opcode = NOP ==>
  !v. MEM v (flag_step i vs) ==> MEM v vs
Proof
  rw[concretize_inst_with_positions_def] >> rpt CASE_TAC >>
  gvs[mk_assign_inst_def, mk_nop_inst_def, flag_step_def,
      write_effects_def, MEM_FILTER]
QED

Theorem concretize_positions_flag_fails_inst:
  flag_fails bbs vs i ==>
  concretize_inst_with_positions p i = i /\ i.inst_opcode <> NOP
Proof
  Cases_on `i.inst_opcode = ALLOCA` >-
    simp[flag_fails_def] >>
  Cases_on `i.inst_opcode = NOP` >- simp[flag_fails_def] >>
  simp[concretize_positions_unchanged]
QED

Theorem concretize_positions_flag_path:
  !xs vs. wf_function fn /\ flag_path fn.fn_blocks vs xs ==>
  flag_path (concretize_function_with_positions p fn).fn_blocks vs
    (FILTER (\i. i.inst_opcode <> NOP)
      (MAP (concretize_inst_with_positions p) xs))
Proof
  Induct >- simp[flag_path_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `flag_path _ _ _` mp_tac >>
  rewrite_tac[flag_path_cons_step] >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  Cases_on `flag_fails fn.fn_blocks vs h`
  >- (drule concretize_positions_flag_fails_inst >> strip_tac >>
      simp[flag_path_cons_step] >> disj1_tac >>
      metis_tac[concretize_positions_flag_fails_environment]) >>
  `flag_path (concretize_function_with_positions p fn).fn_blocks
     (flag_step h vs)
     (FILTER (\i. i.inst_opcode <> NOP)
       (MAP (concretize_inst_with_positions p) xs))` by metis_tac[] >>
  Cases_on `(concretize_inst_with_positions p h).inst_opcode = NOP`
  >- (simp[] >> irule flag_path_mono >>
      qexists `flag_step h vs` >>
      simp[] >> metis_tac[concretize_positions_deleted_flag_step]) >>
  simp[flag_path_cons_step, concretize_positions_not_invoke,
       concretize_positions_flag_step]
QED

Theorem concretize_positions_call_opcode:
  ((concretize_inst_with_positions p i).inst_opcode = CALL <=>
    i.inst_opcode = CALL) /\
  ((concretize_inst_with_positions p i).inst_opcode = STATICCALL <=>
    i.inst_opcode = STATICCALL)
Proof
  rw[concretize_inst_with_positions_def] >> rpt CASE_TAC >>
  simp[mk_assign_inst_def, mk_nop_inst_def]
QED

Theorem concretize_positions_calls_flagged:
  !xs. wf_function fn /\ calls_flagged fn.fn_blocks xs ==>
  calls_flagged (concretize_function_with_positions p fn).fn_blocks
    (FILTER (\i. i.inst_opcode <> NOP)
      (MAP (concretize_inst_with_positions p) xs))
Proof
  Induct >- simp[calls_flagged_def] >>
  rpt strip_tac >>
  `calls_flagged (concretize_function_with_positions p fn).fn_blocks
    (FILTER (\i. i.inst_opcode <> NOP)
      (MAP (concretize_inst_with_positions p) xs))` by
    (fs[calls_flagged_def] >> metis_tac[]) >>
  Cases_on `(concretize_inst_with_positions p h).inst_opcode = NOP`
  >- simp[] >>
  simp[calls_flagged_def, concretize_positions_call_opcode] >>
  strip_tac >>
  `concretize_inst_with_positions p h = h` by
    (irule concretize_positions_unchanged >> simp[]) >>
  gvs[] >>
  qpat_x_assum `calls_flagged _ (h::xs)` mp_tac >>
  simp[calls_flagged_def] >>
  Cases_on `h.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >> strip_tac >>
  irule concretize_positions_flag_path >> simp[]
QED

Theorem concretize_positions_call_checks:
  wf_function fn /\ call_checks_ok fn ==>
  call_checks_ok (concretize_function_with_positions p fn)
Proof
  strip_tac >> simp[call_checks_ok_def, EVERY_MEM] >> rpt strip_tac >>
  qpat_x_assum `MEM _ (concretize_function_with_positions _ _).fn_blocks`
    (mp_tac o REWRITE_RULE [concretize_positions_blocks]) >>
  simp[MEM_MAP] >> strip_tac >> gvs[] >>
  simp[clear_nops_block_def, block_map_transform_def] >>
  irule concretize_positions_calls_flagged >>
  fs[call_checks_ok_def, EVERY_MEM] >> metis_tac[]
QED
