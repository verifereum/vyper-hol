(* Pointer and memory checks ignore the outcome oracle in a call-free entry. *)
Theory deployOutcomesFreeSafety
Ancestors
  deployOutcomesFreeStep deployOutcomesFreeFrames
  loweringBudgetFrameOracleTransport loweringBudgetNonconsumingOracleTransport
  ptrSafeRun ptrDiscipline memSafeRun contextCodegenRel codegenRel
  ctxLookupAgreeHelpers venomExecSemantics venomState venomInst list
  unitTransformDefs dftCommutation

Theorem outcomes_memory_checks[simp]:
  (inst_mem_below_frontier inst (s with vs_outcomes := os) =
    inst_mem_below_frontier inst s) /\
  (inst_dload_in_section inst (s with vs_outcomes := os) =
    inst_dload_in_section inst s)
Proof
  simp[inst_mem_below_frontier_def, inst_dload_in_section_def,
       outcomes_memory_read_ranges, write_ranges_outcomes_update,
       operand_outcomes_update, eval_operands_outcomes_update]
QED

Theorem outcomes_mem_safe_step:
  inst.inst_opcode <> INVOKE ==>
  mem_safe_step fuel ctx inst (s with vs_outcomes := os) =
    mem_safe_step fuel ctx inst s
Proof
  simp[mem_safe_step_def]
QED

Theorem outcomes_ghost_step:
  ~MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE] ==>
  ghost_step fuel ctx PG G tn inst (s with vs_outcomes := os) =
    ghost_step fuel ctx PG G tn inst s
Proof
  strip_tac >> simp[ghost_step_def, outcomes_step_inst] >>
  Cases_on `step_inst fuel ctx inst s` >>
  gvs[MEM, dftCommutationTheory.map_result_state_def,
       step_prov_outcomes_update, step_taint_noncall_outcomes_update]
QED

Theorem outcomes_ptr_inst_ok:
  ~MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE] ==>
  ptr_inst_ok D lo fuel ctx fn G tn inst (s with vs_outcomes := os) =
    ptr_inst_ok D lo fuel ctx fn G tn inst s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, outcomes_state_predicates, outcomes_step_inst] >>
  Cases_on `step_inst fuel ctx inst s` >>
  gvs[MEM, dftCommutationTheory.map_result_state_def,
       step_taint_noncall_outcomes_update, ret_taint_def,
       operand_outcomes_update, eval_operands_outcomes_update]
QED

Theorem outcomes_ptr_safe_defs:
  (!D lo fuel ctx fn PG G tn inst s os.
    ~MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE] ==>
    ptr_safe_step D lo fuel ctx fn PG G tn inst (s with vs_outcomes := os) =
      ptr_safe_step D lo fuel ctx fn PG G tn inst s) /\
  (!D lo fuel ctx fn PG G tn bb s.
    EVERY (\inst. ~MEM inst.inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts fn) /\
    EVERY (\inst. ~MEM inst.inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) bb.bb_instructions ==>
    !os. ptr_safe_block D lo fuel ctx fn PG G tn bb (s with vs_outcomes := os) =
      ptr_safe_block D lo fuel ctx fn PG G tn bb s) /\
  (!D lo fuel ctx fn PG G tn s.
    EVERY (\inst. ~MEM inst.inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts fn) ==>
    !os. ptr_safe_blocks D lo fuel ctx fn PG G tn (s with vs_outcomes := os) =
      ptr_safe_blocks D lo fuel ctx fn PG G tn s)
Proof
  ho_match_mp_tac ptr_safe_defs_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      simp[ptr_safe_step_def, outcomes_ptr_inst_ok])
  >- (rpt gen_tac >> strip_tac >> strip_tac >> gen_tac >>
      once_rewrite_tac[ptr_safe_block_def] >> simp[] >>
      Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
      rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
      `~MEM inst.inst_opcode
        [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]` by
        (drule_all EVERY_get_instruction >> simp[]) >>
      simp[outcomes_ptr_inst_ok, outcomes_step_inst, outcomes_ghost_step] >>
      Cases_on `step_inst fuel ctx inst s` >>
      simp[dftCommutationTheory.map_result_state_def] >>
      Cases_on `is_terminator inst.inst_opcode` >> simp[]
      >>~- ([`OK s1`], Cases_on `s1.vs_halted` >>
        gvs[venom_state_fupdcanon, entry_prov_outcomes_update,
            entry_taint_outcomes_update]) >>
      gvs[venom_state_fupdcanon, entry_prov_outcomes_update,
          entry_taint_outcomes_update]) >>
  rpt gen_tac >> strip_tac >> strip_tac >> gen_tac >>
  Cases_on `fuel` >> once_rewrite_tac[ptr_safe_blocks_def] >> simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  `EVERY (\inst. ~MEM inst.inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) bb.bb_instructions` by
    (drule_all EVERY_fn_lookup_block >> simp[]) >>
  simp[outcomes_eval_phis] >> Cases_on `eval_phis s bb.bb_instructions` >>
  gvs[map_result_state_def, venom_state_fupdcanon]
QED
