Theory bodyPtrPopTraceReplay
Ancestors bodyPtrPopTraceBoundary ptrDiscipline vyperValue venomState finite_map list rich_list

Theorem pop_trace_sub13_inst:
  pop_trace_inst 13 = <|inst_id := 13; inst_opcode := SUB;
    inst_operands := [Var "%8"; Lit 1w]; inst_outputs := ["%11"]|>
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Theorem pop_trace_sub13_success:
  ?u. step_inst_base (pop_trace_inst 13) (pop_trace_state 13) = OK u
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >>
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem pop_trace_store_value_clean:
  op_taint (pop_trace_taint 14) (Var "%11") = {}
Proof
  mp_tac pop_trace_sub13_success >> strip_tac >>
  `14 = SUC 13` by simp[] >> pop_assum SUBST1_TAC >>
  rewrite_tac[Once pop_trace_taint_def] >> simp[] >>
  simp[op_taint_def, step_taint_def, set_var_taint_def,
    pop_trace_sub13_inst, FLOOKUP_UPDATE, out_taint_def] >>
  CASE_TAC >> simp[]
QED

Theorem pop_trace_boundary_storage_empty:
  (pop_trace_taint 23).t_stor = {}
Proof
  rewrite_tac[pop_trace_boundary_storage_residual,
    pop_trace_store_value_clean] >>
  Cases_on `step_inst_base (pop_trace_inst 14) (pop_trace_state 14)` >>
  simp[key_update_def]
QED

Theorem pop_trace_code_length:
  LENGTH pop_saved_code = 37
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Theorem pop_step_prov_empty:
  inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> DALLOCA /\
  inst.inst_opcode <> PARAM ==>
  step_prov PG FEMPTY inst s = FEMPTY
Proof
  strip_tac >> simp[step_prov_def, out_prov_def] >>
  `!ops. first_prov FEMPTY ops = NONE` by
    (Induct >> simp[first_prov_def, op_prov_def] >> Cases_on `h` >>
     simp[op_prov_def]) >>
  simp[set_prov_def, DRESTRICT_FEMPTY] >>
  Cases_on `inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/
    inst.inst_opcode = ASSIGN` >> simp[set_prov_def, DRESTRICT_FEMPTY] >>
  Cases_on `inst.inst_outputs` >> simp[]
QED


Theorem pop_trace_code_no_alloc:
  EVERY (\i. i.inst_opcode <> ALLOCA /\ i.inst_opcode <> DALLOCA /\
    i.inst_opcode <> PARAM) pop_saved_code
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Theorem pop_trace_prov_opcode:
  n < 37 ==>
  (pop_trace_inst n).inst_opcode <> ALLOCA /\
  (pop_trace_inst n).inst_opcode <> DALLOCA /\
  (pop_trace_inst n).inst_opcode <> PARAM
Proof
  strip_tac >> mp_tac pop_trace_code_no_alloc >>
  simp[EVERY_MEM] >> strip_tac >>
  first_x_assum irule >> simp[pop_trace_inst_def, EL_MEM, pop_trace_code_length]
QED

Theorem pop_trace_prov_empty:
  !n. n <= 37 ==> pop_trace_prov n = FEMPTY
Proof
  Induct >- simp[pop_trace_prov_def] >> strip_tac >>
  `n < 37 /\ n <= 37` by decide_tac >>
  drule pop_trace_prov_opcode >> strip_tac >>
  rewrite_tac[Once pop_trace_prov_def] >>
  Cases_on `step_inst_base (pop_trace_inst n) (pop_trace_state n)` >>
  simp[pop_step_prov_empty]
QED

Theorem pop_trace_final_operand_provenance:
  op_prov (pop_trace_prov 37) (FST pop_saved_lowered) = NONE /\
  op_prov (pop_trace_prov 37) (FST (FST pop_saved_cut)) = NONE
Proof
  simp[pop_trace_prov_empty] >>
  Cases_on `FST pop_saved_lowered` >>
  Cases_on `FST (FST pop_saved_cut)` >> simp[op_prov_def]
QED
