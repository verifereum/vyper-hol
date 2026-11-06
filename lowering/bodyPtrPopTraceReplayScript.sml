Theory bodyPtrPopTraceReplay
Ancestors bodyPtrPopTraceBoundary bodyPtrPopEmptyTaint ptrDiscipline vyperValue venomState finite_map list rich_list

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

Theorem pop_trace_tail_no_store:
  EVERY (\i. i.inst_opcode <> SSTORE /\ i.inst_opcode <> CALL)
    (DROP 23 pop_saved_code)
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Theorem pop_trace_tail_opcode:
  23 <= n /\ n < 37 ==>
  (pop_trace_inst n).inst_opcode <> SSTORE /\
  (pop_trace_inst n).inst_opcode <> CALL
Proof
  strip_tac >> mp_tac pop_trace_tail_no_store >>
  simp[EVERY_MEM] >> strip_tac >> first_x_assum irule >>
  simp[pop_trace_inst_def, MEM_EL] >> qexists_tac `n - 23` >>
  simp[LENGTH_DROP, pop_trace_code_length, EL_DROP]
QED

Theorem pop_trace_storage_final:
  !n. 23 <= n /\ n <= 37 ==> (pop_trace_taint n).t_stor = {}
Proof
  Induct >- simp[] >> strip_tac >>
  Cases_on `SUC n = 23` >- simp[pop_trace_boundary_storage_empty] >>
  `23 <= n /\ n < 37 /\ n <= 37` by decide_tac >>
  drule_all pop_trace_tail_opcode >> strip_tac >>
  simp[pop_trace_storage_frame]
QED

Theorem pop_step_taint_transient_frame:
  inst.inst_opcode <> TSTORE /\ inst.inst_opcode <> CALL ==>
  (step_taint inst s s' tn).t_trans = tn.t_trans
Proof
  simp[step_taint_def, store_taint_def, adopt_reset_def]
QED

Theorem pop_trace_no_transient_store:
  EVERY (\i. i.inst_opcode <> TSTORE /\ i.inst_opcode <> CALL)
    pop_saved_code
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Theorem pop_trace_transient_opcode:
  n < 37 ==> (pop_trace_inst n).inst_opcode <> TSTORE /\
    (pop_trace_inst n).inst_opcode <> CALL
Proof
  strip_tac >> mp_tac pop_trace_no_transient_store >>
  simp[EVERY_MEM] >> strip_tac >> first_x_assum irule >>
  simp[pop_trace_inst_def, EL_MEM, pop_trace_code_length]
QED

Theorem pop_trace_transient_empty:
  !n. n <= 37 ==> (pop_trace_taint n).t_trans = {}
Proof
  Induct >- simp[pop_trace_taint_def, entry_taint_def] >> strip_tac >>
  `n < 37 /\ n <= 37` by decide_tac >>
  drule pop_trace_transient_opcode >> strip_tac >>
  rewrite_tac[Once pop_trace_taint_def] >>
  Cases_on `step_inst_base (pop_trace_inst n) (pop_trace_state n)` >>
  simp[pop_step_taint_transient_frame]
QED

Theorem pop_trace_storage_empty:
  !n. n <= 37 ==> (pop_trace_taint n).t_stor = {}
Proof
  rpt strip_tac >> Cases_on `n <= 14`
  >- simp[pop_trace_storage_before_store] >>
  Cases_on `n <= 23`
  >- (`15 <= n /\ 15 <= 23` by decide_tac >>
      mp_tac pop_trace_boundary_storage_empty >>
      simp[pop_trace_storage_after_store]) >>
  simp[pop_trace_storage_final]
QED

Theorem pop_out_taint_register_clean:
  inst.inst_opcode <> MLOAD /\ inst.inst_opcode <> ILOAD /\
  tn.t_stor = {} /\ tn.t_trans = {} /\
  (!u m. FLOOKUP tn.t_var u = SOME m ==> m = {}) ==>
  out_taint tn inst s = {}
Proof
  strip_tac >> drule pop_op_taint_empty >> strip_tac >>
  Cases_on `inst.inst_operands` >- simp[out_taint_def] >>
  Cases_on `t` >-
    (Cases_on `eval_operand h s` >>
     simp[out_taint_def, key_taint_def]) >>
  Cases_on `t'` >-
    (Cases_on `eval_operand h s` >>
     simp[out_taint_def, shift_taint_def]) >>
  simp[out_taint_def]
QED

Theorem pop_trace_no_memory_load:
  EVERY (\i. i.inst_opcode <> MLOAD /\ i.inst_opcode <> ILOAD)
    pop_saved_code
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Theorem pop_trace_load_opcode:
  n < 37 ==> (pop_trace_inst n).inst_opcode <> MLOAD /\
    (pop_trace_inst n).inst_opcode <> ILOAD
Proof
  strip_tac >> mp_tac pop_trace_no_memory_load >>
  simp[EVERY_MEM] >> strip_tac >> first_x_assum irule >>
  simp[pop_trace_inst_def, EL_MEM, pop_trace_code_length]
QED

Theorem pop_trace_register_clean:
  !n. n <= 37 ==>
    !u m. FLOOKUP (pop_trace_taint n).t_var u = SOME m ==> m = {}
Proof
  Induct >- simp[pop_trace_taint_def, entry_taint_def] >>
  strip_tac >> `n < 37 /\ n <= 37` by decide_tac >>
  drule pop_trace_load_opcode >> strip_tac >>
  first_x_assum (drule_then assume_tac) >>
  `out_taint (pop_trace_taint n) (pop_trace_inst n) (pop_trace_state n) = {}` by
    (irule pop_out_taint_register_clean >>
     simp[pop_trace_storage_empty, pop_trace_transient_empty] >>
     metis_tac[]) >>
  rewrite_tac[Once pop_trace_taint_def] >>
  Cases_on `step_inst_base (pop_trace_inst n) (pop_trace_state n)` >>
  simp[step_taint_def] >> metis_tac[pop_set_var_taint_empty]
QED

Theorem pop_trace_final_operand_taint:
  op_taint (pop_trace_taint 37) (FST pop_saved_lowered) = {} /\
  op_taint (pop_trace_taint 37) (FST (FST pop_saved_cut)) = {}
Proof
  conj_tac >> irule pop_op_taint_empty >>
  mp_tac (Q.SPEC `37` pop_trace_register_clean) >> simp[]
QED
