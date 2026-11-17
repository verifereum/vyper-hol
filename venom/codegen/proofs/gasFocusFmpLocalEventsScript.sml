(* Finite successful silent FMP segments preserve the remaining GAS events. *)
Theory gasFocusFmpLocalEvents
Ancestors
  gasEvents fmpStageRel fmpLowerDefs passSharedProps analysisSimDefs
  venomExecSemantics venomState venomInst list rich_list arithmetic

Theorem gas_events_run_insts_silent:
  !xs s u j.
  j + LENGTH xs <= LENGTH bb.bb_instructions /\
  TAKE (LENGTH xs) (DROP j bb.bb_instructions) = xs /\
  EVERY (\i. ~is_terminator i.inst_opcode /\
              i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE) xs /\
  run_insts fuel C xs s = OK u ==>
  gas_events_block fuel C owner bb (s with vs_inst_idx := j) =
  gas_events_block fuel C owner bb
    (u with vs_inst_idx := j + LENGTH xs)
Proof
  Induct >- simp[run_insts_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `run_insts fuel C (h::xs) s = OK u` >>
  `j < LENGTH bb.bb_instructions` by fs[] >>
  `DROP j bb.bb_instructions =
   EL j bb.bb_instructions :: DROP (SUC j) bb.bb_instructions` by
    (qspecl_then [`bb.bb_instructions`,`j`] mp_tac DROP_EL_CONS >>
     simp[ADD1]) >>
  `get_instruction bb j = SOME h` by gvs[get_instruction_def] >>
  gvs[run_insts_def, AllCaseEqs()] >>
  rename1 `step_inst fuel C h s = OK v` >>
  drule_then (qspecl_then [`fuel`,`C`,`s`,`j`] mp_tac)
    step_inst_non_term_idx >>
  simp[] >> strip_tac >>
  CONV_TAC (LHS_CONV (REWR_CONV gas_events_block_def)) >>
  simp[gas_events_step_def] >>
  first_x_assum (qspecl_then [`v`,`u`,`SUC j`] mp_tac) >>
  simp[ADD_CLAUSES]
QED

Theorem fmp_target_run_gas_events:
  fmp_target_run fuel C name t n t1 /\
  lookup_function name C.ctx_functions = SOME fn /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  EVERY (\i. ~is_terminator i.inst_opcode /\
              i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE)
    (TAKE n (DROP t.vs_inst_idx bb.bb_instructions)) ==>
  gas_events_block fuel C owner bb t =
  gas_events_block fuel C owner bb t1
Proof
  strip_tac >> gvs[fmp_target_run_def] >>
  rename1 `run_insts fuel C _ t = OK u` >>
  qspecl_then [`TAKE n (DROP t.vs_inst_idx bb.bb_instructions)`,
               `t`,`u`,`t.vs_inst_idx`] mp_tac
    gas_events_run_insts_silent >>
  simp[LENGTH_TAKE, LENGTH_DROP]
QED

Theorem fmp_restore_run_gas_events:
  fmp_target_run fuel C name t n t1 /\
  lookup_function name C.ctx_functions = SOME fn /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  n <= 1 /\
  (n = 1 ==> (EL t.vs_inst_idx bb.bb_instructions).inst_opcode = ASSIGN) ==>
  gas_events_block fuel C owner bb t =
  gas_events_block fuel C owner bb t1
Proof
  strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\
              i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE)
     (TAKE n (DROP t.vs_inst_idx bb.bb_instructions))` suffices_by
    metis_tac[fmp_target_run_gas_events] >>
  Cases_on `n = 0` >- simp[] >>
  `n = 1` by decide_tac >> gvs[] >>
  `t.vs_inst_idx < LENGTH bb.bb_instructions` by
    fs[fmp_target_run_def] >>
  qspecl_then [`bb.bb_instructions`,`t.vs_inst_idx`] mp_tac DROP_EL_CONS >>
  simp[ADD1] >> disch_then SUBST1_TAC >>
  simp[is_terminator_def]
QED

Theorem fmp_dalloca_expansion_gas_events:
  inst.inst_opcode = DALLOCA /\
  fmp_lower_inst infos ctx runner supply inst = SOME (code,supply') /\
  t.vs_inst_idx + LENGTH code <= LENGTH bb.bb_instructions /\
  TAKE (LENGTH code) (DROP t.vs_inst_idx bb.bb_instructions) = code /\
  run_insts fuel C code t = OK u ==>
  gas_events_block fuel C owner bb t =
  gas_events_block fuel C owner bb
    (u with vs_inst_idx := t.vs_inst_idx + LENGTH code)
Proof
  strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\
              i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE) code` by
    (gvs[fmp_lower_inst_def, AllCaseEqs()] >>
     simp[mk_inst_def, is_terminator_def]) >>
  qspecl_then [`code`,`t`,`u`,`t.vs_inst_idx`] mp_tac
    gas_events_run_insts_silent >> simp[]
QED
