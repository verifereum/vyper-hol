Theory gasFocusRetainedRowTail
Ancestors
  dftIndexedExec gasEvents gasCount gasOracleReplay removeUnusedGasProofs
  venomExecSemantics venomInst venomState stateEquiv list rich_list arithmetic

Theorem focus_retained_row_tail:
  !pre fuel C s g tail u owner.
  EVERY (\i. ~is_terminator i.inst_opcode) pre /\
  FOLDR (dft_exec_cons fuel C) OK pre
    (s with vs_gas_readings := g ++ tail) = OK u /\
  LENGTH (gas_events_block fuel C owner
    <|bb_label := s.vs_current_bb;
      bb_instructions := REPLICATE s.vs_inst_idx (mk_inst 0 STOP [] []) ++ pre|>
    (s with vs_gas_readings := g ++ tail)) = LENGTH g ==>
  !tail'. FOLDR (dft_exec_cons fuel C) OK pre
    (s with vs_gas_readings := g ++ tail') =
    OK (u with vs_gas_readings := tail')
Proof
  Induct
  >- (rpt gen_tac >> simp[Once gas_events_block_def, get_instruction_def] >>
      rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `step_inst fuel C h (s with vs_gas_readings := g ++ tail)` >>
  gvs[dft_exec_cons_def] >>
  rename1 `step_inst fuel C h (s with vs_gas_readings := g ++ tail) = OK v` >>
  qmatch_asmsub_abbrev_tac `gas_events_block fuel C owner B _` >>
  `get_instruction B s.vs_inst_idx = SOME h` by
    simp[Abbr `B`, get_instruction_def, EL_APPEND_EQN] >>
  qpat_x_assum `LENGTH (gas_events_block _ _ _ _ _) = _` mp_tac >>
  simp[Once gas_events_block_def] >> strip_tac >>
  qabbrev_tac `n = gas_count_step fuel C h (s with vs_gas_readings := g ++ tail)` >>
  `n <= LENGTH g` by (gvs[Abbr `n`, gas_events_length] >> decide_tac) >>
  `!t. step_inst fuel C h (s with vs_gas_readings := TAKE n g ++ t) =
         OK (v with vs_gas_readings := t)` by
    (qspec_then `fuel` mp_tac remove_unused_step_successful_replay_count >>
     disch_then (qspecl_then [`C`, `h`, `s with vs_gas_readings := g ++ tail`] mp_tac) >>
     simp[gas_replay_at_def, lift_result_def, Abbr `n`,
          gas_prefix_def, TAKE_APPEND1] >>
     disch_tac >> gen_tac >> first_x_assum (qspec_then `t` mp_tac) >>
     Cases_on `step_inst fuel C h (s with vs_gas_readings :=
       TAKE (gas_count_step fuel C h (s with vs_gas_readings := g ++ tail)) g ++ t)` >>
     gvs[lift_result_def]) >>
  `v.vs_gas_readings = DROP n g ++ tail` by
    (mp_tac (cj 1 gas_count_suffix) >>
     disch_then (qspecl_then [`fuel`, `C`, `h`, `s with vs_gas_readings := g ++ tail`] mp_tac) >>
     simp[gas_count_suffix_def, Abbr `n`, DROP_APPEND1]) >>
  `gas_events_block fuel C owner B (v with vs_inst_idx := SUC s.vs_inst_idx) =
    gas_events_block fuel C owner
      <|bb_label := v.vs_current_bb;
        bb_instructions := REPLICATE (SUC s.vs_inst_idx) (mk_inst 0 STOP [] []) ++ pre|>
      (v with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule gas_events_block_suffix_cong >> simp[Abbr `B`, DROP_APPEND, ADD1]) >>
  `!tail'. FOLDR (dft_exec_cons fuel C) OK pre
      ((v with vs_inst_idx := SUC s.vs_inst_idx) with vs_gas_readings := DROP n g ++ tail') =
      OK (u with vs_gas_readings := tail')` by
    (first_x_assum irule >> qexistsl_tac [`owner`, `tail`] >>
     qpat_assum `v.vs_gas_readings = _` (fn th => pure_rewrite_tac[GSYM th]) >>
     simp[NoAsms] >>
     qpat_x_assum `gas_events_block _ _ _ B _ = _` (fn th => rewrite_tac[GSYM (SRULE [] th)]) >>
     gvs[gas_events_length, Abbr `n`] >> decide_tac) >>
  gen_tac >>
  `g ++ tail' = TAKE n g ++ (DROP n g ++ tail')` by simp[] >>
  once_asm_rewrite_tac[] >> simp[]
  >> (gvs[])
QED
