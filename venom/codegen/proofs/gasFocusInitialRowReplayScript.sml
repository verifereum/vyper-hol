Theory gasFocusInitialRowReplay
Ancestors
  dftIndexedExec gasEvents gasOracleReplay venomExecSemantics
  venomInst venomState stateEquiv list rich_list arithmetic

Theorem focus_initial_unvisited_row_replay:
  !f C owner be zs gs tail.
  EVERY (\i. ~is_terminator i.inst_opcode /\
             i.inst_opcode <> INVOKE /\ ~is_pseudo i.inst_opcode) zs /\
  LENGTH gs = LENGTH (FILTER (\i. i.inst_opcode = GAS) zs) ==>
  !bb. bb = <|bb_label := be.vs_current_bb;
             bb_instructions := REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ zs|> ==>
  !sites. sites = MAP (\i. (owner,i.inst_id)) (FILTER (\i. i.inst_opcode = GAS) zs) ==>
    (?extra. sites = gas_events_block f C owner bb
         (be with vs_gas_readings := gs ++ tail) ++ extra) /\
    (!u. FOLDR (dft_exec_cons f C) OK zs
         (be with vs_gas_readings := gs ++ tail) = OK u ==>
       gas_events_block f C owner bb
         (be with vs_gas_readings := gs ++ tail) = sites /\
       u.vs_gas_readings = tail /\
       (!tail'. FOLDR (dft_exec_cons f C) OK zs
          (be with vs_gas_readings := gs ++ tail') =
            OK (u with vs_gas_readings := tail')))
Proof
  CONV_TAC (TOP_DEPTH_CONV (Unwind.UNWIND_FORALL_CONV)) >>
  ntac 4 gen_tac >> qid_spec_tac `be` >>
  Induct_on `zs`
  >- (simp[] >> rpt gen_tac >>
      simp[Once gas_events_block_def, get_instruction_def,
           venom_state_component_equality]) >>
  rpt gen_tac >> simp[EVERY_DEF] >> strip_tac >>
  simp[] >>
  `gas_replay_at (if h.inst_opcode = GAS then 1 else 0)
     (step_inst_base h) (be with vs_gas_readings := gs ++ tail)` by
    (Cases_on `h.inst_opcode = GAS` >> simp[]
     >- (simp[gas_replay_at_def, step_inst_base_def] >>
         mp_tac (Q.INST [`inst` |-> `h`,
           `s` |-> `be with vs_gas_readings := gs ++ tail`] gas_exec_gas) >>
         simp[gas_replay_at_def]) >>
     irule gas_base_non_gas >> simp[]) >>
  once_rewrite_tac[gas_events_block_def] >>
  simp[get_instruction_def, EL_APPEND_EQN, gas_events_step_def,
       dft_exec_cons_def, step_inst_non_invoke] >>
  Cases_on `step_inst_base h (be with vs_gas_readings := gs ++ tail)` >>
  simp[]
  >- suspend "success"
  >> Cases_on `h.inst_opcode = GAS` >> simp[]
QED

Resume focus_initial_unvisited_row_replay[success]:
  rename1 `step_inst_base h (be with vs_gas_readings := gs ++ tail) = OK v` >>
  qabbrev_tac `n:num = if h.inst_opcode = GAS then 1 else 0` >>
  `LENGTH (DROP n gs) = LENGTH (FILTER (\i. i.inst_opcode = GAS) zs)` by
    (Cases_on `h.inst_opcode = GAS` >> gvs[Abbr `n`, LENGTH_DROP]) >>
  `!tail'. v.vs_gas_readings = DROP n gs ++ tail /\
     step_inst_base h (be with vs_gas_readings := gs ++ tail') =
       OK (v with vs_gas_readings := DROP n gs ++ tail')` by
    (gen_tac >> qpat_x_assum `gas_replay_at _ _ _` mp_tac >>
     simp[gas_replay_at_def] >>
     disch_then (qspec_then `DROP n gs ++ tail'` mp_tac) >>
     Cases_on `step_inst_base h (be with vs_gas_readings := gs ++ tail')` >>
     Cases_on `h.inst_opcode = GAS` >> gvs[Abbr `n`] >>
     Cases_on `gs` >> gvs[gas_prefix_def, lift_result_def]) >>
  `v.vs_gas_readings = DROP n gs ++ tail` by metis_tac[] >>
  first_x_assum (qspecl_then
    [`v with vs_inst_idx := SUC be.vs_inst_idx`, `DROP n gs`, `tail`] mp_tac) >>
  simp[] >>
  `v with <|vs_inst_idx := SUC be.vs_inst_idx;
            vs_gas_readings := DROP n gs ++ tail|> =
     v with vs_inst_idx := SUC be.vs_inst_idx` by
    simp[venom_state_component_equality] >>
  simp[] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `gas_events_block f C owner bb
    (v with vs_inst_idx := SUC be.vs_inst_idx)` >>
  `gas_events_block f C owner bb (v with vs_inst_idx := SUC be.vs_inst_idx) =
   gas_events_block f C owner
     <|bb_label := v.vs_current_bb;
       bb_instructions := mk_inst 0 STOP [] [] ::
         (REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ zs)|>
     (v with vs_inst_idx := SUC be.vs_inst_idx)` by
    (irule gas_events_block_suffix_cong >> qexists_tac `zs` >>
     simp[Abbr `bb`, DROP_APPEND2, ADD1]) >>
  pop_assum (fn th => rewrite_tac[th]) >>
  Cases_on `h.inst_opcode = GAS` >>
  pop_assum (fn th => simp[NoAsms, th]) >> metis_tac[]
QED

Finalise focus_initial_unvisited_row_replay
