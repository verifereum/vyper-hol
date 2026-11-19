Theory dftPacketClosedBodyBoundary
Ancestors
  dftPacketClosedRowNative dftGasFromListReadings dftGasToListReplay
  removeUnusedGasProofs gasEvents gasOracleReplay stateEquiv
  passSimulationDefs dftRunRel venomExecSemantics venomInst venomState
  list rich_list arithmetic

Theorem closed_body_success_replay[local]:
  !fuel C bb s v a d sf keys gs tail.
    exec_block fuel C bb (s with vs_gas_readings := gs ++ tail) = OK v /\
    LENGTH keys = LENGTH gs /\
    trace_gas (trace_block a d fuel C sf bb
      (s with vs_gas_readings := gs ++ tail)) = ZIP (keys,gs) ==>
    !tail'. exec_block fuel C bb (s with vs_gas_readings := gs ++ tail') =
      OK (v with vs_gas_readings := tail')
Proof
  rpt gen_tac >> strip_tac >>
  `gas_count_block fuel C bb (s with vs_gas_readings := gs ++ tail) =
    LENGTH gs` by
    (qpat_x_assum `trace_gas _ = _`
      (mp_tac o AP_TERM ``LENGTH : (gas_event # bytes32) list -> num``) >>
     simp[cj 2 trace_gas_lengths]) >>
  `~(?msg. exec_block fuel C bb
    (s with vs_gas_readings := gs ++ tail) = Error msg)` by simp[] >>
  drule remove_unused_block_successful_replay_count >>
  simp[gas_replay_at_def,gas_prefix_def,TAKE_APPEND,DROP_APPEND,SUB_PLUS] >>
  strip_tac >> gen_tac >> first_x_assum (qspec_then `tail'` mp_tac) >>
  Cases_on `exec_block fuel C bb (s with vs_gas_readings := gs ++ tail')` >>
  simp[lift_result_def]
QED

Theorem dft_packet_closed_body_boundary:
  !N d C7 sf bb ps xs be post a Mb Eb Kb.
    bb.bb_instructions = ps ++ xs /\
    be.vs_inst_idx = LENGTH ps /\ be.vs_current_bb = bb.bb_label /\
    xs <> [] /\ is_terminator (LAST xs).inst_opcode /\ ~post.vs_halted /\
    LENGTH Mb = LENGTH Eb /\ LENGTH Mb = LENGTH Kb /\
    (!F gs tail. N <= F /\
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mb gs ==>
      (?extra. Eb = gas_events_block (F-d) C7 sf.fn_name
        <|bb_label := be.vs_current_bb; bb_instructions :=
          REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
        (be with vs_gas_readings := gs ++ tail) ++ extra) /\
      ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
          (be with vs_gas_readings := gs ++ tail))) ==>
        gas_events_block (F-d) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
          (be with vs_gas_readings := gs ++ tail) = Eb /\
        residual_result tail (OK post)
          (FOLDR (dft_exec_cons (F-d) C7) OK xs
            (be with vs_gas_readings := gs ++ tail))) /\
      (!v. (FOLDR (dft_exec_cons (F-d) C7) OK xs
              (be with vs_gas_readings := gs ++ tail) = OK v \/
            ?ir. FOLDR (dft_exec_cons (F-d) C7) OK xs
              (be with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
        trace_gas (trace_block a d (F-d) C7 sf
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
          (be with vs_gas_readings := gs ++ tail)) = ZIP (Kb,gs))) ==>
    !F gs tail s r. N <= F /\
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mb gs /\
      s = be with vs_gas_readings := gs ++ tail /\
      r = FOLDR (dft_exec_cons (F-d) C7) OK xs s ==>
      exec_block (F-d) C7 bb s = r /\
      (?extra. Eb = gas_events_block (F-d) C7 sf.fn_name bb s ++ extra) /\
      (!v. r = OK v ==>
        v = post with vs_gas_readings := tail /\
        gas_events_block (F-d) C7 sf.fn_name bb s = Eb /\
        trace_gas (trace_block a d (F-d) C7 sf bb s) = ZIP (Kb,gs)) /\
      (~(?v. r = OK v) ==> ?msg. r = Error msg)
Proof
  rpt gen_tac >> strip_tac >>
  map_every qx_gen_tac [`fuel`,`gs`,`tail`,`s`,`r`] >> strip_tac >>
  `exec_block (fuel-d) C7 bb s = r` by
    (simp[] >> irule native_exec_block_terminated_fold >>
     simp[DROP_APPEND]) >>
  `gas_events_block (fuel-d) C7 sf.fn_name bb s =
    gas_events_block (fuel-d) C7 sf.fn_name
      <|bb_label := be.vs_current_bb; bb_instructions :=
        REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|> s` by
    (irule gas_events_block_suffix_cong >> qexists_tac `xs` >> simp[DROP_APPEND]) >>
  `trace_block a d (fuel-d) C7 sf bb s =
    trace_block a d (fuel-d) C7 sf
      <|bb_label := be.vs_current_bb; bb_instructions :=
        REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|> s` by
    (irule native_trace_block_suffix_cong >> simp[DROP_APPEND]) >>
  qpat_x_assum `!F gs tail. _`
    (qspecl_then [`fuel`,`gs`,`tail`] mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `Eb = _ ++ _` kall_tac >>
  Cases_on `?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
    (be with vs_gas_readings := gs ++ tail))`
  >- gvs[] >>
  `?msg. FOLDR (dft_exec_cons (fuel-d) C7) OK xs
    (be with vs_gas_readings := gs ++ tail) = Error msg` by
    (Cases_on `FOLDR (dft_exec_cons (fuel-d) C7) OK xs
      (be with vs_gas_readings := gs ++ tail)` >> simp[] >>
     qpat_x_assum `~?f. _` mp_tac >> simp[] >>
     qexists_tac `fuel-d` >> simp[terminates_def]) >>
  gvs[]
QED

Theorem dft_packet_closed_body_tail:
  !N d C7 sf bb ps xs be post a Mb Eb Kb.
    bb.bb_instructions = ps ++ xs /\
    be.vs_inst_idx = LENGTH ps /\ be.vs_current_bb = bb.bb_label /\
    xs <> [] /\ is_terminator (LAST xs).inst_opcode /\ ~post.vs_halted /\
    LENGTH Mb = LENGTH Eb /\ LENGTH Mb = LENGTH Kb /\
    (!F gs tail. N <= F /\
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mb gs ==>
      (?extra. Eb = gas_events_block (F-d) C7 sf.fn_name
        <|bb_label := be.vs_current_bb; bb_instructions :=
          REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
        (be with vs_gas_readings := gs ++ tail) ++ extra) /\
      ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
          (be with vs_gas_readings := gs ++ tail))) ==>
        gas_events_block (F-d) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
          (be with vs_gas_readings := gs ++ tail) = Eb /\
        residual_result tail (OK post)
          (FOLDR (dft_exec_cons (F-d) C7) OK xs
            (be with vs_gas_readings := gs ++ tail))) /\
      (!v. (FOLDR (dft_exec_cons (F-d) C7) OK xs
              (be with vs_gas_readings := gs ++ tail) = OK v \/
            ?ir. FOLDR (dft_exec_cons (F-d) C7) OK xs
              (be with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
        trace_gas (trace_block a d (F-d) C7 sf
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
          (be with vs_gas_readings := gs ++ tail)) = ZIP (Kb,gs))) ==>
    !F gs tail s r v. N <= F /\
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mb gs /\
      s = be with vs_gas_readings := gs ++ tail /\
      r = FOLDR (dft_exec_cons (F-d) C7) OK xs s /\ r = OK v ==>
      !tail'. FOLDR (dft_exec_cons (F-d) C7) OK xs
          (be with vs_gas_readings := gs ++ tail') =
          OK (post with vs_gas_readings := tail') /\
        gas_events_block (F-d) C7 sf.fn_name bb
          (be with vs_gas_readings := gs ++ tail') = Eb
Proof
  rpt gen_tac >> strip_tac >>
  map_every qx_gen_tac [`fuel`,`gs`,`tail`,`s`,`r`,`v`] >> strip_tac >>
  drule_all dft_packet_closed_body_boundary >>
  simp[] >> strip_tac >>
  qpat_x_assum `Eb = _ ++ _` kall_tac >>
  `LENGTH Kb = LENGTH gs` by metis_tac[LIST_REL_LENGTH] >>
  `!tail'. exec_block (fuel-d) C7 bb
    (be with vs_gas_readings := gs ++ tail') =
      OK (post with vs_gas_readings := tail')` by
    (drule_all closed_body_success_replay >> simp[]) >>
  qx_gen_tac `tail'` >>
  `exec_block (fuel-d) C7 bb (be with vs_gas_readings := gs ++ tail') =
    FOLDR (dft_exec_cons (fuel-d) C7) OK xs
      (be with vs_gas_readings := gs ++ tail')` by
    (irule native_exec_block_terminated_fold >> simp[DROP_APPEND]) >>
  `FOLDR (dft_exec_cons (fuel-d) C7) OK xs
    (be with vs_gas_readings := gs ++ tail') =
    OK (post with vs_gas_readings := tail')` by metis_tac[] >>
  `?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
    (be with vs_gas_readings := gs ++ tail'))` by
    (qexists_tac `fuel-d` >> simp[terminates_def]) >>
  qpat_x_assum `!F gs tail. _`
    (qspecl_then [`fuel`,`gs`,`tail'`] mp_tac) >> simp[] >>
  strip_tac >> qpat_x_assum `Eb = _ ++ _` kall_tac >>
  `gas_events_block (fuel-d) C7 sf.fn_name bb
    (be with vs_gas_readings := gs ++ tail') =
    gas_events_block (fuel-d) C7 sf.fn_name
      <|bb_label := bb.bb_label; bb_instructions :=
        REPLICATE (LENGTH ps) (mk_inst 0 STOP [] []) ++ xs|>
      (be with vs_gas_readings := gs ++ tail')` by
    (irule gas_events_block_suffix_cong >> qexists_tac `xs` >> simp[DROP_APPEND]) >>
  metis_tac[]
QED
