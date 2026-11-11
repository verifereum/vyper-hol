Theory dftGasFromListTraceReach
Ancestors
  dftGasFromListCalleeSeed dftGasFromListReachBoundary dftGasFromListReplay dftGasFromListReplayBoundary
  dftGasFromListRestore dftGasFromListTraceDefs gasOracleReplay
  dftGasOracleDefs contextCodegenRel venomExecSemantics venomInst venomState list

Theorem trace_visits_reachable:
  (!p d fuel ctx fn inst s. !orc vs0 gs.
    active_inst fn inst s /\
    ev_reachable orc vs0 ctx p d fn inst (s with vs_gas_readings := gs) /\
    trace_agrees orc (trace_step p d fuel ctx fn inst s) ==>
    !q e id f i t. MEM ((q,e,id),f,i,t) (trace_step p d fuel ctx fn inst s) ==>
      ev_reachable orc vs0 ctx q e f i (t with vs_gas_readings := gs)) /\
  (!p d fuel ctx fn bb s. !orc vs0 gs.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    (!i. active_inst fn i s ==>
      ev_reachable orc vs0 ctx p d fn i (s with vs_gas_readings := gs)) /\
    trace_agrees orc (trace_block p d fuel ctx fn bb s) ==>
    !q e id f i t. MEM ((q,e,id),f,i,t) (trace_block p d fuel ctx fn bb s) ==>
      ev_reachable orc vs0 ctx q e f i (t with vs_gas_readings := gs)) /\
  (!p d fuel ctx fn s. !orc vs0 gs.
    (!u i. enters_block fn s u /\ active_inst fn i u ==>
      ev_reachable orc vs0 ctx p (SUC d) fn i (u with vs_gas_readings := gs)) /\
    trace_agrees orc (trace_blocks p d fuel ctx fn s) ==>
    !q e id f i t. MEM ((q,e,id),f,i,t) (trace_blocks p d fuel ctx fn s) ==>
      ev_reachable orc vs0 ctx q e f i (t with vs_gas_readings := gs))
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume trace_visits_reachable[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (Cases_on `decode_invoke inst`
      >- simp[Once trace_defs] >>
      rename1 `decode_invoke inst = SOME decoded` >> PairCases_on `decoded` >>
      Cases_on `lookup_function decoded0 ctx.ctx_functions`
      >- simp[Once trace_defs] >>
      rename1 `lookup_function _ _ = SOME callee` >>
      Cases_on `eval_operands decoded1 s`
      >- simp[Once trace_defs] >>
      rename1 `eval_operands _ _ = SOME args` >>
      Cases_on `setup_callee callee args s`
      >- simp[Once trace_defs] >>
      rename1 `setup_callee _ _ _ = SOME cs` >>
      drule_all trace_step_invoke >> disch_then (fn th =>
        RULE_ASSUM_TAC (REWRITE_RULE [th]) >> rewrite_tac[th]) >>
      rpt strip_tac >>
      qpat_x_assum `!v nm ops fn args cs. _`
        (mp_tac o SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO]) >>
      disch_then drule >> disch_then drule >>
      disch_then drule >> disch_then drule >>
      disch_then (qspecl_then [`orc`,`vs0`,`gs`] mp_tac) >>
      disch_then irule >> reverse conj_tac
      >- metis_tac[] >>
      rpt strip_tac >> metis_tac[restored_callee_entry]) >>
  simp[trace_step_noninvoke]
QED

Resume trace_visits_reachable[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[Once trace_defs] >>
  rename1 `get_instruction _ _ = SOME inst` >>
  `active_inst fn inst s` by (irule lookup_instruction_active >> simp[]) >>
  `ev_reachable orc vs0 ctx p d fn inst (s with vs_gas_readings := gs)` by
    metis_tac[] >>
  qpat_x_assum `trace_agrees _ _` mp_tac >>
  simp[Once trace_defs, trace_agrees_cons] >> strip_tac >>
  simp[Once trace_defs, MEM_APPEND] >> rpt strip_tac
  >- gvs[]
  >- (qpat_x_assum `!inst'. SOME inst = SOME inst' ==> _`
        (mp_tac o SRULE []) >>
      disch_then (qspecl_then [`orc`,`vs0`,`gs`] mp_tac) >>
      metis_tac[]) >>
  Cases_on `step_inst fuel ctx inst s` >> gvs[] >>
  rename1 `step_inst _ _ _ _ = OK out` >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
  `ev_step orc p d fuel ctx inst (s with vs_gas_readings := gs) =
     OK (out with vs_gas_readings := gs)` by
    (`trace_agrees orc
        (((p,d,inst.inst_id),fn,inst,s)::trace_step p d fuel ctx fn inst s)` by
        simp[trace_agrees_cons] >>
     drule (cj 1 trace_replay) >>
     disch_then (qspec_then `gs` mp_tac) >> simp[restore_rel_cases]) >>
  `out.vs_current_bb = s.vs_current_bb` by
    (drule_all ev_step_preserves_current_bb >> simp[]) >>
  qpat_x_assum `!orc vs0 gs. lookup_block _ _ = _ /\ _ ==> _` mp_tac >>
  disch_then (qspecl_then [`orc`,`vs0`,`gs`] mp_tac) >>
  disch_then irule >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  qpat_x_assum `!orc vs0 gs. _` kall_tac >>
  `ev_reachable orc vs0 ctx p d fn inst (s with vs_gas_readings := gs)` by
    metis_tac[] >>
  `active_inst fn inst (s with vs_gas_readings := gs)` by
    simp[active_inst_restore] >>
  `active_inst fn i' ((out with vs_gas_readings := gs) with
      vs_inst_idx := SUC (s with vs_gas_readings := gs).vs_inst_idx)` by
    (fs[active_inst_def] >> metis_tac[]) >>
  drule_all ev_reachable_next >> simp[]
QED

Resume trace_visits_reachable[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `fuel` >- simp[] >>
  rename1 `trace_blocks p d (SUC k) ctx fn s` >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[Once trace_defs] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  simp[Once trace_defs] >> gvs[] >>
  rename1 `eval_phis _ _ = OK sp` >>
  `sp.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
  `enters_block fn s (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (simp[enters_block_def] >> metis_tac[]) >>
  qpat_x_assum `trace_agrees _ _` mp_tac >>
  simp[Once trace_defs] >> strip_tac >>
  rpt strip_tac
  >- (qpat_x_assum `!orc vs0 gs. lookup_block _ _ = _ /\ _ ==> _` mp_tac >>
      disch_then (qspecl_then [`orc`,`vs0`,`gs`] mp_tac) >>
      disch_then irule >> simp[] >> reverse conj_tac
      >- metis_tac[] >>
      rpt strip_tac >>
      qpat_x_assum `!u i. _` (drule_at Any) >> simp[]) >>
  Cases_on `exec_block k ctx bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  gvs[] >>
  rename1 `exec_block _ _ _ _ = OK out` >>
  Cases_on `out.vs_halted` >> gvs[] >>
  `ev_block orc p (SUC d) k ctx bb
      ((sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)
        with vs_gas_readings := gs) = OK (out with vs_gas_readings := gs)` by
    (drule (cj 2 trace_replay) >>
     disch_then (qspec_then `gs` mp_tac) >> simp[restore_rel_cases]) >>
  qpat_x_assum `!orc vs0 gs. (!u i. _ ) /\ _ ==> _` mp_tac >>
  disch_then (qspecl_then [`orc`,`vs0`,`gs`] mp_tac) >>
  disch_then irule >> simp[] >> reverse conj_tac
  >- metis_tac[] >>
  rpt strip_tac >>
  drule enters_block_restore >> disch_then (qspec_then `gs` assume_tac) >>
  `active_inst fn i' (u with vs_gas_readings := gs)` by simp[] >>
  irule ev_block_next_entry >> conj_tac >- simp[] >>
  qexistsl_tac [`bb`, `k`,
    `(sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)
      with vs_gas_readings := gs`, `out with vs_gas_readings := gs`] >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `!u i. _` (drule_at Any) >> simp[]
QED

Finalise trace_visits_reachable
