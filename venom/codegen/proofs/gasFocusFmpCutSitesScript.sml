Theory gasFocusFmpCutSites
Ancestors frameExecutionHistory[qualified,ignore_grammar] frameOriginReachable[qualified,ignore_grammar] concretizePtrChronologicalHistory[qualified,ignore_grammar] o1LowerDloadOccurrence[qualified,ignore_grammar] frameOriginHistory[qualified,ignore_grammar] frameJointTransition[qualified,ignore_grammar] fmpStageReclaimSound[qualified,ignore_grammar] ptrSafeRun[qualified,ignore_grammar]
  fmpStageRel fmpStageFmpStepsDallocaExec frameAllocationOwnership
  concretizeLayoutCutSafe gasOracleReplay lowerDloadPtrRawReachable
  lowerDloadLifetime rawReachableFmp ptrDisciplineEmptyTaint ptrDiscipline
  o1PassContract ctxLookupAgreeHelpers venomExecProofs venomExecSemantics
  venomState venomInst opcodeClass unitTransformDefs contextCodegenRel
  o1SafeUpto passSimulationDefs list finite_map words
  arithmetic pair pred_set

Theorem cut_sites_source_point[local]:
  o1_ctx_shape C /\ EVERY (o1_fn_row 3) C.ctx_functions /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s ==>
  raw_reachable vs C fn inst s /\ inst.inst_opcode <> ALLOCA /\
  pre_fmp_opcode inst.inst_opcode
Proof
  strip_tac >> drule_all frame_reachable_raw_certificate >> strip_tac >>
  `o1_fn_row 3 fn` by metis_tac[EVERY_MEM] >>
  gvs[o1_fn_row_def, pre_fmp_ops_def] >>
  imp_res_tac EVERY_active_inst >> gvs[]
QED

Theorem cut_sites_dalloca_growth[local]:
  inst.inst_opcode = DALLOCA /\ dalloca_no_wrap inst s /\
  step_inst fuel C inst s = OK t ==>
  w2n s.vs_fmp <= w2n t.vs_fmp /\
  (!b z. out_prov PG G inst t = SOME (b,z) ==>
         b = w2n s.vs_fmp /\ b + z = w2n t.vs_fmp)
Proof
  strip_tac >> `terminates (OK t)` by simp[terminates_def] >>
  drule_all fmp_dalloca_source >> strip_tac >>
  `step_inst_base inst s = OK t` by gvs[step_inst_non_invoke] >>
  drule_all ld_dalloca_provenance >>
  gvs[update_var_def, w2n_n2w] >> decide_tac
QED

(* The suspended callers carry the same bounds relative to their own
   frontiers. In particular a return uses the saved caller's bound, not
   the larger frontier of the callee at its return instruction. *)
Theorem cut_sites_invariant[local]:
  !vs C stk PG G tn fn inst s.
    frame_reachable vs C stk PG G tn fn inst s ==>
    !n raw0.
      o1_ctx_shape C /\ EVERY (o1_fn_row 3) C.ctx_functions /\
      raw0 = w2n vs.vs_fmp /\
      (!fn inst s. raw_reachable vs C fn inst s /\ gas_cut n vs s ==>
                   dalloca_no_wrap inst s) /\ gas_cut n vs s ==>
      (raw0 <= fmp_frame_base raw0 stk /\
       fmp_frame_base raw0 stk <= w2n s.vs_fmp /\
       EVERY (\f. w2n f.cf_state.vs_fmp <= w2n s.vs_fmp) stk /\
       prov_sites (\(b,z). 0 < z ==> raw0 <= b /\ b + z <= w2n s.vs_fmp) G /\
       param_sites (\(b,z). 0 < z ==> raw0 <= b /\ b + z <= fmp_frame_base raw0 stk) PG) /\
      (!pre f rest. stk = pre ++ f::rest ==>
       raw0 <= fmp_frame_base raw0 rest /\
       fmp_frame_base raw0 rest <= w2n f.cf_state.vs_fmp /\
       EVERY (\g. w2n g.cf_state.vs_fmp <= w2n f.cf_state.vs_fmp) rest /\
       prov_sites (\(b,z). 0 < z ==> raw0 <= b /\ b + z <= w2n f.cf_state.vs_fmp) f.cf_prov /\
       param_sites (\(b,z). 0 < z ==> raw0 <= b /\ b + z <= fmp_frame_base raw0 rest) f.cf_params)
Proof
  ho_match_mp_tac frame_reachable_strongind >> rpt conj_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume cut_sites_invariant[entry]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule fmpStageReclaimSoundTheory.fmp_enters_block_frontier >>
  simp[fmp_frame_base_def, prov_sites_def, param_sites_def]
QED

Resume cut_sites_invariant[next]:
  rpt gen_tac >> strip_tac >> map_every qx_gen_tac [`n`, `raw0`] >> strip_tac >>
  `gas_cut n vs s` by
    (irule gas_cut_readings_mono >> first_assum (irule_at Any) >> simp[] >>
     irule step_inst_noninvoke_readings_le >> metis_tac[]) >>
  qpat_x_assum `!n raw0. _` (qspecl_then [`n`, `raw0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  drule_all cut_sites_source_point >> strip_tac >>
  `dalloca_no_wrap inst s` by metis_tac[] >>
  `w2n s.vs_fmp <= w2n s'.vs_fmp /\
   (inst.inst_opcode = DALLOCA ==>
    !site. out_prov PG G inst s' = SOME site ==>
           (\(b,z). 0 < z ==> raw0 <= b /\ b + z <= w2n s'.vs_fmp) site)` by
    (Cases_on `inst.inst_opcode = DALLOCA`
     >- (drule_all cut_sites_dalloca_growth >>
         disch_then (qspecl_then [`PG`, `G`] strip_assume_tac) >> simp[] >>
         Cases >> simp[] >> rpt strip_tac >>
         qpat_x_assum `!b z. out_prov _ _ _ _ = _ ==> _` drule >>
         strip_tac >> decide_tac) >>
     drule_all fmpStageReclaimSoundTheory.fmp_source_nonalloc_frontier >> simp[]) >>
  reverse conj_tac >- (qpat_assum `!pre f rest. _` ACCEPT_TAC) >>
  pure_rewrite_tac[venom_state_accfupds, venom_state_accessors] >>
  rpt conj_tac >- simp[] >- decide_tac
  >- (gvs[EVERY_MEM] >> metis_tac[LESS_EQ_TRANS])
  >- (irule fmpStageReclaimSoundTheory.fmp_sites_step >> simp[] >> conj_tac
      >- (gvs[param_sites_def] >> Cases >> simp[] >> strip_tac >>
          qpat_assum `!site. MEM (SOME site) PG ==> _` drule >>
          disch_then (assume_tac o SRULE []) >> gvs[] >> decide_tac) >>
      irule prov_sites_mono >> goal_assum (drule_at Any) >>
      Cases >> simp[] >> decide_tac) >>
  simp[]
QED

Resume cut_sites_invariant[block]:
  rpt gen_tac >> strip_tac >> map_every qx_gen_tac [`n`, `raw0`] >> strip_tac >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> DALLOCA` by
    metis_tac[is_terminator_def] >>
  `gas_cut n vs s` by
    (irule gas_cut_readings_mono >> first_assum (irule_at Any) >>
     drule enters_block_readings >> strip_tac >> simp[] >>
     irule step_inst_noninvoke_readings_le >> metis_tac[]) >>
  qpat_x_assum `!n raw0. _` (qspecl_then [`n`, `raw0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  drule_all cut_sites_source_point >> strip_tac >>
  drule_all_then assume_tac fmpStageReclaimSoundTheory.fmp_source_nonalloc_frontier >>
  drule_then assume_tac fmpStageReclaimSoundTheory.fmp_enters_block_frontier >>
  reverse conj_tac >- (qpat_assum `!pre f rest. _` ACCEPT_TAC) >>
  gvs[prov_sites_entry]
QED

Resume cut_sites_invariant[call]:
  rpt gen_tac >> strip_tac >> map_every qx_gen_tac [`n`, `raw0`] >> strip_tac >>
  `gas_cut n vs s` by
    (drule enters_block_readings >> drule gas_setup_callee_readings >>
     rpt strip_tac >> gvs[gas_cut_def]) >>
  qpat_x_assum `!n raw0. _` (qspecl_then [`n`, `raw0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  drule_then strip_assume_tac setup_callee_frame >>
  drule_then assume_tac fmpStageReclaimSoundTheory.fmp_enters_block_frontier >>
  conj_tac
  >- (simp[fmp_frame_base_def, prov_sites_def, param_sites_def, MEM_MAP] >>
      Cases >> simp[] >> rpt strip_tac >>
      qpat_x_assum `SOME _ = op_prov _ _` (assume_tac o SYM) >>
      drule_all prov_sites_op >> gvs[]) >>
  rpt gen_tac >> namedCases_on `pre` ["", "head tail"]
  >- (simp[] >> strip_tac >> gvs[] >> simp[]) >>
  pure_rewrite_tac[APPEND, CONS_11] >> strip_tac >>
  qpat_x_assum `!pre f rest. _` (qspecl_then [`tail`, `f`, `rest`] mp_tac) >>
  simp[]
QED

Resume cut_sites_invariant[ret]:
  rpt gen_tac >> strip_tac >> map_every qx_gen_tac [`n`, `raw0`] >> strip_tac >>
  `LENGTH s'.vs_gas_readings <= LENGTH s.vs_gas_readings` by
    (drule_all return_readings_le >> simp[]) >>
  `gas_cut n vs s` by
    (irule gas_cut_readings_mono >> qexists `s'` >> gvs[gas_cut_def]) >>
  qpat_x_assum `!n raw0. _` (qspecl_then [`n`, `raw0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  drule_all cut_sites_source_point >> strip_tac >>
  `ret.iret_adopt_fmp = NONE` by
    (irule (CONJUNCT1 run_defs_adopt_fmp_none) >>
     simp[GSYM CONJ_ASSOC] >> gvs[pre_fmp_opcode_def] >> metis_tac[]) >>
  `s'.vs_fmp = f.cf_state.vs_fmp` by
    (drule bind_outputs_allocation_frame >>
     simp[adopt_return_fmp_def, merge_callee_state_def]) >>
  conj_tac
  >- (qpat_assum `!pre f rest. _` (qspecl_then [`[]`, `f`, `stk`] mp_tac) >>
      simp[] >> strip_tac >> gvs[prov_sites_restrict]) >>
  map_every qx_gen_tac [`pre`, `saved`, `rest`] >> strip_tac >>
  qpat_x_assum `!pre f rest. _` (qspecl_then [`f::pre`, `saved`, `rest`] mp_tac) >>
  simp[]
QED

Finalise cut_sites_invariant[local]

Theorem focus_fmp_frame_sites_upto:
  o1_ctx_shape C /\ EVERY (o1_fn_row 3) C.ctx_functions /\
  raw0 = w2n vs.vs_fmp /\
  (!fn inst s. raw_reachable vs C fn inst s /\ gas_cut n vs s ==>
               dalloca_no_wrap inst s) /\
  frame_reachable vs C stk PG G tn fn inst s /\ gas_cut n vs s ==>
  raw0 <= fmp_frame_base raw0 stk /\
  fmp_frame_base raw0 stk <= w2n s.vs_fmp /\
  EVERY (\f. w2n f.cf_state.vs_fmp <= w2n s.vs_fmp) stk /\
  (!v b z. FLOOKUP G v = SOME (b,z) /\ 0 < z ==>
      raw0 <= b /\ b + z <= w2n s.vs_fmp) /\
  EVERY (\h. !b z. h = SOME (b,z) /\ 0 < z ==>
              b + z <= fmp_frame_base raw0 stk) PG
Proof
  strip_tac >> drule cut_sites_invariant >>
  disch_then (qspecl_then [`n`, `raw0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_x_assum `!pre f rest. _` kall_tac >>
  gvs[prov_sites_def, param_sites_def, EVERY_MEM] >>
  conj_tac >> rpt strip_tac
  >- (qpat_assum `!v site. _` drule >> simp[])
  >- (qpat_assum `!v site. _` drule >> simp[]) >>
  gvs[] >> first_x_assum drule >> simp[]
QED
