(* Control clauses transport the abort-sensitive terminal observation unchanged. *)
Theory o1LowerDloadRequestControl
Ancestors
  o1LowerDloadRequestRunner o1ContractLowerDloadSim
  o1LowerDloadEndpointConsumer o1LowerDloadJointRelation
  o1LowerDloadOccurrence o1LowerDloadRunnerBoundary o1PassLift
  venomExecProofs venomExecSemantics venomWf venomInst contextCodegenRel
  venomState list arithmetic passSimulationDefs o1PassContract ptrDiscipline

val requestClauses = strip_conj (fst (dest_imp
  (concl ld_request_runner_induction)));
val requestPacket = fst (strip_comb (fst (dest_imp
  (concl ld_request_runner_packet_terminates))));
val requestAssumptions = ``ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  o1_src_inv D C vs /\ callee_first names C.ctx_functions /\
  ptr_discipline lo C vs``;

Theorem ld_request_runner_run_clause:
  ^(List.nth(requestClauses,2))
Proof
  qabbrev_tac `RR = ^requestPacket` >> qabbrev_tac `AA = ^requestAssumptions` >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  `occ_frame_reachable vs C stk PG G tn fn i s1 n a U B HP H` by
    metis_tac[ld_joint_source] >>
  `wf_function fn` by
    (drule occ_frame_reachable_annotation >> strip_tac >>
     fs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[o1_fn_shape_def]) >>
  `active_inst fn i s1` by
    (drule occ_frame_reachable_projection >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `s1.vs_call_ctx = s.vs_call_ctx /\ s1.vs_halted = s.vs_halted` by
    metis_tac[ld_enters_block_call_ctx, ld_enters_block_halted] >>
  Cases_on `fuel` >- fs[Once run_blocks_def, terminates_def] >>
  qpat_assum `enters_block fn s s1`
    (strip_assume_tac o REWRITE_RULE [enters_block_def]) >>
  qpat_assum `enters_block fn' t0 t1`
    (strip_assume_tac o REWRITE_RULE [enters_block_def]) >> gvs[] >>
  `s_phi.vs_current_bb = s.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  `s_phi'.vs_current_bb = t0.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  `get_instruction bb (phi_prefix_length bb.bb_instructions) = SOME i` by
    (qpat_x_assum `active_inst fn i _` mp_tac >>
     simp[active_inst_def] >> strip_tac >>
     `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb''` by
       (irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >>
     gvs[get_instruction_def]) >>
  qmatch_goalsub_abbrev_tac `run_blocks (SUC k) C fn s` >>
  qmatch_asmsub_abbrev_tac `terminates (run_blocks (SUC k) C fn s)` >>
  qmatch_asmsub_abbrev_tac `enters_block fn s sin` >>
  `terminates (exec_block k C bb sin)` by
    (qpat_x_assum `terminates (run_blocks _ _ _ _)` mp_tac >>
     simp[Once run_blocks_def, Abbr `sin`] >>
     Cases_on `exec_block k C bb
       (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
     simp[terminates_def]) >>
  `lookup_block sin.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb sin.vs_inst_idx = SOME i` by simp[Abbr `sin`] >>
  gvs[] >> first_x_assum (drule_all_then strip_assume_tac) >> gvs[] >>
  qpat_x_assum `occ_frame_reachable _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `ld_joint_boundary _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `active_inst _ _ _` kall_tac >>
  qmatch_asmsub_abbrev_tac `RR stk PG fn a U HP ts A0 br bt` >>
  Cases_on `br`
  >- suspend "branch"
  >- suspend "halt"
  >- suspend "abort"
  >- suspend "return"
  >> fs[terminates_def]
QED

Resume ld_request_runner_run_clause[halt]:
  `?te. bt = Halt te` by fs[Abbr `RR`] >>
  qpat_x_assum `Abbrev (Halt v = _)`
    (assume_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `exec_block m C' bb'
      (s_phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) = Halt te` by
    fs[Abbr `bt`] >>
  qexists_tac `SUC m` >>
  simp[Once run_blocks_def] >> simp[Once run_blocks_def] >>
  qpat_x_assum `RR _ _ _ _ _ _ _ _ _ _` mp_tac >> simp[]
QED
Resume ld_request_runner_run_clause[abort]:
  `?te. bt = Abort a' te` by fs[Abbr `RR`] >>
  qpat_x_assum `Abbrev (Abort _ _ = _)`
    (assume_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `exec_block m C' bb'
      (s_phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) = Abort a' te` by
    fs[Abbr `bt`] >>
  qexists_tac `SUC m` >>
  simp[Once run_blocks_def] >> simp[Once run_blocks_def] >>
  qpat_x_assum `RR _ _ _ _ _ _ _ _ _ _` mp_tac >> simp[]
QED
Resume ld_request_runner_run_clause[return]:
  `?jr tr. bt = IntRet jr tr` by
    (fs[Abbr `RR`] >> metis_tac[]) >>
  qpat_x_assum `Abbrev (IntRet _ _ = _)`
    (assume_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `exec_block m C' bb'
      (s_phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) = IntRet jr tr` by
    fs[Abbr `bt`] >>
  qexists_tac `SUC m` >>
  simp[Once run_blocks_def] >> simp[Once run_blocks_def] >>
  qpat_x_assum `RR _ _ _ _ _ _ _ _ _ _` mp_tac >> simp[]
QED
Resume ld_request_runner_run_clause[branch]:
  qpat_x_assum `Abbrev (OK v = _)`
    (assume_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `~v.vs_halted` by metis_tac[exec_block_OK_not_halted] >>
  `terminates (run_blocks k C fn v)` by
    (qpat_x_assum `terminates (run_blocks (SUC k) C fn s)` mp_tac >>
     simp[Once run_blocks_def]) >>
  qpat_assum `Abbrev (RR = _)` (fn rr =>
    qpat_assum `RR _ _ _ _ _ _ _ _ _ _`
      (strip_assume_tac o SIMP_RULE (srw_ss())
        [REWRITE_RULE [markerTheory.Abbrev_def] rr])) >>
  `MEM bi.inst_opcode [JMP; JNZ; DJMP]` by simp[] >>
  `?sn. enters_block fn v sn` by
    (Cases_on `k` >- fs[Once run_blocks_def, terminates_def] >>
     Cases_on `lookup_block v.vs_current_bb fn.fn_blocks`
     >- fs[Once run_blocks_def, terminates_def] >>
     rename1 `lookup_block v.vs_current_bb fn.fn_blocks = SOME dest` >>
     `(?p. eval_phis v dest.bb_instructions = OK p) \/
      (?e. eval_phis v dest.bb_instructions = Error e)` by
       metis_tac[eval_phis_ok_or_error_defs] >>
     fs[Once run_blocks_def, terminates_def] >>
     simp[enters_block_def] >> metis_tac[]) >>
  drule_all (SIMP_RULE bool_ss [PULL_EXISTS] ld_branch_endpoint_consume) >>
  strip_tac >> gvs[] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  `terminates (run_blocks m' C' fn' te)` by
    (qpat_assum `Abbrev (RR = _)` (fn rr =>
      qpat_assum `RR _ _ _ _ _ _ _ _ (run_blocks k C fn v) _`
        (mp_tac o REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] rr])) >>
     CONV_TAC (LAND_CONV (DEPTH_CONV BETA_CONV)) >> disch_tac >>
     drule (SIMP_RULE (srw_ss()) [] ld_request_runner_packet_terminates) >> simp[]) >>
  `run_blocks (MAX m m') C' fn' te = run_blocks m' C' fn' te` by
    (irule run_blocks_terminates_mono >> simp[]) >>
  `exec_block (MAX m m') C' bb'
     (s_phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) = OK te` by
    (irule EQ_TRANS >>
     qexists_tac `exec_block m C' bb'
       (s_phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions)` >>
     conj_tac >- (irule exec_block_terminates_mono >> simp[terminates_def]) >>
     simp[]) >>
  `~te.vs_halted` by metis_tac[exec_block_OK_not_halted] >>
  `run_blocks (SUC k) C fn s = run_blocks k C fn v` by
    (qpat_assum `run_block_non_phis k C bb sin = OK v`
       (mp_tac o SIMP_RULE (srw_ss()) [Abbr `sin`]) >>
     simp[Once run_blocks_def]) >>
  `run_blocks (SUC (MAX m m')) C' fn' t0 = run_blocks m' C' fn' te` by
    simp[Once run_blocks_def] >>
  qexists_tac `SUC (MAX m m')` >> simp[]
QED
Finalise ld_request_runner_run_clause

Theorem ld_request_runner_step_clause:
  ^(List.nth(requestClauses,0))
Proof
  qabbrev_tac `RR = ^requestPacket` >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  drule_at (Pat `terminates _`) ld_terminating_invoke_inversion >>
  disch_then (qspecl_then [`s`, `fuel`, `inst`, `C`] mp_tac) >>
  simp[] >> strip_tac >>
  drule_all lower_dload_stage_invoke_entry >> strip_tac >>
  first_x_assum (drule_all_then strip_assume_tac o
    SIMP_RULE bool_ss [PULL_EXISTS]) >> gvs[] >>
  qpat_x_assum `RR _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `RR`] >> strip_tac
  >- suspend "return"
  >- suspend "halt"
  >> suspend "abort"
QED
Resume ld_request_runner_step_clause[return]:
  `wf_function fn` by
    (drule ld_joint_source >>
     disch_then (strip_assume_tac o MATCH_MP occ_frame_reachable_annotation) >>
     fs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[o1_fn_shape_def]) >>
  `cs.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address` by
    metis_tac[ld_setup_callee_call_ctx] >>
  drule_at (Pat `ld_joint_boundary _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    (SIMP_RULE bool_ss [PULL_EXISTS] ld_return_endpoint_consume) >>
  simp[] >> disch_then (drule_all_then strip_assume_tac) >>
  `s1.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address` by
    (qpat_x_assum `bind_outputs _ jr.iret_values _ = _` kall_tac >>
     qspec_then `\u. u.vs_call_ctx.cc_address` mp_tac
       venomInstProofs1Theory.bind_outputs_preserves >>
     simp[update_var_def] >> disch_then drule >>
     simp[adopt_return_fmp_def, merge_callee_state_def]) >>
  `step_inst m C' inst t = OK t1'` by simp[Once step_inst_def] >>
  qexists_tac `m` >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED
Resume ld_request_runner_step_clause[halt]:
  qexists_tac `m` >> simp[Once step_inst_def] >> simp[Once step_inst_def] >> gvs[]
QED
Resume ld_request_runner_step_clause[abort]:
  qexists_tac `m` >> simp[Once step_inst_def] >> simp[Once step_inst_def] >> gvs[]
QED
Finalise ld_request_runner_step_clause
