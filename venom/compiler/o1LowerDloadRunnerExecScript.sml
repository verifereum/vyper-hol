Theory o1LowerDloadRunnerExec
Ancestors
  o1LowerDloadRunner o1LowerDloadNonCallContinuation
  o1LowerDloadRunnerEndpoints o1LowerDloadUnchangedFetch
  o1LowerDloadRunnerBoundary o1ContractSimplifyCfg o1ContractSimplifyCfgSrcFrame o1PassContract ptrDiscipline
  dretDesugarDefs opcodeClass o1PassLift
  o1LowerDloadJointRelation o1LowerDloadOccurrence
  passSimulationDefs venomExecSemantics venomExecProps venomInstProps
  venomInst venomWf contextCodegenRel list

val ldExecClause = snd (dest_conj (fst (dest_imp
  (concl ld_runner_conditional_induction))));
val ldPacket = fst (strip_comb (fst (dest_imp
  (concl ld_runner_packet_terminates))));

Theorem ld_joint_current_bb[local]:
  ld_joint_boundary vs C C' lo D stk PG G tn fn i s t
    n a U B HP H sites X ts ==> s.vs_current_bb = t.vs_current_bb
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_runner_exec_clause:
  ^ldExecClause
Proof
  qabbrev_tac `RR = ^ldPacket` >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[] >>
  `active_inst fn i s` by
    (drule ld_joint_source >>
     disch_then (strip_assume_tac o MATCH_MP occ_frame_reachable_projection) >>
     fs[Once frame_reachable_cases] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = RETURNDATACOPY /\ in_revert_forward fn s`
  >- (fs[] >>
      `exec_block fuel C bb s = exec_block fuel C bb s` by simp[] >>
      drule_all ld_runner_forward_endpoint >>
      strip_tac >> qexists_tac `fuel` >> gvs[Abbr `RR`]) >>
  Cases_on `step_inst fuel C i s`
  >- suspend "ok"
  >- suspend "halt"
  >- suspend "abort"
  >- suspend "ret"
  >> qpat_x_assum `terminates _` mp_tac >>
  simp[Once exec_block_def, terminates_def]
QED

Resume ld_runner_exec_clause[ok]:
  `~v.vs_halted` by metis_tac[ld_step_ok_halted] >>
  Cases_on `is_terminator i.inst_opcode`
  >- (drule_all ld_runner_branch_endpoint >> strip_tac >>
      qexists_tac `fuel` >>
      `exec_block fuel C bb s = OK v` by simp[Once exec_block_def] >>
      fs[Abbr `RR`] >> metis_tac[]) >>
  `v.vs_current_bb = s.vs_current_bb /\
   v.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address` by
    (conj_tac >- metis_tac[step_preserves_control_flow] >>
     metis_tac[ld_step_ok_call_ctx]) >>
  `terminates (exec_block fuel C bb (v with vs_inst_idx := SUC s.vs_inst_idx))` by
    (qpat_x_assum `terminates (exec_block fuel C bb s)` mp_tac >>
     simp[Once exec_block_def]) >>
  Cases_on `i.inst_opcode = INVOKE` >- suspend "call_ok" >>
  `~in_revert_forward fn s` by
    (spose_not_then assume_tac >>
     fs[in_revert_forward_def, revert_forward_at_def, revert_forward_pair_def] >>
     gvs[] >> fs[is_terminator_def]) >>
  drule_all (SIMP_RULE bool_ss [PULL_EXISTS] ld_joint_noncall_continue) >>
  strip_tac >>
  `wf_function fn` by
    (drule ld_joint_source >> strip_tac >> drule occ_frame_reachable_annotation >>
     strip_tac >> fs[o1_ctx_shape_def, EVERY_MEM] >>
     metis_tac[o1_fn_shape_def]) >>
  `get_instruction bb (SUC s.vs_inst_idx) = SOME inst2` by
    (qpat_x_assum `active_inst fn inst2 _` mp_tac >>
     simp[active_inst_def] >> strip_tac >>
     `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb''` by
       (irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >>
     gvs[get_instruction_def]) >>
  qpat_x_assum `!s''. _` (qspec_then `v` mp_tac) >> simp[] >>
  disch_then (drule_all_then strip_assume_tac) >>
  `tnext.vs_current_bb = t.vs_current_bb` by
    (imp_res_tac ld_joint_current_bb >> fs[]) >>
  `exec_block fuel C bb s =
   exec_block fuel C bb (v with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[Once exec_block_def] >>
  gvs[] >> qexists_tac `m` >> simp[]
QED

Resume ld_runner_exec_clause[halt]:
  rename1 `step_inst fuel C i s = Halt se` >>
  `exec_block fuel C bb s = Halt se` by simp[Once exec_block_def] >>
  Cases_on `i.inst_opcode = INVOKE`
  >- (gvs[terminates_def] >>
      first_x_assum (drule_all_then strip_assume_tac) >>
      `~MEM i.inst_opcode [DLOAD; DLOADBYTES]` by simp[] >>
      drule_all ld_joint_unchanged_fetch >> strip_tac >>
      `exec_block m C' bb' t = Halt te` by simp[Once exec_block_def] >>
      qexists_tac `m` >> gvs[Abbr `RR`]) >>
  `taint_within D C vs` by fs[o1_src_inv_def] >>
  drule_all (SIMP_RULE bool_ss [PULL_EXISTS] ld_runner_halt_endpoint) >>
  strip_tac >> qexists_tac `fuel` >> gvs[Abbr `RR`]
QED

Resume ld_runner_exec_clause[abort]:
  rename1 `step_inst fuel C i s = Abort reason se` >>
  `exec_block fuel C bb s = Abort reason se` by simp[Once exec_block_def] >>
  Cases_on `i.inst_opcode = INVOKE`
  >- (gvs[terminates_def] >>
      first_x_assum (drule_all_then strip_assume_tac) >>
      `~MEM i.inst_opcode [DLOAD; DLOADBYTES]` by simp[] >>
      drule_all ld_joint_unchanged_fetch >> strip_tac >>
      `exec_block m C' bb' t = Abort reason te` by simp[Once exec_block_def] >>
      qexists_tac `m` >> gvs[Abbr `RR`]) >>
  drule_all ld_runner_abort_endpoint >>
  strip_tac >> qexists_tac `fuel` >> gvs[Abbr `RR`]
QED

Resume ld_runner_exec_clause[ret]:
  (* P4a in progress *) cheat
QED

Resume ld_runner_exec_clause[call_ok]:
  (* P4a in progress *) cheat
QED
Finalise ld_runner_exec_clause

val _ = if null (hyp ld_runner_exec_clause) andalso
               aconv (concl ld_runner_exec_clause) ldExecClause
        then () else raise Fail "exec clause audit failed";

val ldExecClauseFuel = snd (dest_conj (fst (dest_imp
  (concl ld_runner_conditional_induction_fuel))));

Theorem ld_runner_exec_clause_fuel:
  ^ldExecClauseFuel
Proof
  qabbrev_tac `RR = ^ldPacket` >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[] >>
  `active_inst fn i s` by
    (drule ld_joint_source >>
     disch_then (strip_assume_tac o MATCH_MP occ_frame_reachable_projection) >>
     fs[Once frame_reachable_cases] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = RETURNDATACOPY /\ in_revert_forward fn s`
  >- (fs[] >>
      `exec_block fuel C bb s = exec_block fuel C bb s` by simp[] >>
      drule_all ld_runner_forward_endpoint >>
      strip_tac >> gvs[Abbr `RR`]) >>
  Cases_on `step_inst fuel C i s`
  >- suspend "ok"
  >- suspend "halt"
  >- suspend "abort"
  >- suspend "ret"
  >> qpat_x_assum `terminates _` mp_tac >>
  simp[Once exec_block_def, terminates_def]
QED

Resume ld_runner_exec_clause_fuel[ok]:
  `~v.vs_halted` by metis_tac[ld_step_ok_halted] >>
  Cases_on `is_terminator i.inst_opcode`
  >- (drule_all ld_runner_branch_endpoint >> strip_tac >>
      `exec_block fuel C bb s = OK v` by simp[Once exec_block_def] >>
      fs[Abbr `RR`] >> metis_tac[]) >>
  `v.vs_current_bb = s.vs_current_bb /\
   v.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address` by
    (conj_tac >- metis_tac[step_preserves_control_flow] >>
     metis_tac[ld_step_ok_call_ctx]) >>
  `terminates (exec_block fuel C bb (v with vs_inst_idx := SUC s.vs_inst_idx))` by
    (qpat_x_assum `terminates (exec_block fuel C bb s)` mp_tac >>
     simp[Once exec_block_def]) >>
  Cases_on `i.inst_opcode = INVOKE` >- suspend "call_ok" >>
  `~in_revert_forward fn s` by
    (spose_not_then assume_tac >>
     fs[in_revert_forward_def, revert_forward_at_def, revert_forward_pair_def] >>
     gvs[] >> fs[is_terminator_def]) >>
  drule_all (SIMP_RULE bool_ss [PULL_EXISTS] ld_joint_noncall_continue) >>
  strip_tac >>
  `wf_function fn` by
    (drule ld_joint_source >> strip_tac >> drule occ_frame_reachable_annotation >>
     strip_tac >> fs[o1_ctx_shape_def, EVERY_MEM] >>
     metis_tac[o1_fn_shape_def]) >>
  `get_instruction bb (SUC s.vs_inst_idx) = SOME inst2` by
    (qpat_x_assum `active_inst fn inst2 _` mp_tac >>
     simp[active_inst_def] >> strip_tac >>
     `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb''` by
       (irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >>
     gvs[get_instruction_def]) >>
  qpat_x_assum `!s''. _` (qspec_then `v` mp_tac) >> simp[] >>
  disch_then (drule_all_then strip_assume_tac) >>
  `tnext.vs_current_bb = t.vs_current_bb` by
    (imp_res_tac ld_joint_current_bb >> fs[]) >>
  `exec_block fuel C bb s =
   exec_block fuel C bb (v with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[Once exec_block_def] >>
  gvs[] >> simp[]
QED

Resume ld_runner_exec_clause_fuel[halt]:
  rename1 `step_inst fuel C i s = Halt se` >>
  `exec_block fuel C bb s = Halt se` by simp[Once exec_block_def] >>
  Cases_on `i.inst_opcode = INVOKE`
  >- (gvs[terminates_def] >>
      first_x_assum (drule_all_then strip_assume_tac) >>
      `~MEM i.inst_opcode [DLOAD; DLOADBYTES]` by simp[] >>
      drule_all ld_joint_unchanged_fetch >> strip_tac >>
      `exec_block fuel C' bb' t = Halt te` by simp[Once exec_block_def] >>
      gvs[Abbr `RR`]) >>
  `taint_within D C vs` by fs[o1_src_inv_def] >>
  drule_all (SIMP_RULE bool_ss [PULL_EXISTS] ld_runner_halt_endpoint) >>
  strip_tac >> gvs[Abbr `RR`]
QED

Resume ld_runner_exec_clause_fuel[abort]:
  rename1 `step_inst fuel C i s = Abort reason se` >>
  `exec_block fuel C bb s = Abort reason se` by simp[Once exec_block_def] >>
  Cases_on `i.inst_opcode = INVOKE`
  >- (gvs[terminates_def] >>
      first_x_assum (drule_all_then strip_assume_tac) >>
      `~MEM i.inst_opcode [DLOAD; DLOADBYTES]` by simp[] >>
      drule_all ld_joint_unchanged_fetch >> strip_tac >>
      `exec_block fuel C' bb' t = Abort reason te` by simp[Once exec_block_def] >>
      gvs[Abbr `RR`]) >>
  drule_all ld_runner_abort_endpoint >>
  strip_tac >> gvs[Abbr `RR`]
QED

Resume ld_runner_exec_clause_fuel[ret]:
  (* P4a in progress *) cheat
QED

Resume ld_runner_exec_clause_fuel[call_ok]:
  (* P4a in progress *) cheat
QED
Finalise ld_runner_exec_clause_fuel

val _ = if null (hyp ld_runner_exec_clause_fuel) andalso
               aconv (concl ld_runner_exec_clause_fuel) ldExecClauseFuel
        then () else raise Fail "exact-fuel exec clause audit failed";
