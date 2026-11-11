Theory o1LowerDloadRunnerExec
Ancestors
  gasEvents gasEventsFuel ctxLookupAgreeHelpers
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
  simp[ld_joint_boundary_def, ld_joint_frame_def, ld_joint_control_def] >>
  metis_tac[]
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
      `gas_events_block fuel C fn.fn_name bb s = []` by
        (`i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE` by
           (conj_tac >> strip_tac >> gvs[is_terminator_def]) >>
         simp[Once gas_events_block_def, gas_events_step_def]) >>
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
  gvs[] >> qexists_tac `m` >> simp[] >>
  sym_tac >> irule gas_events_block_nonterminator >> simp[]
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
      `fn'.fn_name = fn.fn_name` by metis_tac[lookup_function_selected_name] >>
      qexists_tac `m` >> gvs[Abbr `RR`] >>
      once_rewrite_tac[gas_events_block_def] >> simp[]) >>
  `taint_within D C vs` by fs[o1_src_inv_def] >>
  drule_all (SIMP_RULE bool_ss [PULL_EXISTS] ld_runner_halt_endpoint) >>
  strip_tac >> qexists_tac `fuel` >> gvs[Abbr `RR`] >>
  `i.inst_opcode <> GAS` by
    (drule step_inst_halt_opcodes >> rpt strip_tac >> gvs[]) >>
  simp[Once gas_events_block_def, gas_events_step_def]
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
      `fn'.fn_name = fn.fn_name` by metis_tac[lookup_function_selected_name] >>
      qexists_tac `m` >> gvs[Abbr `RR`] >>
      once_rewrite_tac[gas_events_block_def] >> simp[]) >>
  drule_all ld_runner_abort_endpoint >>
  strip_tac >> qexists_tac `fuel` >> gvs[Abbr `RR`] >>
  `i.inst_opcode <> GAS` by
    (drule step_inst_abort_opcodes >> rpt strip_tac >> gvs[]) >>
  simp[Once gas_events_block_def, gas_events_step_def]
QED

Resume ld_runner_exec_clause[ret]:
  rename1 `step_inst fuel C i s = IntRet ir se` >>
  `exec_block fuel C bb s = IntRet ir se` by simp[Once exec_block_def] >>
  Cases_on `i.inst_opcode = INVOKE`
  >- (gvs[terminates_def] >> metis_tac[]) >>
  `MEM fn C.ctx_functions` by
    (drule ld_joint_source >> strip_tac >>
     drule occ_frame_reachable_annotation >> simp[]) >>
  `MEM i (fn_insts fn)` by
    (fs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[MEM_EL]) >>
  `~is_raw_fmp_opcode i.inst_opcode /\ no_dret fn` by
    (fs[o1_src_inv_def, fmp_free_ctx_def, o1_ctx_shape_def, EVERY_MEM,
        o1_fn_shape_def, no_raw_fmp_ops_def] >> metis_tac[]) >>
  `i.inst_opcode = RET` by
    (drule step_inst_intret_opcodes >>
     fs[no_dret_def, EVERY_MEM] >> strip_tac >>
     gvs[is_raw_fmp_opcode_def]) >>
  drule_all ld_runner_ret_endpoint >> strip_tac >>
  `gas_events_block fuel C fn.fn_name bb s = []` by
    simp[Once gas_events_block_def, gas_events_step_def] >>
  qexists_tac `fuel` >> fs[Abbr `RR`] >> metis_tac[]
QED

Resume ld_runner_exec_clause[call_ok]:
  gvs[terminates_def] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  `~MEM i.inst_opcode [DLOAD; DLOADBYTES]` by simp[] >>
  drule_all ld_joint_unchanged_fetch >> strip_tac >>
  `wf_function fn` by
    (drule ld_joint_source >> strip_tac >> drule occ_frame_reachable_annotation >>
     strip_tac >> fs[o1_ctx_shape_def, EVERY_MEM] >>
     metis_tac[o1_fn_shape_def]) >>
  `get_instruction bb (SUC s.vs_inst_idx) = SOME next` by
    (qpat_x_assum `active_inst fn next _` mp_tac >>
     simp[active_inst_def] >> strip_tac >>
     `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb''` by
       (irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >>
     gvs[get_instruction_def]) >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  `t1.vs_current_bb = t.vs_current_bb` by
    (imp_res_tac ld_joint_current_bb >> fs[]) >>
  gvs[] >>
  `terminates (exec_block m' C' bb' (t1 with vs_inst_idx := SUC t.vs_inst_idx))` by
    (irule ld_runner_packet_terminates >>
     qpat_x_assum `RR _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Abbr `RR`] >> metis_tac[]) >>
  `step_inst (MAX m m') C' i t = OK t1` by
    (`terminates (step_inst m C' i t)` by simp[terminates_def] >>
     drule step_inst_terminates_mono >>
     disch_then (qspec_then `MAX m m'` mp_tac) >> simp[]) >>
  `exec_block (MAX m m') C' bb' (t1 with vs_inst_idx := SUC t.vs_inst_idx) =
   exec_block m' C' bb' (t1 with vs_inst_idx := SUC t.vs_inst_idx)` by
    (irule exec_block_terminates_mono >> simp[]) >>
  `exec_block fuel C bb s =
   exec_block fuel C bb (v with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[Once exec_block_def] >>
  `exec_block (MAX m m') C' bb' t =
   exec_block m' C' bb' (t1 with vs_inst_idx := SUC t.vs_inst_idx)` by
    simp[Once exec_block_def] >>
  `fn'.fn_name = fn.fn_name` by metis_tac[lookup_function_selected_name] >>
  `gas_events_step (MAX m m') C' fn.fn_name i t =
   gas_events_step m C' fn.fn_name i t` by
    (irule (cj 2 (cj 2 (cj 1 gas_events_fuel_extension))) >> simp[]) >>
  `gas_events_block (MAX m m') C' fn'.fn_name bb'
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) =
   gas_events_block m' C' fn'.fn_name bb'
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)` by
    (irule (cj 2 (cj 2 (cj 2 gas_events_fuel_extension))) >> simp[] >>
     Cases_on `exec_block m' C' bb' (t1 with vs_inst_idx := SUC t.vs_inst_idx)` >>
     fs[terminates_def]) >>
  qexists_tac `MAX m m'` >> simp[] >>
  once_rewrite_tac[gas_events_block_def] >> simp[is_terminator_def] >> gvs[]
QED
Finalise ld_runner_exec_clause

val _ = if null (hyp ld_runner_exec_clause) andalso
               aconv (concl ld_runner_exec_clause) ldExecClause
        then () else raise Fail "exec clause audit failed";
