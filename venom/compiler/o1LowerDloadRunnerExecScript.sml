Theory o1LowerDloadRunnerExec
Ancestors
  gasEvents gasEventsFuel ctxLookupAgreeHelpers
  o1LowerDloadRunner o1LowerDloadNonCallContinuation
  o1LowerDloadRunnerEndpoints o1LowerDloadUnchangedFetch
  o1LowerDloadRunnerBoundary o1ContractSimplifyCfg o1ContractSimplifyCfgSrcFrame o1PassContract ptrDiscipline o1SafeUpto
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

Theorem ld_silent_events_nil[local]:
  !d s. jt = d + s.vs_inst_idx /\
    (!k inst. s.vs_inst_idx <= k /\ k <= jt /\
              get_instruction bb k = SOME inst ==>
              inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE) /\
    (!inst. get_instruction bb jt = SOME inst ==>
            is_terminator inst.inst_opcode) ==>
    gas_events_block fuel C owner bb s = []
Proof
  Induct
  >- (rpt strip_tac >> gvs[] >>
      CONV_TAC (LHS_CONV (REWR_CONV gas_events_block_def)) >>
      Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
      rename1 `get_instruction bb s.vs_inst_idx = SOME x` >>
      `x.inst_opcode <> GAS /\ x.inst_opcode <> INVOKE /\
       is_terminator x.inst_opcode` by
        (first_x_assum (qspecl_then [`s.vs_inst_idx`, `x`] mp_tac) >> simp[]) >>
      simp[gas_events_step_def] >>
      Cases_on `step_inst fuel C x s` >> simp[]) >>
  rpt strip_tac >>
  CONV_TAC (LHS_CONV (REWR_CONV gas_events_block_def)) >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME x` >>
  `x.inst_opcode <> GAS /\ x.inst_opcode <> INVOKE` by
    (first_x_assum (qspecl_then [`s.vs_inst_idx`, `x`] mp_tac) >> simp[]) >>
  simp[gas_events_step_def] >>
  Cases_on `step_inst fuel C x s` >> simp[] >>
  Cases_on `is_terminator x.inst_opcode` >> simp[] >>
  first_x_assum irule >> simp[] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`k`, `inst`] mp_tac) >> simp[]
QED

Theorem ld_silent_to_terminator[local]:
  s.vs_inst_idx <= jt /\
  (!k inst. s.vs_inst_idx <= k /\ k <= jt /\
            get_instruction bb k = SOME inst ==>
            inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE) /\
  (!inst. get_instruction bb jt = SOME inst ==>
          is_terminator inst.inst_opcode) ==>
  gas_events_block fuel C owner bb s = []
Proof
  strip_tac >>
  qspecl_then [`jt - s.vs_inst_idx`, `s`] mp_tac ld_silent_events_nil >>
  simp[] >> impl_tac >- first_assum ACCEPT_TAC >> simp[]
QED

(* A revert forwarding runs RETURNDATACOPY, ASSIGNs and REVERT: no GAS and
   no INVOKE, so it reads no gas events. *)
Theorem ld_revert_forward_events_nil[local]:
  in_revert_forward fn s /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
  gas_events_block fuel C owner bb s = []
Proof
  simp[in_revert_forward_def, revert_forward_at_def] >> rpt strip_tac >>
  gvs[revert_forward_pair_def] >> irule ld_silent_to_terminator
  >- (qexists_tac `j` >> simp[is_terminator_def] >> rpt strip_tac >>
      Cases_on `k = s.vs_inst_idx` >> gvs[] >>
      Cases_on `k = j` >> gvs[] >>
      `inst.inst_opcode = ASSIGN` by
        (first_x_assum irule >> qexists_tac `k` >> simp[]) >>
      gvs[]) >>
  qexists_tac `s.vs_inst_idx` >> simp[is_terminator_def] >> rpt strip_tac >>
  `k = s.vs_inst_idx` by decide_tac >> gvs[]
QED

val ld_c2_stop_tac =
  strip_tac >>
  `LENGTH (gas_events_block fuel C fn.fn_name bb s) =
   LENGTH (gas_events_step fuel C fn.fn_name i s)` by
    (AP_TERM_TAC >> irule ld_block_events_step_stop >> simp[]) >>
  `F` suffices_by simp[] >> decide_tac;

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
  `gas_cut ncut vs s` by metis_tac[ld_budget_cut] >>
  `ptr_discipline_upto lo ncut C vs /\ taint_within_upto D ncut C vs /\
   fmp_free_ctx C` by fs[o1_safe_upto_def, o1_ptr_safe_upto_def] >>
  `LENGTH (gas_events_step fuel C fn.fn_name i s) <=
   LENGTH (gas_events_block fuel C fn.fn_name bb s)` by
    (irule ld_block_events_step_length >> simp[]) >>
  Cases_on `j <= LENGTH (gas_events_step fuel C fn.fn_name i s)`
  >- suspend "step_prefix" >>
  `LENGTH (gas_events_step fuel C fn.fn_name i s) < j` by decide_tac >>
  Cases_on `i.inst_opcode = RETURNDATACOPY /\ in_revert_forward fn s`
  >- (`gas_events_block fuel C fn.fn_name bb s = []` by
        metis_tac[ld_revert_forward_events_nil] >>
      reverse conj_tac >- (strip_tac >> gvs[]) >>
      strip_tac >> fs[] >>
      `exec_block fuel C bb s = exec_block fuel C bb s` by simp[] >>
      drule_all ld_runner_forward_endpoint >>
      strip_tac >> qexists_tac `fuel` >> gvs[Abbr `RR`]) >>
  Cases_on `step_inst fuel C i s`
  >- suspend "ok"
  >- suspend "halt"
  >- suspend "abort"
  >- suspend "ret"
  >> conj_tac
  >- (strip_tac >> qpat_x_assum `terminates _` mp_tac >>
      simp[Once exec_block_def, terminates_def])
  >> ld_c2_stop_tac
QED

Resume ld_runner_exec_clause[step_prefix]:
  conj_tac >- (strip_tac >> `F` suffices_by simp[] >> decide_tac) >>
  strip_tac >>
  `~(i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE)` by
    (strip_tac >> fs[gas_events_step_def]) >>
  `~MEM i.inst_opcode [DLOAD; DLOADBYTES]` by
    (Cases_on `i.inst_opcode = GAS` >> Cases_on `i.inst_opcode = INVOKE` >>
     gvs[]) >>
  drule_all ld_joint_unchanged_fetch >> strip_tac >>
  `fn'.fn_name = fn.fn_name` by metis_tac[lookup_function_selected_name] >>
  `?m. TAKE j (gas_events_step m C' fn.fn_name i t) =
       TAKE j (gas_events_step fuel C fn.fn_name i s)` by
    (Cases_on `i.inst_opcode = GAS`
     >- (qexists_tac `fuel` >> simp[gas_events_step_def]) >>
     `i.inst_opcode = INVOKE` by
       (Cases_on `i.inst_opcode = INVOKE` >> gvs[]) >>
     first_x_assum (drule_all_then (mp_tac o CONJUNCT2)) >>
     impl_tac >- decide_tac >> strip_tac >> qexists_tac `m` >> simp[]) >>
  qexistsl_tac [`m`, `fn'`, `bb'`] >> simp[] >>
  qspecl_then [`m`,`C'`,`fn.fn_name`,`bb'`,`t`,`i`] mp_tac
    ld_block_events_unfold >>
  qspecl_then [`fuel`,`C`,`fn.fn_name`,`bb`,`s`,`i`] mp_tac
    ld_block_events_unfold >>
  simp[] >> rpt (disch_then SUBST1_TAC) >>
  irule ld_take_append_eq >> simp[]
QED

Resume ld_runner_exec_clause[ok]:
  `~v.vs_halted` by metis_tac[ld_step_ok_halted] >>
  Cases_on `is_terminator i.inst_opcode`
  >- (reverse conj_tac >- ld_c2_stop_tac >> strip_tac >>
      drule_all ld_runner_branch_endpoint >> strip_tac >>
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
  `exec_block fuel C bb s =
   exec_block fuel C bb (v with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[Once exec_block_def] >>
  `gas_events_block fuel C fn.fn_name bb s =
   gas_events_step fuel C fn.fn_name i s ++
   gas_events_block fuel C fn.fn_name bb (v with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule gas_events_block_nonterminator >> simp[]) >>
  `j - LENGTH (gas_events_step fuel C fn.fn_name i s) +
     LENGTH vs.vs_gas_readings <= ncut + LENGTH v.vs_gas_readings /\
   0 < j - LENGTH (gas_events_step fuel C fn.fn_name i s)` by
    (irule ld_step_budget >> simp[]) >>
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
  conj_tac
  >- (strip_tac >>
      qpat_x_assum `terminates _ /\ _ < _ ==> _` mp_tac >>
      impl_tac >- (fs[] >> decide_tac) >> strip_tac >>
      gvs[] >> qexists_tac `m` >> simp[]) >>
  strip_tac >>
  qpat_x_assum `_ <= _ ==> _` mp_tac >>
  impl_tac >- (fs[] >> decide_tac) >> strip_tac >>
  gvs[] >> qexists_tac `m` >> simp[] >>
  irule ld_take_append_right >> simp[]
QED

Resume ld_runner_exec_clause[halt]:
  rename1 `step_inst fuel C i s = Halt se` >>
  `exec_block fuel C bb s = Halt se` by simp[Once exec_block_def] >>
  reverse conj_tac >- ld_c2_stop_tac >>
  strip_tac >>
  Cases_on `i.inst_opcode = INVOKE`
  >- (gvs[] >>
      `0 < j /\ LENGTH (gas_events_step fuel C fn.fn_name i s) < j` by decide_tac >>
      first_x_assum (drule_all_then (mp_tac o CONJUNCT1)) >>
      impl_tac >- (simp[terminates_def] >> decide_tac) >> strip_tac >>
      `~MEM i.inst_opcode [DLOAD; DLOADBYTES]` by simp[] >>
      drule_all ld_joint_unchanged_fetch >> strip_tac >>
      `exec_block m C' bb' t = Halt te` by simp[Once exec_block_def] >>
      `fn'.fn_name = fn.fn_name` by metis_tac[lookup_function_selected_name] >>
      qexists_tac `m` >> gvs[Abbr `RR`] >>
      once_rewrite_tac[gas_events_block_def] >> simp[]) >>
  drule_all (SIMP_RULE bool_ss [PULL_EXISTS] ld_runner_halt_endpoint) >>
  strip_tac >> qexists_tac `fuel` >> gvs[Abbr `RR`] >>
  `i.inst_opcode <> GAS` by
    (drule step_inst_halt_opcodes >> rpt strip_tac >> gvs[]) >>
  simp[Once gas_events_block_def, gas_events_step_def]
QED

Resume ld_runner_exec_clause[abort]:
  rename1 `step_inst fuel C i s = Abort reason se` >>
  `exec_block fuel C bb s = Abort reason se` by simp[Once exec_block_def] >>
  reverse conj_tac >- ld_c2_stop_tac >>
  strip_tac >>
  Cases_on `i.inst_opcode = INVOKE`
  >- (gvs[] >>
      `0 < j /\ LENGTH (gas_events_step fuel C fn.fn_name i s) < j` by decide_tac >>
      first_x_assum (drule_all_then (mp_tac o CONJUNCT1)) >>
      impl_tac >- (simp[terminates_def] >> decide_tac) >> strip_tac >>
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
  reverse conj_tac >- ld_c2_stop_tac >>
  strip_tac >>
  Cases_on `i.inst_opcode = INVOKE`
  >- (gvs[] >>
      `0 < j /\ LENGTH (gas_events_step fuel C fn.fn_name i s) < j` by decide_tac >>
      first_x_assum (drule_all_then (mp_tac o CONJUNCT1)) >>
      simp[terminates_def]) >>
  `MEM fn C.ctx_functions` by
    (drule ld_joint_source >> strip_tac >>
     drule occ_frame_reachable_annotation >> simp[]) >>
  `MEM i (fn_insts fn)` by
    (fs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[MEM_EL]) >>
  `~is_raw_fmp_opcode i.inst_opcode /\ no_dret fn` by
    (fs[fmp_free_ctx_def, o1_ctx_shape_def, EVERY_MEM,
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
  gvs[] >>
  `0 < j /\ LENGTH (gas_events_step fuel C fn.fn_name i s) < j` by decide_tac >>
  first_x_assum (drule_all_then (mp_tac o CONJUNCT1)) >>
  impl_tac >- (simp[terminates_def] >> decide_tac) >> strip_tac >>
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
  `j - LENGTH (gas_events_step fuel C fn.fn_name i s) +
     LENGTH vs.vs_gas_readings <= ncut + LENGTH v.vs_gas_readings /\
   0 < j - LENGTH (gas_events_step fuel C fn.fn_name i s)` by
    (irule ld_step_budget >> simp[]) >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  `t1.vs_current_bb = t.vs_current_bb` by
    (imp_res_tac ld_joint_current_bb >> fs[]) >>
  `fn'.fn_name = fn.fn_name` by metis_tac[lookup_function_selected_name] >>
  `!m2. m <= m2 ==>
     step_inst m2 C' i t = OK t1 /\
     gas_events_step m2 C' fn.fn_name i t = gas_events_step m C' fn.fn_name i t` by
    (rpt strip_tac
     >- (`terminates (step_inst m C' i t)` by simp[terminates_def] >>
         drule step_inst_terminates_mono >>
         disch_then (qspec_then `m2` mp_tac) >> simp[]) >>
     irule (cj 2 (cj 2 (cj 1 gas_events_fuel_extension))) >> simp[]) >>
  `!m2. m <= m2 ==>
     exec_block m2 C' bb' t =
       exec_block m2 C' bb' (t1 with vs_inst_idx := SUC t.vs_inst_idx) /\
     gas_events_block m2 C' fn.fn_name bb' t =
       gas_events_step fuel C fn.fn_name i s ++
       gas_events_block m2 C' fn.fn_name bb'
         (t1 with vs_inst_idx := SUC t.vs_inst_idx)` by
    (rpt strip_tac
     >- (first_x_assum (qspec_then `m2` mp_tac) >> simp[] >> strip_tac >>
         simp[Once exec_block_def]) >>
     first_x_assum (qspec_then `m2` mp_tac) >> simp[] >> strip_tac >>
     `gas_events_step fuel C fn.fn_name i s =
      gas_events_step m2 C' fn.fn_name i t` by simp[] >>
     pop_assum SUBST1_TAC >>
     irule gas_events_block_nonterminator >> simp[]) >>
  conj_tac
  >- (strip_tac >>
      qpat_x_assum `terminates _ /\ _ < _ ==> _` mp_tac >>
      impl_tac >- (fs[] >> decide_tac) >> strip_tac >>
      gvs[] >>
      rename1 `RR _ _ _ _ _ _ _ _ _ (exec_block mx C' _ (t1 with vs_inst_idx := _))` >>
      `terminates (exec_block mx C' bb' (t1 with vs_inst_idx := SUC t.vs_inst_idx))` by
        (irule ld_runner_packet_terminates >>
         qpat_x_assum `RR _ _ _ _ _ _ _ _ _ _` mp_tac >>
         simp[Abbr `RR`] >> metis_tac[]) >>
      `exec_block (MAX m mx) C' bb' (t1 with vs_inst_idx := SUC t.vs_inst_idx) =
       exec_block mx C' bb' (t1 with vs_inst_idx := SUC t.vs_inst_idx)` by
        (irule exec_block_terminates_mono >> simp[]) >>
      `gas_events_block (MAX m mx) C' fn.fn_name bb'
          (t1 with vs_inst_idx := SUC t.vs_inst_idx) =
       gas_events_block mx C' fn.fn_name bb'
          (t1 with vs_inst_idx := SUC t.vs_inst_idx)` by
        (irule (cj 2 (cj 2 (cj 2 gas_events_fuel_extension))) >> simp[] >>
         Cases_on `exec_block mx C' bb' (t1 with vs_inst_idx := SUC t.vs_inst_idx)` >>
         fs[terminates_def]) >>
      `m <= MAX m mx` by simp[] >>
      qexists_tac `MAX m mx` >> simp[]) >>
  strip_tac >>
  qpat_x_assum `_ <= _ ==> _` mp_tac >>
  impl_tac >- (fs[] >> decide_tac) >> strip_tac >>
  gvs[] >>
  rename1 `TAKE _ (gas_events_block mx C' _ _ (t1 with vs_inst_idx := _))` >>
  `TAKE (j - LENGTH (gas_events_step fuel C fn.fn_name i s))
     (gas_events_block (MAX m mx) C' fn.fn_name bb'
        (t1 with vs_inst_idx := SUC t.vs_inst_idx)) =
   TAKE (j - LENGTH (gas_events_step fuel C fn.fn_name i s))
     (gas_events_block mx C' fn.fn_name bb'
        (t1 with vs_inst_idx := SUC t.vs_inst_idx))` by
    (irule ld_block_events_fuel_take >> simp[] >>
     `j - LENGTH (gas_events_step fuel C fn.fn_name i s) <=
      LENGTH (gas_events_block mx C' fn.fn_name bb'
                (t1 with vs_inst_idx := SUC t.vs_inst_idx))` by
       (irule ld_take_length >>
        qexists_tac `gas_events_block fuel C fn.fn_name bb
                       (v with vs_inst_idx := SUC s.vs_inst_idx)` >>
        conj_tac >- simp[] >> fs[] >> decide_tac) >>
     decide_tac) >>
  `m <= MAX m mx` by simp[] >>
  qexists_tac `MAX m mx` >> simp[] >>
  irule ld_take_append_right >> simp[]
QED
Finalise ld_runner_exec_clause

val _ = if null (hyp ld_runner_exec_clause) andalso
               aconv (concl ld_runner_exec_clause) ldExecClause
        then () else raise Fail "exec clause audit failed";
