(* Advance a bounded successful LowerDload body at its actual next fetch. *)
Theory gasFocusLowerDloadNonInvokeNext
Ancestors
  gasFocusLowerDloadImageBodyNext gasFocusLowerDloadWriteCopyDispatch
  gasFocusLowerDloadEnvironmentNext gasFocusLowerDloadDallocaNext
  gasFocusLowerDloadFreshAllocaNext gasFocusLowerDloadCachedAllocaNext
  gasFocusLowerDloadArithmeticNext gasFocusLowerDloadClassifiedReadNext
  gasFocusLowerDloadAssignmentParamNext gasFocusLowerDloadObservationalReadNext
  gasFocusLowerDloadLogNext gasFocusLowerDloadStorageWriteNext
  gasFocusLowerDloadResidualDataEffect gasFocusLowerDloadExternalSingletonEffect
  lowerDloadNormalDispatch lowerDloadSafetyAdvance lowerDloadSafetyLocations
  lowerDloadPublicTrace lowerDloadReturnOrdinary lowerDloadEnvelopeControl
  lowerDloadSafetyRelation lowerDloadReturnAlignment lowerDloadDefs
  lowerDloadSafetyKernel lowerDloadExpansionEndpoint o1ContractLowerDload
  lowerDloadSourceInterface o1PassContract o1SafeUpto venomInstProps venomExecSemantics
  lowerDloadSafetyAmbient lowerDloadOracleCallAssembly
  contextCodegenRel venomInst venomWf venomExecProofs opcodeClass list arithmetic
Libs
  lowerDloadReturnPackageLib

Theorem ld_focus_noninvoke_body_next:
  o1_ctx_shape C /\ o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\
  code_layout_valid vs /\ EVERY pre_fmp_ops C.ctx_functions /\ o1_safe_upto D lo n C vs /\
  ld_sync lo P C vs stk PG G tn fn inst s t0 A frames N /\
  ^ld_probe_stable lo P Sigma names fs f0 A0 A frames /\
  gn = ld_image (HD frames) /\
  ld_envelope (HD frames).lf_supply fn s s.vs_inst_idx X p /\
  ld_prefix C' gn X p h t0 t /\
  lookup_block t.vs_current_bb gn.fn_blocks = SOME bb /\
  ld_return_cont C fn cs s /\
  s.vs_gas_readings = t0.vs_gas_readings /\
  t0.vs_gas_readings = t.vs_gas_readings /\
  EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
             LENGTH s.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) frames /\
  get_instruction bb t.vs_inst_idx = SOME ti /\
  ir_supply_covers_fn (HD frames).lf_supply fn /\
  ti.inst_opcode <> INVOKE /\ ~is_terminator ti.inst_opcode /\
  step_inst fuel C' ti t = OK u /\
  (let q = u with vs_inst_idx := SUC t.vs_inst_idx in
     run_block_non_phis fuel C' bb q = z /\
     ((?v. z = OK v /\ gas_cut n vs v) \/ (?rt v. z = IntRet rt v /\ gas_cut n vs v))) ==>
  let q = u with vs_inst_idx := SUC t.vs_inst_idx in
  ?PG1 G1 tn1 i s1 b1 A1 frames1 N1 Y p1 h1 j.
    ld_sync lo P C vs stk PG1 G1 tn1 fn i s1 b1 A1 frames1 N1 /\
    ^ld_probe_stable lo P Sigma names fs f0 A0 A1 frames1 /\
    gn = ld_image (HD frames1) /\
    ld_envelope (HD frames1).lf_supply fn s1 s1.vs_inst_idx Y p1 /\
    b1.vs_inst_idx = p1 /\ ld_prefix C' gn Y p1 h1 b1 q /\
    lookup_block q.vs_current_bb gn.fn_blocks = SOME bb /\
    get_instruction bb q.vs_inst_idx = SOME j /\ h1 < LENGTH Y /\ j = EL h1 Y /\
    ld_return_cont C fn cs s1 /\
    s1.vs_gas_readings = b1.vs_gas_readings /\ b1.vs_gas_readings = q.vs_gas_readings /\
    EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
               LENGTH s1.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) frames1
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  reverse (Cases_on `X = [inst]`)
  >- (drule_all (BETA_RULE (REWRITE_RULE [LET_THM] ld_focus_image_body_next)) >> simp[]) >>
  Cases_on `MEM ti.inst_opcode [MSTORE;MSTORE8;MCOPY;CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY]`
  >- (drule_all (BETA_RULE (REWRITE_RULE [LET_THM] ld_focus_write_copy_successor_point)) >> simp[]) >>
  `?f. frames = f::fs` by (Cases_on `frames` >> gns[]) >>
  qpat_x_assum `frames = _` SUBST_ALL_TAC >>
  RULE_ASSUM_TAC (REWRITE_RULE [HD, TL]) >>
  drule ld_sync_source >> strip_tac >>
  `f.lf_fn = fn` by (drule ld_sync_active >> simp[HD]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) gn.fn_blocks)` by
    (qpat_assum `gn = ld_image _` SUBST1_TAC >>
     pure_rewrite_tac[ld_image_def] >>
     qpat_assum `f.lf_fn = fn` SUBST1_TAC >>
     Cases_on `lower_dload_function_supply f.lf_supply fn` >>
     drule lower_dload_function_supply_labels >> simp[fn_labels_def]) >>
  `h < LENGTH X` by metis_tac[ld_prefix_bound] >>
  `h = 0` by gns[] >>
  qpat_x_assum `h = 0` SUBST_ALL_TAC >>
  qpat_x_assum `X = [inst]` SUBST_ALL_TAC >>
  `active_inst gn inst t` by
    (drule ld_prefix_active >> simp[]) >>
  `ti = inst` by
    (drule_all ld_active_lookup >> simp[] >> strip_tac >> gvs[get_instruction_def]) >>
  `t0 = t` by metis_tac[ld_prefix_zero] >>
  qpat_x_assum `ti = inst` SUBST_ALL_TAC >>
  qpat_x_assum `t0 = t` SUBST_ALL_TAC >>
  `t.vs_inst_idx = p` by (drule_all ld_sync_envelope_position >> simp[]) >>
  qpat_assum `gn = ld_image f` SUBST_ALL_TAC >>
  Cases_on `MEM inst.inst_opcode [CALLER;ADDRESS;CALLVALUE;GAS;ORIGIN;GASPRICE;CHAINID;COINBASE;
      TIMESTAMP;NUMBER;PREVRANDAO;GASLIMIT;BASEFEE;BLOBBASEFEE;CALLDATASIZE;RETURNDATASIZE;CODESIZE]`
  >- suspend "environment" >>
  Cases_on `inst.inst_opcode = DALLOCA` >- suspend "dalloca" >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
      >- suspend "fresh" >> rename1 `FLOOKUP _ _ = SOME bm` >>
      PairCases_on `bm` >> suspend "cached") >>
  Cases_on `MEM inst.inst_opcode [MUL;Div;Mod;SDIV;SMOD;Exp;ADDMOD;MULMOD;SLT;SGT;
      ISZERO;AND;OR;XOR;NOT;SIGNEXTEND;BYTE;OFFSET;ADD;SUB;SHL;SHR;SAR]`
  >- suspend "arithmetic" >>
  Cases_on `MEM inst.inst_opcode [MLOAD;ILOAD;LT;GT;EQ]` >- suspend "classified" >>
  Cases_on `MEM inst.inst_opcode [ASSIGN;RETPC_PARAM;PARAM]` >- suspend "assign" >>
  Cases_on `MEM inst.inst_opcode [BLOCKHASH;BLOBHASH;CALLDATALOAD;BALANCE;SELFBALANCE;
      EXTCODESIZE;EXTCODEHASH;SLOAD;TLOAD]` >- suspend "read" >>
  Cases_on `inst.inst_opcode = LOG` >- suspend "log" >>
  Cases_on `MEM inst.inst_opcode [SSTORE;TSTORE]` >- suspend "storage" >>
  Cases_on `MEM inst.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE;ISTORE;SHA3;INITIAL_FMP;BUMP] \/
    MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2]`
  >- suspend "residual" >> suspend "complement"
QED

(* All unchanged ordinary images resume at index zero of the next envelope. *)
local
  fun body_point_with alloc =
    qexistsl_tac [`PG`, `step_prov PG G inst ss`, `step_taint inst s ss tn`, `i`,
      `ss with vs_inst_idx := SUC s.vs_inst_idx`, `u with vs_inst_idx := SUC t.vs_inst_idx`,
      alloc, `g::fs`, `N`, `Y`, `SUC t.vs_inst_idx`, `0`, `HD Y`] >>
    gnvs[EL, EVERY_MEM] >> metis_tac[]
  fun body_case th =
    drule_all (REWRITE_RULE [HD, TL, NOT_CONS_NIL]
      (Q.INST [`fs0` |-> `fs`] (BETA_RULE th))) >>
    disch_then (qx_choose_then `ss` (qx_choose_then `g`
      (qx_choose_then `i` (qx_choose_then `Y` strip_assume_tac)))) >>
    body_point_with `A`
in
  val ordinary_body_case = body_case
  val body_point_with = body_point_with
end

Resume ld_focus_noninvoke_body_next[environment]:
  ordinary_body_case ld_focus_environment_body_next
QED
Resume ld_focus_noninvoke_body_next[dalloca]:
  ordinary_body_case ld_focus_dalloca_body_next
QED
Resume ld_focus_noninvoke_body_next[fresh]:
  drule_all (REWRITE_RULE [HD, TL, NOT_CONS_NIL]
    (Q.INST [`fs0` |-> `fs`] (BETA_RULE ld_focus_fresh_alloca_body_next))) >>
  disch_then (qx_choose_then `sz` (qx_choose_then `Ar` (qx_choose_then `ss`
    (qx_choose_then `g` (qx_choose_then `i` (qx_choose_then `Y` strip_assume_tac)))))) >>
  body_point_with `Ar`
QED
Resume ld_focus_noninvoke_body_next[cached]:
  ordinary_body_case ld_focus_cached_alloca_body_next
QED
Resume ld_focus_noninvoke_body_next[arithmetic]:
  ordinary_body_case ld_focus_arithmetic_body_next
QED
Resume ld_focus_noninvoke_body_next[classified]:
  ordinary_body_case ld_focus_classified_read_body_next
QED
Resume ld_focus_noninvoke_body_next[assign]:
  ordinary_body_case ld_focus_assignment_param_body_next
QED
Resume ld_focus_noninvoke_body_next[read]:
  ordinary_body_case ld_focus_observational_read_body_next
QED
Resume ld_focus_noninvoke_body_next[log]:
  ordinary_body_case ld_focus_log_body_next
QED
Resume ld_focus_noninvoke_body_next[storage]:
  ordinary_body_case ld_focus_storage_write_body_next
QED
Resume ld_focus_noninvoke_body_next[residual]:
  `pre_fmp_ops fn` by (drule ld_sync_head >> simp[] >> metis_tac[EVERY_MEM]) >>
  qpat_x_assum `MEM inst.inst_opcode _ \/ MEM inst.inst_opcode _`
    (let fun effect th fact = assume_tac fact >>
           drule_all (REWRITE_RULE [HD, TL, NOT_CONS_NIL]
             (Q.INST [`fs0` |-> `fs`] (BETA_RULE th)))
     in DISJ_CASES_THEN2 (effect ld_focus_residual_data_effect)
                        (effect ld_focus_external_singleton_effect)
     end) >>
  disch_then (qx_choose_then `ss` (qx_choose_then `H'` strip_assume_tac)) >>
  `step_inst fuel C inst s = OK ss` by metis_tac[step_inst_non_invoke] >>
  `step_inst 0 C inst s = OK ss` by metis_tac[step_inst_non_invoke] >>
  qabbrev_tac `q = u with vs_inst_idx := SUC t.vs_inst_idx` >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule ld_sync_control >> strip_tac >>
  `?j. get_instruction bb q.vs_inst_idx = SOME j` by
    (irule (BETA_RULE ld_successful_body_fetch) >> metis_tac[Abbr `q`]) >>
  `lookup_block q.vs_current_bb (ld_image f).fn_blocks = SOME bb` by simp[Abbr `q`] >>
  `q.vs_current_bb = s.vs_current_bb /\ q.vs_inst_idx = p + LENGTH [inst]` by
    simp[Abbr `q`, ADD1] >>
  `active_inst (ld_image f) j q` by
    (simp[active_inst_def] >> qexists `bb` >> fs[get_instruction_def] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `ld_image f = FST (lower_dload_function_supply f.lf_supply fn)` by simp[ld_image_def] >>
  `?i Y. active_inst fn i (ss with vs_inst_idx := SUC s.vs_inst_idx) /\
    ld_envelope f.lf_supply fn (ss with vs_inst_idx := SUC s.vs_inst_idx)
      (SUC s.vs_inst_idx) Y (SUC p) /\ 0 < LENGTH Y /\ j = EL 0 Y` by
    (drule_at (Pat `ld_envelope _ _ _ _ _ _`) ld_envelope_successor_head >>
     disch_then (qspecl_then [`j`,`ss`,`q`,`ld_image f`] mp_tac) >>
     simp[ADD1, Excl "EL"]) >>
  qabbrev_tac `s1 = ss with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `g = f with <|lf_src := s1; lf_tgt := q; lf_H := H';
                           lf_tv := (step_taint inst s ss tn).t_var|>` >>
  `ld_vars P A g` by
    (mp_tac (ld_vars_inst_indices |> Q.INST
       [`f` |-> `f with <|lf_src := ss; lf_tgt := u; lf_H := H';
                         lf_tv := (step_taint inst s ss tn).t_var|>`,
        `i` |-> `SUC s.vs_inst_idx`, `j` |-> `SUC t.vs_inst_idx`]) >>
     simp[Abbr `g`, Abbr `s1`, Abbr `q`]) >>
  `ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst s ss tn)
      fn i s1 q A (g::fs) N /\ ld_global lo A (g::fs)` by
    (drule ld_sync_ordinary_advance >> metis_tac[markerTheory.Abbrev_def]) >>
  `g.lf_serial = f.lf_serial /\ g.lf_fn = fn /\ g.lf_supply = f.lf_supply /\
   g.lf_Q = f.lf_Q /\ g.lf_src = s1 /\ g.lf_tgt = q /\ ld_image g = ld_image f` by
    simp[Abbr `g`, ld_image_def] >>
  `^ld_probe_stable lo P Sigma names fs f0 A0 A (g::fs)` by
    (BETA_TAC >> irule (BETA_RULE ld_stable_head_replace) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexists `f` >> gns[]) >>
  `ld_return_cont C fn cs s1` by
    (simp[Abbr `s1`] >> irule ld_return_cont_next >> goal_assum (drule_at Any) >>
     simp[] >> qexistsl_tac [`inst`,`0`] >> simp[]) >>
  `ss.vs_gas_readings = u.vs_gas_readings` by fs[ld_nonghost_def] >>
  `LENGTH ss.vs_gas_readings <= LENGTH s.vs_gas_readings` by
    (qspecl_then [`fuel`,`C'`,`inst`,`t`] mp_tac (CONJUNCT1 gasCountTheory.gas_count_suffix) >>
     simp[gasCountTheory.gas_count_suffix_def, LENGTH_DROP]) >>
  `EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
            LENGTH s1.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (g::fs)` by
    (simp[Abbr `s1`, Abbr `q`] >>
     qpat_x_assum `EVERY (\a. _ /\ LENGTH s.vs_gas_readings <= _) (f::fs)` mp_tac >>
     simp[EVERY_MEM, DISJ_IMP_THM, FORALL_AND_THM] >> metis_tac[LESS_EQ_TRANS]) >>
  qexistsl_tac [`PG`, `step_prov PG G inst ss`, `step_taint inst s ss tn`, `i`,
    `s1`, `q`, `A`, `g::fs`, `N`, `Y`, `0`] >>
  `s1.vs_inst_idx = SUC s.vs_inst_idx /\ s1.vs_gas_readings = q.vs_gas_readings` by
    simp[Abbr `s1`, Abbr `q`] >>
  `q.vs_inst_idx = SUC p` by simp[Abbr `q`] >>
  gnvs[ld_prefix_zero, Excl "EL"] >> metis_tac[]
QED
Resume ld_focus_noninvoke_body_next[complement]:
  `MEM inst (fn_insts fn)` by metis_tac[ld_active_inst_member] >>
  drule ld_sync_ptr_ok >> strip_tac >>
  drule_all ld_fn_ptr_excluded_opcodes >> strip_tac >>
  drule step_inst_ok_imp_not_phi >> strip_tac >>
  `inst_wf inst` by
    (drule_all ld_sync_fn_shape >>
     simp[o1_fn_shape_components |> cj 2, fn_inst_wf_def] >>
     metis_tac[o1_fn_shape_components, fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM]) >>
  drule_all ld_active_envelope_origin >> strip_tac >>
  `inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES` by
    (qpat_x_assum `[inst] = FST _` mp_tac >>
     qpat_x_assum `inst_wf inst` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `inst.inst_opcode = DLOAD`
     >- (simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> strip_tac >>
         simp[lower_dload_inst_supply_def] >> rpt (CASE_TAC >> simp[])) >>
     Cases_on `inst.inst_opcode = DLOADBYTES` >> simp[] >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> strip_tac >>
     simp[lower_dload_inst_supply_def] >> rpt (CASE_TAC >> simp[])) >>
  `F` suffices_by simp[] >>
  qpat_x_assum `~(MEM inst.inst_opcode _ \/ MEM inst.inst_opcode _)` mp_tac >>
  rpt (qpat_x_assum `~MEM inst.inst_opcode _` mp_tac) >>
  rpt (qpat_x_assum `inst.inst_opcode <> _` mp_tac) >>
  qpat_x_assum `~is_terminator inst.inst_opcode` mp_tac >>
  Cases_on `inst.inst_opcode` >> simp[NoAsms, is_terminator_def]
QED
Finalise ld_focus_noninvoke_body_next
