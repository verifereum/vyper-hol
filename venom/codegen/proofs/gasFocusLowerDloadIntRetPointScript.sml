(* Reconstruct an actual successful IntRet at a bounded LowerDload point. *)
Theory gasFocusLowerDloadIntRetPoint
Ancestors
  gasFocusLowerDloadReturn o1SafeUpto lowerDloadEnvelopeControl
  lowerDloadSafetyLocations lowerDloadSafetyAmbient lowerDloadSafetyRelation
  lowerDloadSafetyKernel lowerDloadOracleCallAssembly
  o1ContractLowerDload o1PassContract opcodeClass
  venomExecSemantics venomInst finite_map list
Libs
  lowerDloadReturnPackageLib

Theorem ld_focus_point_intret_terminal:
  o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\
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
  step_inst_base ti t = IntRet rt u /\ gas_cut n vs u ==>
  inst.inst_opcode = RET /\ ti = inst /\ t0 = t /\
  ?sf rs e.
    run_blocks sf C fn cs = IntRet rs e /\
    step_inst 0 C inst s = IntRet rs e /\
    step_inst 0 C' inst t0 = IntRet rt u /\
    rs.iret_values = rt.iret_values /\
    rs.iret_adopt_fmp = NONE /\ rt.iret_adopt_fmp = NONE /\
    ld_memory lo A tn e u /\ ld_nonghost tn e u /\ e = s /\ u = t0 /\
    (!a. a IN ld_slots A fs ==>
         FLOOKUP (DRESTRICT A (ld_slots A fs)) a = FLOOKUP A a) /\
    e.vs_gas_readings = u.vs_gas_readings /\
    EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
               LENGTH e.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) frames
Proof
  BETA_TAC >> strip_tac >>
  drule ld_sync_source >> strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) gn.fn_blocks)` by
    (`(HD frames).lf_fn = fn` by metis_tac[ld_sync_active] >>
     qpat_assum `gn = ld_image _` SUBST1_TAC >>
     pure_rewrite_tac[ld_image_def] >>
     qpat_assum `(HD frames).lf_fn = fn` SUBST1_TAC >>
     Cases_on `lower_dload_function_supply (HD frames).lf_supply fn` >>
     drule lower_dload_function_supply_labels >> simp[fn_labels_def]) >>
  `active_inst gn (EL h X) t` by metis_tac[ld_prefix_active] >>
  `ti = EL h X` by
    (drule_all ld_active_lookup >> simp[] >> strip_tac >> gvs[get_instruction_def]) >>
  `h < LENGTH X` by metis_tac[ld_prefix_bound] >>
  `is_terminator ti.inst_opcode` by metis_tac[step_inst_base_no_intret] >>
  `inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES` by
    (Cases_on `inst.inst_opcode = DLOAD \/ inst.inst_opcode = DLOADBYTES`
     >- (`~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
           fs[is_terminator_def] >>
         drule_all ld_envelope_nonterminal >>
         simp[EVERY_EL] >> disch_then (qspec_then `h` mp_tac) >> gvs[]) >> fs[]) >>
  `X = [inst]` by (drule_all ld_envelope_ordinary >> simp[]) >>
  `h = 0` by fs[] >>
  `ti = inst /\ t0 = t` by fs[ld_prefix_zero] >>
  qpat_x_assum `ti = inst` SUBST_ALL_TAC >>
  qpat_x_assum `t0 = t` SUBST_ALL_TAC >>
  qpat_x_assum `inst = EL h X` kall_tac >>
  `MEM fn C.ctx_functions` by
    (drule_all ld_frame_reachable_certificate >> disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  `MEM inst (fn_insts fn)` by metis_tac[ld_active_inst_member] >>
  `pre_fmp_opcode inst.inst_opcode` by
    (fs[o1_safe_upto_def, o1_ptr_safe_upto_def, fmp_free_ctx_def,
        pre_fmp_ops_def, EVERY_MEM] >> metis_tac[]) >>
  `inst.inst_opcode = RET` by
    (drule step_inst_base_intret_opcodes >> strip_tac >> gvs[pre_fmp_opcode_def]) >>
  `u = t` by
    (qpat_assum `step_inst_base inst t = _` mp_tac >>
     once_rewrite_tac[step_inst_base_def] >> simp[AllCaseEqs()] >>
     rpt strip_tac >> gvs[]) >>
  `gas_cut n vs s` by fs[gas_cut_def] >>
  `taint_ok fn tn inst s` by
    (fs[o1_safe_upto_def, o1_ptr_safe_upto_def, ptr_discipline_upto_def] >>
     metis_tac[]) >>
  ntac 3 (conj_tac >- asm_rewrite_tac[]) >>
  drule_all ld_focus_ret_correlated_terminal >>
  disch_then (qspec_then `C'` strip_assume_tac) >>
  qexistsl_tac [`sf`, `rs`, `e`] >> simp[FLOOKUP_DRESTRICT]
QED
