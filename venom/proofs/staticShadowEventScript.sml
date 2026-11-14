(* Successful static prefixes have non-static shadows. Nothing requires
   the shadow to terminate after the first static fault. *)
Theory staticShadowEvent
Ancestors
  dftGasOracleDefs dftGasInvFlexibleTrace
  staticShadowEntry staticShadowBase staticShadowFrame staticShadowPrim staticShadowDefs
  venomExecSemantics venomCallOracleDefs extCallOracle
  venomState venomInst list finite_map

Theorem static_shadow_ev_gas[local]:
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
  static_shadow_result_rel (ev_gas w inst s) (ev_gas w inst sh)
Proof
  strip_tac >> simp[ev_gas_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[static_shadow_result_rel_def] >>
  simp[static_shadow_rel_update_var, update_var_def]
QED

Theorem static_shadow_ev_runs:
  (!orc p d fuel C inst s sh.
    s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
    static_shadow_result_rel (ev_step orc p d fuel C inst s)
                             (ev_step orc p d fuel C inst sh)) /\
  (!orc p d fuel C bb s sh.
    s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
    static_shadow_result_rel (ev_block orc p d fuel C bb s)
                             (ev_block orc p d fuel C bb sh)) /\
  (!orc p d fuel C fn s sh.
    s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
    static_shadow_result_rel (ev_blocks orc p d fuel C fn s)
                             (ev_blocks orc p d fuel C fn sh))
Proof
  ho_match_mp_tac ev_defs_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      Cases_on `inst.inst_opcode = GAS`
      >- (simp[ev_step_def] >> irule static_shadow_ev_gas >> simp[]) >>
      Cases_on `inst.inst_opcode = INVOKE`
      >- (simp[Once ev_step_def] >>
          Cases_on `decode_invoke inst` >> simp[static_shadow_result_rel_def] >>
          PairCases_on `x` >> simp[] >>
          Cases_on `lookup_function x0 C.ctx_functions` >>
          simp[static_shadow_result_rel_def] >>
          `eval_operands x1 sh = eval_operands x1 s` by
            metis_tac[static_shadow_rel_eval_operands] >>
          simp[] >> Cases_on `eval_operands x1 s` >>
          simp[static_shadow_result_rel_def] >>
          Cases_on `setup_callee x x' s` >>
          simp[static_shadow_result_rel_def] >>
          drule_all static_shadow_setup_callee >> strip_tac >>
          first_x_assum (qspec_then `(x0,x1)` mp_tac) >>
          simp[] >> disch_then drule_all >>

          Cases_on `ev_blocks orc ((d, inst.inst_id)::p) d fuel C x x''` >>
          simp[static_shadow_result_rel_def] >> strip_tac >>
          simp[ev_step_def] >>
          Cases_on `bind_outputs inst.inst_outputs i.iret_values
            (adopt_return_fmp i (merge_callee_state s v))` >>
          simp[] >>
          `static_shadow_rel (adopt_return_fmp i (merge_callee_state s v))
            (adopt_return_fmp i (merge_callee_state sh sh'))` by
            metis_tac[static_shadow_rel_merge_callee, static_shadow_rel_adopt_return] >>
          ` (adopt_return_fmp i (merge_callee_state s v)).vs_call_ctx.cc_static` by
            (Cases_on `i.iret_adopt_fmp` >>
             simp[adopt_return_fmp_def, merge_callee_state_def]) >>
          drule_all static_shadow_bind_outputs >> strip_tac >> simp[]) >>
      simp[ev_step_def, static_shadow_base])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      `sh.vs_inst_idx = s.vs_inst_idx` by
        gvs[static_shadow_rel_def, static_shadow_def, venom_state_component_equality] >>
      once_rewrite_tac[ev_block_def] >> simp[] >>
      Cases_on `get_instruction bb s.vs_inst_idx` >>
      simp[static_shadow_result_rel_def] >>
      qpat_x_assum `!inst. _` (qspec_then `x` mp_tac) >> simp[] >>
      disch_then drule_all >>
      Cases_on `ev_step orc p d fuel C x s` >>
      simp[static_shadow_result_rel_def] >> strip_tac >>
      simp[] >>
      `sh'.vs_halted = v.vs_halted` by
        gvs[static_shadow_rel_def, static_shadow_def, venom_state_component_equality] >>
      Cases_on `is_terminator x.inst_opcode` >> simp[]
      >- (Cases_on `v.vs_halted` >> simp[static_shadow_result_rel_def]) >>
      qpat_x_assum `!inst s''. _` (qspecl_then [`x`, `v`] mp_tac) >>
      simp[] >> disch_then (qspec_then `sh' with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
      simp[static_shadow_rel_updates, static_shadow_result_rel_def]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `sh.vs_current_bb = s.vs_current_bb` by
    gvs[static_shadow_rel_def, static_shadow_def, venom_state_component_equality] >>
  once_rewrite_tac[ev_blocks_def] >> simp[] >>
  Cases_on `fuel` >> simp[static_shadow_result_rel_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  simp[static_shadow_result_rel_def] >>
  mp_tac (Q.SPECL [`s`, `x.bb_instructions`] eval_phis_ok_or_error_defs) >>
  strip_tac >> simp[]
  >- (drule_all static_shadow_phis >>
      disch_then (qspec_then `x.bb_instructions` mp_tac) >>
      simp[static_shadow_result_rel_def] >> strip_tac >> simp[] >>
      qpat_x_assum `!fuel' bb s_phi. _`
        (qspecl_then [`n`, `x`, `s'`] mp_tac) >> simp[] >>
      disch_then (qspec_then `sh' with vs_inst_idx := phi_prefix_length x.bb_instructions` mp_tac) >>
      simp[static_shadow_rel_updates] >>
      Cases_on `ev_block orc p (SUC d) n C x (s' with vs_inst_idx := phi_prefix_length x.bb_instructions)` >>
      simp[static_shadow_result_rel_def] >> strip_tac >> simp[] >>
      `sh''.vs_halted = v.vs_halted` by
        gvs[static_shadow_rel_def, static_shadow_def, venom_state_component_equality] >>
      Cases_on `v.vs_halted` >> simp[static_shadow_result_rel_def] >>
      qpat_x_assum `!fuel' bb s_phi s''. _`
        (qspecl_then [`n`, `x`, `s'`, `v`] mp_tac) >> simp[] >>
      disch_then (qspec_then `sh''` mp_tac) >>
      simp[static_shadow_result_rel_def]) >>
  simp[static_shadow_result_rel_def]
QED

Theorem static_shadow_ev_ftrace:
  !is s t sh.
    inv_ev_ftrace orc p d C is s t /\
    s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
    ?th. inv_ev_ftrace orc p d C is sh th /\
         static_shadow_rel t th /\ t.vs_call_ctx.cc_static
Proof
  Induct >- simp[inv_ev_ftrace_def] >>
  simp[inv_ev_ftrace_def] >> rpt strip_tac >>
  `static_shadow_result_rel (ev_step orc p d fuel C h s)
                           (ev_step orc p d fuel C h sh)` by
    metis_tac[static_shadow_ev_runs] >>
  gvs[static_shadow_result_rel_def] >>
  `sh.vs_inst_idx = s.vs_inst_idx` by
    gvs[static_shadow_rel_def, static_shadow_def, venom_state_component_equality] >>
  first_x_assum (qspecl_then
    [`u with vs_inst_idx := SUC s.vs_inst_idx`, `t`,
     `sh' with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
  simp[static_shadow_rel_updates] >> metis_tac[]
QED
