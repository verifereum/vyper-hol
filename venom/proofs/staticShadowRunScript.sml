(* Successful static prefixes have non-static shadows. Nothing requires
   the shadow to terminate after the first static fault. *)
Theory staticShadowRun
Ancestors
  staticShadowEntry staticShadowBase staticShadowFrame staticShadowPrim staticShadowDefs
  venomExecSemantics venomCallOracleDefs extCallOracle
  venomState venomInst opcodeClass list finite_map
Libs
  stepInstBaseLib

Theorem static_shadow_runs:
  (!fuel C inst s sh.
    s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
    static_shadow_result_rel (step_inst fuel C inst s)
                             (step_inst fuel C inst sh)) /\
  (!fuel C bb s sh.
    s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
    static_shadow_result_rel (exec_block fuel C bb s)
                             (exec_block fuel C bb sh)) /\
  (!fuel C fn s sh.
    s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
    static_shadow_result_rel (run_blocks fuel C fn s)
                             (run_blocks fuel C fn sh))
Proof
  ho_match_mp_tac run_defs_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      Cases_on `inst.inst_opcode = INVOKE`
      >- (simp[Once step_inst_def] >>
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

          Cases_on `run_blocks fuel C x x''` >>
          simp[static_shadow_result_rel_def] >> strip_tac >>
          simp[step_inst_def] >>
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
      simp[step_inst_non_invoke, static_shadow_base])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      `sh.vs_inst_idx = s.vs_inst_idx` by
        gvs[static_shadow_rel_def, static_shadow_def, venom_state_component_equality] >>
      once_rewrite_tac[exec_block_def] >> simp[] >>
      Cases_on `get_instruction bb s.vs_inst_idx` >>
      simp[static_shadow_result_rel_def] >>
      qpat_x_assum `!inst. _` (qspec_then `x` mp_tac) >> simp[] >>
      disch_then drule_all >>
      Cases_on `step_inst fuel C x s` >>
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
  once_rewrite_tac[run_blocks_def] >> simp[] >>
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
      Cases_on `exec_block n C x (s' with vs_inst_idx := phi_prefix_length x.bb_instructions)` >>
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

Theorem static_shadow_base_revert[local]:
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh /\
  step_inst_base inst s = Abort Revert_abort v ==>
  ?vh. step_inst_base inst sh = Abort Revert_abort vh /\
       static_shadow_rel v vh
Proof
  strip_tac >>
  `!op. eval_operand op sh = eval_operand op s` by
    metis_tac[static_shadow_rel_eval_operand] >>
  `sh.vs_memory = s.vs_memory` by
    gvs[static_shadow_rel_def, static_shadow_def, venom_state_component_equality] >>
  drule step_inst_base_abort_opcodes >> strip_tac >>
  with_opcode_clause (fn ths =>
    fs (ths @ [AllCaseEqs(), exec_call_helpers_no_halt_abort,
               exec_create_abort_iff, exec_write2_def, eval_operands_def])) >>
  gvs[revert_state_def, GSYM halt_state_def] >>
  metis_tac[static_shadow_rel_controls]
QED

Theorem static_shadow_revert_runs[local]:
  (!fuel C inst s sh v.
    s.vs_call_ctx.cc_static /\ static_shadow_rel s sh /\
    step_inst fuel C inst s = Abort Revert_abort v ==>
    ?vh. step_inst fuel C inst sh = Abort Revert_abort vh /\
         static_shadow_rel v vh) /\
  (!fuel C bb s sh v.
    s.vs_call_ctx.cc_static /\ static_shadow_rel s sh /\
    exec_block fuel C bb s = Abort Revert_abort v ==>
    ?vh. exec_block fuel C bb sh = Abort Revert_abort vh /\
         static_shadow_rel v vh) /\
  (!fuel C fn s sh v.
    s.vs_call_ctx.cc_static /\ static_shadow_rel s sh /\
    run_blocks fuel C fn s = Abort Revert_abort v ==>
    ?vh. run_blocks fuel C fn sh = Abort Revert_abort vh /\
         static_shadow_rel v vh)
Proof
  ho_match_mp_tac run_defs_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      Cases_on `inst.inst_opcode = INVOKE`
      >- (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
          simp[Once step_inst_def, AllCaseEqs()] >> strip_tac >>
          `eval_operands arg_ops sh = eval_operands arg_ops s` by
            metis_tac[static_shadow_rel_eval_operands] >>
          drule_all static_shadow_setup_callee >> strip_tac >>
          first_x_assum (qspec_then `(callee_name,arg_ops)` mp_tac) >>
          simp[] >> disch_then drule_all >> strip_tac >>
          simp[Once step_inst_def] >> metis_tac[]) >>
      fs[step_inst_non_invoke] >> metis_tac[static_shadow_base_revert])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      `sh.vs_inst_idx = s.vs_inst_idx` by
        gvs[static_shadow_rel_def, static_shadow_def, venom_state_component_equality] >>
      qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
      once_rewrite_tac[exec_block_def] >>
      Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
      rename1 `get_instruction bb s.vs_inst_idx = SOME x` >>
      Cases_on `step_inst fuel C x s` >> simp[] >> strip_tac
      >- (rename1 `step_inst fuel C x s = OK v'` >>
          mp_tac (cj 1 static_shadow_runs) >>
          disch_then (qspecl_then [`fuel`, `C`, `x`, `s`, `sh`] mp_tac) >>
          simp[static_shadow_result_rel_def] >> strip_tac >>
          rename1 `step_inst fuel C x sh = OK sh'` >>
          `~is_terminator x.inst_opcode` by
            (Cases_on `is_terminator x.inst_opcode` >> fs[] >>
             Cases_on `v'.vs_halted` >> fs[]) >>
          first_x_assum (qspecl_then [`x`, `v'`] mp_tac) >> simp[] >>
          disch_then (qspecl_then
            [`sh' with vs_inst_idx := SUC s.vs_inst_idx`, `v`] mp_tac) >>
          simp[static_shadow_rel_updates] >> strip_tac >> simp[] >> metis_tac[]) >>
      first_x_assum (qspec_then `x` mp_tac) >> simp[] >>
      disch_then drule_all >> strip_tac >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `sh.vs_current_bb = s.vs_current_bb` by
    gvs[static_shadow_rel_def, static_shadow_def, venom_state_component_equality] >>
  qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[run_blocks_def] >>
  Cases_on `fuel` >> simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME x` >>
  mp_tac (Q.SPECL [`s`, `x.bb_instructions`] eval_phis_ok_or_error_defs) >>
  strip_tac >> simp[] >>
  drule_all static_shadow_phis >>
  disch_then (qspec_then `x.bb_instructions` mp_tac) >>
  simp[static_shadow_result_rel_def] >> strip_tac >> simp[] >>
  Cases_on `exec_block n C x
    (s' with vs_inst_idx := phi_prefix_length x.bb_instructions)` >>
  simp[] >> strip_tac
  >- (rename1 `exec_block n C x
        (s' with vs_inst_idx := phi_prefix_length x.bb_instructions) = OK v'` >>
      mp_tac (cj 2 static_shadow_runs) >>
      disch_then (qspecl_then [`n`, `C`, `x`,
        `s' with vs_inst_idx := phi_prefix_length x.bb_instructions`,
        `sh' with vs_inst_idx := phi_prefix_length x.bb_instructions`] mp_tac) >>
      simp[static_shadow_rel_updates, static_shadow_result_rel_def] >>
      strip_tac >>
      rename1 `exec_block n C x
        (sh' with vs_inst_idx := phi_prefix_length x.bb_instructions) = OK sh''` >>
      `sh''.vs_halted = v'.vs_halted` by
        gvs[static_shadow_rel_def, static_shadow_def,
            venom_state_component_equality] >>
      Cases_on `v'.vs_halted` >> fs[] >>
      first_x_assum (qspecl_then [`n`, `x`, `s'`, `v'`] mp_tac) >> simp[] >>
      disch_then drule_all >> strip_tac >> simp[] >> metis_tac[]) >>
  first_x_assum (qspecl_then [`n`, `x`, `s'`] mp_tac) >> simp[] >>
  disch_then (qspec_then
    `sh' with vs_inst_idx := phi_prefix_length x.bb_instructions` mp_tac) >>
  simp[static_shadow_rel_updates] >> strip_tac >> simp[] >> metis_tac[]
QED

Theorem static_shadow_run_context_revert:
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh /\
  run_context fuel C s = Abort Revert_abort v ==>
  ?vh. run_context fuel C sh = Abort Revert_abort vh /\
       static_shadow_rel v vh
Proof
  simp[run_context_def, run_function_def, AllCaseEqs()] >>
  strip_tac >> simp[] >> irule (cj 3 static_shadow_revert_runs) >>
  qexists_tac `s with <|vs_prev_bb := NONE; vs_current_bb := lbl;
                       vs_inst_idx := 0|>` >>
  simp[static_shadow_rel_updates]
QED
