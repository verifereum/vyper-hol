(* Reachability records only successful static prefixes. *)
Theory staticShadowReachable
Ancestors
  contextRawReachable contextCodegenRel staticShadowRun staticShadowEntry staticShadowFrame
  staticShadowDefs venomExecSemantics venomState

Theorem static_shadow_active_inst:
  static_shadow_rel s sh ==> (active_inst fn inst sh <=> active_inst fn inst s)
Proof
  simp[static_shadow_rel_def, static_shadow_def,
       venom_state_component_equality, active_inst_def]
QED

Theorem static_shadow_enters_block:
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh /\
  enters_block fn s t ==>
  ?th. enters_block fn sh th /\ static_shadow_rel t th /\
       t.vs_call_ctx.cc_static
Proof
  simp[enters_block_def] >> rpt strip_tac >>
  `sh.vs_current_bb = s.vs_current_bb` by
    gvs[static_shadow_rel_def, static_shadow_def, venom_state_component_equality] >>
  drule_all static_shadow_phis >>
  disch_then (qspec_then `bb.bb_instructions` mp_tac) >>
  simp[static_shadow_result_rel_def] >> strip_tac >>
  qexists_tac `sh' with vs_inst_idx := phi_prefix_length bb.bb_instructions` >>
  simp[static_shadow_rel_updates] >> metis_tac[]
QED

Theorem static_shadow_raw_reachable:
  !vs C fn inst s.
    raw_reachable vs C fn inst s ==>
    vs.vs_call_ctx.cc_static ==>
    s.vs_call_ctx.cc_static /\
    ?sh. static_shadow_rel s sh /\
         raw_reachable (static_shadow vs) C fn inst sh
Proof
  ho_match_mp_tac raw_reachable_ind >> rpt conj_tac >> rpt gen_tac
  >- (strip_tac >> strip_tac >>
      `static_shadow_rel
        (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
        ((static_shadow vs) with
          <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)` by
        simp[static_shadow_rel_updates, static_shadow_rel_initial] >>
      `(vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>).vs_call_ctx.cc_static` by simp[] >>
      drule_all static_shadow_enters_block >> strip_tac >> simp[] >>
      qexists_tac `th` >> simp[] >>
      irule raw_reachable_entry >>
      metis_tac[static_shadow_active_inst])
  >- (strip_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
      `static_shadow_result_rel (step_inst fuel C inst s)
                               (step_inst fuel C inst sh)` by
        metis_tac[static_shadow_runs] >>
      gvs[static_shadow_result_rel_def] >>
      `sh.vs_inst_idx = s.vs_inst_idx` by
        gvs[static_shadow_rel_def, static_shadow_def, venom_state_component_equality] >>
      `active_inst fn inst sh` by metis_tac[static_shadow_active_inst] >>
      `static_shadow_rel (s' with vs_inst_idx := SUC s.vs_inst_idx)
                         (sh' with vs_inst_idx := SUC s.vs_inst_idx)` by
        simp[static_shadow_rel_updates] >>
      `active_inst fn inst' (sh' with vs_inst_idx := SUC s.vs_inst_idx)` by
        metis_tac[static_shadow_active_inst] >>
      qexists_tac `sh' with vs_inst_idx := SUC s.vs_inst_idx` >>
      simp[static_shadow_rel_updates] >>
      qpat_assum `sh.vs_inst_idx = s.vs_inst_idx`
        (fn th => rewrite_tac[GSYM th]) >>
      irule raw_reachable_next >> metis_tac[])
  >- (strip_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
      `static_shadow_result_rel (step_inst fuel C inst s)
                               (step_inst fuel C inst sh)` by
        metis_tac[static_shadow_runs] >>
      gvs[static_shadow_result_rel_def] >>
      drule_all static_shadow_enters_block >> strip_tac >> simp[] >>
      qexists_tac `th` >> simp[] >>
      irule raw_reachable_block >>
      `sh'.vs_halted = s'.vs_halted` by
        gvs[static_shadow_rel_def, static_shadow_def, venom_state_component_equality] >>
      metis_tac[static_shadow_active_inst]) >>
  strip_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
  `eval_operands ops sh = eval_operands ops s` by
    metis_tac[static_shadow_rel_eval_operands] >>
  drule_all static_shadow_setup_callee >> strip_tac >>
  drule_all static_shadow_enters_block >> strip_tac >> simp[] >>
  qexists_tac `th'` >> simp[] >>
  irule raw_reachable_callee >>
  metis_tac[static_shadow_active_inst]
QED
