Theory concretizePtrForwardingTaint
Ancestors
  concretizePtrChronologicalHistory frameHistoryInstructions frameHistoryCfg
  simplifyCfgFrameRf analysisSimProofsBase contextCodegenRel ptrDiscipline
  venomInstProofs venomExecProofs venomWf venomExecSemantics venomState venomInst
  finite_map list rich_list pred_set

Theorem ptr_step_back_assign_taint:
  step_inst fuel C inst s = OK t /\ inst.inst_opcode <> INVOKE /\
  step_back_assign inst op = SOME old ==>
  op_taint (step_taint inst s t tn) op = op_taint tn old
Proof
  rpt strip_tac >> Cases_on `op` >>
  gvs[step_back_assign_def] >> simp[op_taint_def] >>
  rename1 `MEM v inst.inst_outputs` >>
  Cases_on `MEM v inst.inst_outputs` >> gvs[AllCaseEqs()]
  >- (namedCases_on `inst.inst_operands` ["", "input inputs"] >> gvs[] >>
      `?value. eval_operand input s = SOME value` by
        (gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >> metis_tac[]) >>
      simp[step_taint_def, out_taint_def, set_var_taint_def,
           op_taint_def, FLOOKUP_UPDATE]) >>
  Cases_on `FLOOKUP tn.t_var v` >>
  namedCases_on `inst.inst_outputs` ["", "out rest"] >>
  simp[step_taint_def, set_var_taint_def, FLOOKUP_DRESTRICT,
       FLOOKUP_UPDATE, op_taint_def] >>
  Cases_on `rest` >> fs[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem ptr_step_back_restrict_taint[local]:
  inst.inst_opcode <> ASSIGN /\ step_back_assign inst op = SOME old ==>
  op_taint (entry_taint with t_var := DRESTRICT tv (COMPL (set inst.inst_outputs))) op =
  op_taint (entry_taint with t_var := tv) old
Proof
  rpt strip_tac >> Cases_on `op` >>
  gvs[step_back_assign_def, AllCaseEqs()] >>
  simp[op_taint_def, FLOOKUP_DRESTRICT]
QED

Theorem ptr_same_after_assigns_taint_next[local]:
  wf_function fn /\ active_inst fn inst s /\
  step_inst fuel C inst s = OK t /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\
  (!bb p q. MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
    same_after_assigns (REVERSE (TAKE s.vs_inst_idx bb.bb_instructions)) p q ==>
    op_taint tn p = op_taint tn q) ==>
  !bb p q. MEM bb fn.fn_blocks /\ bb.bb_label = t.vs_current_bb /\
    same_after_assigns (REVERSE (TAKE (SUC s.vs_inst_idx) bb.bb_instructions)) p q ==>
    op_taint (step_taint inst s t tn) p = op_taint (step_taint inst s t tn) q
Proof
  rpt strip_tac >> drule_all step_preserves_control_flow >> strip_tac >>
  qpat_x_assum `active_inst fn inst s` mp_tac >>
  PURE_REWRITE_TAC [active_inst_def] >>
  disch_then (qx_choose_then `active_bb` strip_assume_tac) >>
  `active_bb = bb` by metis_tac[same_label_same_block] >>
  qpat_x_assum `active_bb = bb` SUBST_ALL_TAC >> gvs[] >>
  gvs[TAKE_SUC_BY_TAKE, REVERSE_SNOC, same_after_assigns_def, AllCaseEqs()] >>
  Cases_on `step_back_assign (EL s.vs_inst_idx bb.bb_instructions) p` >> gvs[] >>
  Cases_on `step_back_assign (EL s.vs_inst_idx bb.bb_instructions) q` >> gvs[] >>
  metis_tac[ptr_step_back_assign_taint]
QED

Theorem ptr_same_after_assigns_taint_resume[local]:
  wf_function fn /\ active_inst fn inst s /\ inst.inst_opcode = INVOKE /\
  (!bb p q. MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
    same_after_assigns (REVERSE (TAKE s.vs_inst_idx bb.bb_instructions)) p q ==>
    op_taint (entry_taint with t_var := tv) p =
      op_taint (entry_taint with t_var := tv) q) ==>
  !bb p q. MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
    same_after_assigns (REVERSE (TAKE (SUC s.vs_inst_idx) bb.bb_instructions)) p q ==>
    op_taint (entry_taint with t_var := DRESTRICT tv (COMPL (set inst.inst_outputs))) p =
      op_taint (entry_taint with t_var := DRESTRICT tv (COMPL (set inst.inst_outputs))) q
Proof
  rpt strip_tac >>
  qpat_x_assum `active_inst fn inst s` mp_tac >>
  PURE_REWRITE_TAC [active_inst_def] >>
  disch_then (qx_choose_then `active_bb` strip_assume_tac) >>
  `active_bb = bb` by metis_tac[same_label_same_block] >>
  qpat_x_assum `active_bb = bb` SUBST_ALL_TAC >> gvs[] >>
  gvs[TAKE_SUC_BY_TAKE, REVERSE_SNOC, same_after_assigns_def, AllCaseEqs()] >>
  namedCases_on `step_back_assign (EL s.vs_inst_idx bb.bb_instructions) p`
    ["", "old_p"] >> gvs[] >>
  namedCases_on `step_back_assign (EL s.vs_inst_idx bb.bb_instructions) q`
    ["", "old_q"] >> gvs[] >>
  `op_taint (entry_taint with t_var := tv) old_p =
    op_taint (entry_taint with t_var := tv) old_q` by
    (first_x_assum irule >> qexists_tac `bb` >> simp[]) >>
  `op_taint (entry_taint with t_var := DRESTRICT tv
      (COMPL (set (EL s.vs_inst_idx bb.bb_instructions).inst_outputs))) p =
    op_taint (entry_taint with t_var := tv) old_p` by
    (irule ptr_step_back_restrict_taint >> simp[]) >>
  `op_taint (entry_taint with t_var := DRESTRICT tv
      (COMPL (set (EL s.vs_inst_idx bb.bb_instructions).inst_outputs))) q =
    op_taint (entry_taint with t_var := tv) old_q` by
    (irule ptr_step_back_restrict_taint >> simp[]) >> simp[]
QED

Theorem ptr_same_after_assigns_taint_entry[local]:
  wf_function fn /\ enters_block fn s t ==>
  !bb p q. MEM bb fn.fn_blocks /\ bb.bb_label = t.vs_current_bb /\
    same_after_assigns (REVERSE (TAKE t.vs_inst_idx bb.bb_instructions)) p q ==>
    op_taint tn p = op_taint tn q
Proof
  rpt strip_tac >> drule enters_block_entry_index >>
  disch_then (qx_choose_then `entry_bb` strip_assume_tac) >>
  `entry_bb = bb` by metis_tac[same_label_same_block] >>
  qpat_x_assum `entry_bb = bb` SUBST_ALL_TAC >> gvs[] >>
  `EVERY (\inst. inst.inst_opcode <> ASSIGN)
    (REVERSE (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions))` by
    (simp[EVERY_REVERSE] >>
     mp_tac (Q.SPEC `bb.bb_instructions` phi_prefix_all_phi) >>
     simp[EVERY_MEM] >> metis_tac[]) >>
  `p = q` by metis_tac[scfg_same_after_nonassigns] >> simp[]
QED

Theorem ptr_reachable_same_after_assigns_taint_invariant[local]:
  !vs C stk PG G tn fn inst s.
  frame_reachable vs C stk PG G tn fn inst s ==>
  EVERY wf_function C.ctx_functions ==>
  MEM fn C.ctx_functions /\
  (!bb p q. MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
    same_after_assigns (REVERSE (TAKE s.vs_inst_idx bb.bb_instructions)) p q ==>
    op_taint tn p = op_taint tn q) /\
  EVERY (\f. MEM f.cf_fn C.ctx_functions /\
    active_inst f.cf_fn f.cf_inst f.cf_state /\ f.cf_inst.inst_opcode = INVOKE /\
    (!bb p q. MEM bb f.cf_fn.fn_blocks /\ bb.bb_label = f.cf_state.vs_current_bb /\
      same_after_assigns (REVERSE (TAKE f.cf_state.vs_inst_idx bb.bb_instructions)) p q ==>
      op_taint (entry_taint with t_var := f.cf_tvar) p =
        op_taint (entry_taint with t_var := f.cf_tvar) q)) stk
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- (rpt strip_tac >> drule lookup_function_MEM >> strip_tac >> simp[] >>
      irule ptr_same_after_assigns_taint_entry >>
      goal_assum (drule_at Any) >> metis_tac[EVERY_MEM])
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume ptr_reachable_same_after_assigns_taint_invariant[next]:
  rpt gen_tac >> strip_tac >> disch_tac >>
  first_x_assum (drule_then strip_assume_tac) >> simp[] >>
  `wf_function fn` by metis_tac[EVERY_MEM] >>
  mp_tac (Q.INST [`fn` |-> `fn`, `inst` |-> `inst`,
    `s` |-> `s`, `t` |-> `s'`, `tn` |-> `tn`,
    `fuel` |-> `fuel`, `C` |-> `C`] ptr_same_after_assigns_taint_next) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]
QED

Resume ptr_reachable_same_after_assigns_taint_invariant[block]:
  rpt gen_tac >> strip_tac >> disch_tac >>
  first_x_assum (drule_then strip_assume_tac) >> simp[] >>
  `wf_function fn` by metis_tac[EVERY_MEM] >>
  mp_tac (Q.INST [`fn` |-> `fn`, `s` |-> `s'`, `t` |-> `s''`,
    `tn` |-> `entry_taint_vars fn s' tn`] ptr_same_after_assigns_taint_entry) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]
QED

Resume ptr_reachable_same_after_assigns_taint_invariant[call]:
  rpt gen_tac >> strip_tac >> disch_tac >>
  first_x_assum (drule_then strip_assume_tac) >>
  drule lookup_function_MEM >> strip_tac >> simp[] >> conj_tac
  >- (mp_tac (Q.INST [`fn` |-> `fn'`, `s` |-> `cs`, `t` |-> `s''`,
        `tn` |-> `tn with t_var := FEMPTY`] ptr_same_after_assigns_taint_entry) >>
      (impl_tac >- (simp[] >> metis_tac[EVERY_MEM])) >> simp[]) >>
  qpat_assum `!bb p q. MEM bb fn.fn_blocks /\ _ ==> op_taint tn p = _` mp_tac >>
  simp[op_taint_def]
QED

Resume ptr_reachable_same_after_assigns_taint_invariant[ret]:
  rpt gen_tac >> strip_tac >> disch_tac >>
  first_x_assum (drule_then strip_assume_tac) >> gvs[] >>
  drule return_binding_current_bb >> strip_tac >> simp[] >>
  `wf_function f.cf_fn` by metis_tac[EVERY_MEM] >>
  mp_tac (Q.INST [`fn` |-> `f.cf_fn`, `inst` |-> `f.cf_inst`,
    `s` |-> `f.cf_state`, `tv` |-> `f.cf_tvar`]
    ptr_same_after_assigns_taint_resume) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp[op_taint_def]
QED

Finalise ptr_reachable_same_after_assigns_taint_invariant

Theorem ptr_reachable_same_after_assigns_taint:
  frame_reachable vs C stk PG G tn fn inst s /\ EVERY wf_function C.ctx_functions /\
  MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
  same_after_assigns (REVERSE (TAKE s.vs_inst_idx bb.bb_instructions)) p q ==>
  op_taint tn p = op_taint tn q
Proof
  metis_tac[ptr_reachable_same_after_assigns_taint_invariant]
QED
