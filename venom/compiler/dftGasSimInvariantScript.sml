Theory dftGasSimInvariant
Ancestors
  dftGasSimBoundary dftGasOracleDefs dftRunRel
  venomExecSemantics venomExecProofs venomState venomInst venomInstProps
  list dftScheduleOrder
  venomWfProps

Theorem ev_setup_callee_dominators:
  setup_callee fn args s = SOME t ==> strict_dom_vars_defined fn t
Proof
  strip_tac >> irule strict_dom_vars_defined_entry >>
  gvs[setup_callee_def, AllCaseEqs(), fn_entry_label_def, entry_block_def]
QED

Theorem ev_step_labels:
  ev_step orc p d fuel C inst s = OK t ==> t.vs_labels = s.vs_labels
Proof
  Cases_on `inst.inst_opcode = GAS`
  >- (simp[ev_step_gas, ev_gas_def] >>
      Cases_on `inst.inst_outputs` >> simp[] >>
      rename1 `inst.inst_outputs = out::outs` >> Cases_on `outs` >>
      simp[update_var_def] >> strip_tac >> gvs[]) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (simp[Once ev_step_def] >>
      simp[AllCaseEqs()] >> rpt strip_tac >>
      `!pairs st. (FOLDL (\st' (out,value). update_var out value st') st pairs).vs_labels = st.vs_labels` by
        (Induct >> simp[] >> Cases >> simp[update_var_def]) >>
      gvs[bind_outputs_def, AllCaseEqs()] >>
      simp[adopt_return_fmp_def, merge_callee_state_def] >>
      Cases_on `ret.iret_adopt_fmp` >> simp[]) >>
  simp[Once ev_step_def] >> strip_tac >>
  `step_inst fuel C inst s = OK t` by simp[step_inst_non_invoke] >>
  metis_tac[step_inst_preserves_labels_always]
QED

Theorem ev_suffix_labels:
  !xs s t. ev_suffix orc p d fuel C xs s = OK t ==>
    t.vs_labels = s.vs_labels
Proof
  Induct >> simp[ev_suffix_def] >> rpt gen_tac >>
  Cases_on `ev_step orc p d fuel C h s` >> simp[] >>
  drule ev_step_labels >> strip_tac >>
  IF_CASES_TAC
  >- (IF_CASES_TAC >> simp[] >> strip_tac >> gvs[]) >>
  simp[] >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem ev_block_labels:
  ev_block orc p d fuel C bb s = OK t ==> t.vs_labels = s.vs_labels
Proof
  mp_tac (ev_suffix_block |> Q.INST [`ctx` |-> `C`]) >>
  disch_then (qspecl_then [`DROP s.vs_inst_idx bb.bb_instructions`, `s`, `bb`] mp_tac) >>
  simp[] >> metis_tac[ev_suffix_labels]
QED

Theorem ctx_labels_bound_ev_step:
  ctx_labels_bound C s.vs_labels /\ ev_step orc p d fuel D inst s = OK t ==>
    ctx_labels_bound C t.vs_labels
Proof
  metis_tac[ev_step_labels]
QED

Theorem ev_step_call_ctx:
  ev_step orc p d fuel C inst s = OK t ==> t.vs_call_ctx = s.vs_call_ctx
Proof
  Cases_on `inst.inst_opcode = GAS`
  >- (simp[ev_step_gas, ev_gas_def] >>
      Cases_on `inst.inst_outputs` >> simp[] >>
      rename1 `inst.inst_outputs = out::outs` >> Cases_on `outs` >>
      simp[update_var_def] >> strip_tac >> gvs[]) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (simp[Once ev_step_def] >>
      simp[AllCaseEqs()] >> rpt strip_tac >>
      `!pairs st. (FOLDL (\st' (out,value). update_var out value st') st pairs).vs_call_ctx = st.vs_call_ctx` by
        (Induct >> simp[] >> Cases >> simp[update_var_def]) >>
      gvs[bind_outputs_def, AllCaseEqs()] >>
      simp[adopt_return_fmp_def, merge_callee_state_def] >>
      Cases_on `ret.iret_adopt_fmp` >> simp[]) >>
  simp[Once ev_step_def] >> strip_tac >>
  `step_inst fuel C inst s = OK t` by simp[step_inst_non_invoke] >>
  reverse (Cases_on `is_terminator inst.inst_opcode`)
  >- metis_tac[step_preserves_call_ctx] >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
  qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  pure_asm_rewrite_tac[opcode_case_def] >> simp[AllCaseEqs(), jump_to_def] >>
  rpt strip_tac >> gvs[] >> pairarg_tac >> gvs[]
QED

Theorem ev_suffix_call_ctx:
  !xs s t. ev_suffix orc p d fuel C xs s = OK t ==>
    t.vs_call_ctx = s.vs_call_ctx
Proof
  Induct >> simp[ev_suffix_def] >> rpt gen_tac >>
  Cases_on `ev_step orc p d fuel C h s` >> simp[] >>
  drule ev_step_call_ctx >> strip_tac >>
  IF_CASES_TAC
  >- (IF_CASES_TAC >> simp[] >> strip_tac >> gvs[]) >>
  simp[] >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem ev_block_call_ctx:
  ev_block orc p d fuel C bb s = OK t ==> t.vs_call_ctx = s.vs_call_ctx
Proof
  mp_tac (ev_suffix_block |> Q.INST [`ctx` |-> `C`]) >>
  disch_then (qspecl_then [`DROP s.vs_inst_idx bb.bb_instructions`, `s`, `bb`] mp_tac) >>
  simp[] >> metis_tac[ev_suffix_call_ctx]
QED

Theorem ev_step_fdom:
  ev_step orc p d fuel C inst s = OK t /\ inst_wf inst /\
  inst.inst_opcode <> PHI /\ ~is_terminator inst.inst_opcode ==>
  FDOM t.vs_vars = FDOM s.vs_vars UNION set inst.inst_outputs
Proof
  strip_tac >> Cases_on `inst.inst_opcode = GAS`
  >- (gvs[ev_step_gas, ev_gas_def, AllCaseEqs()] >>
      simp[update_var_def, finite_mapTheory.FDOM_FUPDATE] >>
      pred_setLib.SET_TAC[]) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (gvs[Once ev_step_def, AllCaseEqs()] >>
      drule bind_outputs_fdom >>
      simp[adopt_return_fmp_def, merge_callee_state_def] >>
      Cases_on `ret.iret_adopt_fmp` >> simp[]) >>
  `step_inst_base inst s = OK t` by gvs[Once ev_step_def] >>
  metis_tac[step_inst_base_fdom]
QED

Theorem ev_step_current_bb:
  ev_step orc p d fuel C inst s = OK t /\
  ~is_terminator inst.inst_opcode ==> t.vs_current_bb = s.vs_current_bb
Proof
  strip_tac >> Cases_on `inst.inst_opcode = GAS`
  >- (gvs[ev_step_gas, ev_gas_def, AllCaseEqs()] >> simp[update_var_def]) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (gvs[Once ev_step_def, AllCaseEqs()] >>
      `!pairs st. (FOLDL (\st' (out,value). update_var out value st') st pairs).vs_current_bb = st.vs_current_bb` by
        (Induct >> simp[] >> Cases >> simp[update_var_def]) >>
      gvs[bind_outputs_def, AllCaseEqs()] >>
      simp[adopt_return_fmp_def, merge_callee_state_def] >>
      Cases_on `ret.iret_adopt_fmp` >> simp[]) >>
  `step_inst fuel C inst s = OK t` by
    gvs[Once ev_step_def, step_inst_non_invoke] >>
  metis_tac[step_preserves_control_flow]
QED

Theorem ev_step_dominators:
  ev_step orc p d fuel C inst s = OK t /\ inst_wf inst /\
  ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode /\
  strict_dom_vars_defined fn s ==> strict_dom_vars_defined fn t
Proof
  strip_tac >>
  `inst.inst_opcode <> PHI` by (strip_tac >> gvs[is_pseudo_def]) >>
  drule_all ev_step_fdom >> strip_tac >>
  drule_all ev_step_current_bb >> strip_tac >>
  gvs[strict_dom_vars_defined_def] >> metis_tac[]
QED

Theorem ev_remaining_inv_step:
  wf_function fn /\ EVERY inst_wf bb.bb_instructions /\
  dft_remaining_inv fn bb (pre ++ y::post) s /\
  ~is_terminator y.inst_opcode /\ ev_step orc p d fuel C y s = OK t ==>
  dft_remaining_inv fn bb (pre ++ post)
    (t with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `MEM y bb.bb_instructions /\ ~is_pseudo y.inst_opcode` by
    metis_tac[dft_remaining_inv_head_order] >>
  `inst_wf y /\ y.inst_opcode <> PHI` by
    (fs[EVERY_MEM] >> metis_tac[is_pseudo_def]) >>
  drule_all ev_step_fdom >> strip_tac >>
  drule_all ev_step_current_bb >> strip_tac >>
  drule ev_step_labels >> strip_tac >>
  `strict_dom_vars_defined fn t` by
    (irule ev_step_dominators >> metis_tac[dft_remaining_inv_def]) >>
  `strict_dom_vars_defined fn (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    (gvs[strict_dom_vars_defined_def] >> metis_tac[]) >>
  gvs[dft_remaining_inv_def] >> rpt conj_tac
  >- (gvs[ALL_DISTINCT_APPEND] >> metis_tac[])
  >- (rpt strip_tac >> first_x_assum irule >>
      `!pre. id_before (pre ++ post) x y' ==>
        id_before (pre ++ y::post) x y'` by
        (Induct >> simp[id_before_cons] >> metis_tac[MEM_APPEND, MEM]) >>
      metis_tac[]) >>
  rpt strip_tac >> rename1 `MEM producer bb.bb_instructions` >>
  Cases_on `producer = y` >> gvs[] >> metis_tac[]
QED

Theorem ev_setup_callee_labels_bound:
  setup_callee fn args s = SOME t /\ ctx_labels_bound C s.vs_labels ==>
  ctx_labels_bound C t.vs_labels
Proof
  simp[setup_callee_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem ev_setup_callee_nonstatic:
  setup_callee fn args s = SOME t /\ ~s.vs_call_ctx.cc_static ==>
  ~t.vs_call_ctx.cc_static
Proof
  simp[setup_callee_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED
