Theory dftGasSimEndpoint
Ancestors
  dftGasSimInvariant dftGasSimBoundary dftGasOracleDefs
  venomExecProofs venomExecSemantics venomState venomInst
  list pred_set finite_map venomWf

Theorem ev_step_fdom_mono:
  ev_step orc p d fuel C inst s = OK t /\ inst_wf inst ==>
  FDOM s.vs_vars SUBSET FDOM t.vs_vars
Proof
  strip_tac >> Cases_on `is_terminator inst.inst_opcode`
  >- (`inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE` by
        (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
      `step_inst fuel C inst s = OK t` by
        gvs[Once ev_step_def, step_inst_non_invoke] >>
      gvs[SUBSET_DEF] >> rpt strip_tac >>
      drule_all step_terminator_preserves_vars >>
      disch_then (qspec_then `x` mp_tac) >>
      gvs[lookup_var_def, FLOOKUP_DEF] >> metis_tac[optionTheory.NOT_NONE_SOME]) >>
  Cases_on `inst.inst_opcode = PHI`
  >- gvs[Once ev_step_def, step_inst_base_phi_error] >>
  drule_all ev_step_fdom >> simp[SUBSET_DEF]
QED

Theorem ev_suffix_fdom_mono:
  !xs s t. EVERY inst_wf xs /\ ev_suffix orc p d fuel C xs s = OK t ==>
  FDOM s.vs_vars SUBSET FDOM t.vs_vars
Proof
  Induct >> simp[ev_suffix_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `ev_step orc p d fuel C h s` >> gvs[] >>
  drule_all ev_step_fdom_mono >> strip_tac >>
  Cases_on `is_terminator h.inst_opcode`
  >- (Cases_on `v.vs_halted` >> gvs[]) >>
  gvs[] >> first_x_assum drule >> simp[] >>
  metis_tac[SUBSET_TRANS]
QED

Theorem ev_block_fdom_mono:
  ev_block orc p d fuel C bb s = OK t /\ bb_well_formed bb /\
  EVERY inst_wf bb.bb_instructions ==>
  FDOM s.vs_vars SUBSET FDOM t.vs_vars
Proof
  strip_tac >>
  mp_tac (ev_suffix_block |> Q.INST [`ctx` |-> `C`]) >>
  disch_then (qspecl_then [`DROP s.vs_inst_idx bb.bb_instructions`, `s`, `bb`] mp_tac) >>
  simp[] >> strip_tac >>
  irule ev_suffix_fdom_mono >>
  goal_assum (drule_at Any) >>
  `EVERY inst_wf (TAKE s.vs_inst_idx bb.bb_instructions ++
     DROP s.vs_inst_idx bb.bb_instructions)` by
       (pure_rewrite_tac[TAKE_DROP] >> simp[]) >>
  gvs[EVERY_APPEND]
QED

Theorem ev_block_output_in_fdom_aux[local]:
  !bb idx v n fuel C s t.
    idx < LENGTH bb.bb_instructions /\
    ~is_terminator (EL idx bb.bb_instructions).inst_opcode /\
    MEM v (EL idx bb.bb_instructions).inst_outputs /\
    n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
    ev_block orc p d fuel C bb s = OK t /\
    bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
    s.vs_inst_idx <= idx ==> v IN FDOM t.vs_vars
Proof
  ntac 3 gen_tac >> completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >>
  qpat_x_assum `ev_block _ _ _ _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[ev_block_def] >> simp[get_instruction_def] >>
  Cases_on `ev_step orc p d fuel C (EL s.vs_inst_idx bb.bb_instructions) s` >>
  gvs[] >> rename1 `ev_step _ _ _ _ _ _ s = OK u` >>
  Cases_on `is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode`
  >- (gvs[bb_well_formed_def] >>
      `s.vs_inst_idx = PRE (LENGTH bb.bb_instructions)` by
        (first_x_assum irule >> simp[] >> decide_tac) >>
      `idx = s.vs_inst_idx` by decide_tac >> gvs[]) >>
  simp[] >> strip_tac >> Cases_on `s.vs_inst_idx = idx`
  >- (`inst_wf (EL idx bb.bb_instructions)` by gvs[EVERY_EL] >>
      `(EL idx bb.bb_instructions).inst_opcode <> PHI` by
        (strip_tac >> gvs[Once ev_step_def, step_inst_base_phi_error]) >>
      gvs[] >> drule_all ev_step_fdom >> strip_tac >>
      `v IN FDOM u.vs_vars` by gvs[] >>
      drule_all ev_block_fdom_mono >> simp[SUBSET_DEF]) >>
  first_x_assum (qspec_then
    `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> disch_then irule >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem ev_block_outputs_in_fdom_from_prefix:
  ev_block orc p d fuel C bb s = OK t /\
  bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
  (!j w. j < s.vs_inst_idx /\ j < LENGTH bb.bb_instructions /\
         MEM w (EL j bb.bb_instructions).inst_outputs ==>
         w IN FDOM s.vs_vars) /\
  idx < LENGTH bb.bb_instructions /\
  ~is_terminator (EL idx bb.bb_instructions).inst_opcode /\
  MEM v (EL idx bb.bb_instructions).inst_outputs ==>
  v IN FDOM t.vs_vars
Proof
  strip_tac >> Cases_on `idx < s.vs_inst_idx`
  >- (`v IN FDOM s.vs_vars` by metis_tac[] >>
      drule_all ev_block_fdom_mono >> simp[SUBSET_DEF]) >>
  irule ev_block_output_in_fdom_aux >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED
