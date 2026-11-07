Theory dftGasFromListReachBoundary
Ancestors
  dftGasFromListReplay dftGasFromListRestore dftGasOracleDefs
  contextCodegenRel venomExecProofs venomInstProofs venomInstProofs1 gasOracleReplay
  venomExecSemantics venomInst venomState list arithmetic

Theorem lookup_instruction_active:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  active_inst fn inst s
Proof
  simp[get_instruction_def] >> rpt strip_tac >>
  drule lookup_block_MEM >> strip_tac >>
  drule lookup_block_label >> strip_tac >>
  simp[active_inst_def] >> qexists_tac `bb` >> simp[]
QED

Theorem ev_step_preserves_current_bb:
  ev_step orc p d fuel ctx inst s = OK t /\
  ~is_terminator inst.inst_opcode ==>
  t.vs_current_bb = s.vs_current_bb
Proof
  Cases_on `inst.inst_opcode = GAS`
  >- (simp[ev_step_def, ev_gas_def] >>
      Cases_on `inst.inst_outputs` >> simp[] >>
      rename1 `inst.inst_outputs = out::outs` >>
      Cases_on `outs` >> simp[] >>
      gvs[AllCaseEqs(), update_var_def] >> rpt strip_tac >> gvs[]) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (simp[ev_step_def] >> rpt strip_tac >>
      gvs[AllCaseEqs()] >>
      rename1 `bind_outputs _ ret.iret_values _ = SOME t` >>
      Cases_on `ret.iret_adopt_fmp` >>
      gvs[bind_outputs_def, adopt_return_fmp_def, merge_callee_state_def] >>
      qspec_then `\s:venom_state. s.vs_current_bb` mp_tac
        foldl_update_var_preserves >> simp[update_var_def]) >>
  simp[ev_step_def] >> rpt strip_tac >>
  `step_inst fuel ctx inst s = OK t` by simp[Once step_inst_def] >>
  drule_all step_preserves_control_flow >> simp[]
QED

Theorem ev_block_exit:
  !s. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  (!i. active_inst fn i s ==> ev_reachable orc vs0 ctx p d fn i s) /\
  ev_block orc p d fuel ctx bb s = OK v /\ ~v.vs_halted ==>
  ?i t. ev_reachable orc vs0 ctx p d fn i t /\
    active_inst fn i t /\ is_terminator i.inst_opcode /\
    ev_step orc p d fuel ctx i t = OK v
Proof
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `ev_block _ _ _ _ _ _ _ = _` mp_tac >>
      simp[Once ev_block_def]) >>
  rename1 `get_instruction _ _ = SOME inst` >>
  `active_inst fn inst s` by (irule lookup_instruction_active >> simp[]) >>
  `ev_reachable orc vs0 ctx p d fn inst s` by metis_tac[] >>
  qpat_x_assum `ev_block _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once ev_block_def] >>
  Cases_on `ev_step orc p d fuel ctx inst s` >> simp[] >>
  rename1 `ev_step _ _ _ _ _ _ _ = OK out` >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]) >>
  strip_tac >>
  `out.vs_current_bb = s.vs_current_bb` by
    (drule_all ev_step_preserves_current_bb >> simp[]) >>
  first_x_assum irule >>
  simp[] >>
  qexists_tac `out with vs_inst_idx := SUC s.vs_inst_idx` >>
  simp[] >> conj_tac
  >- (gvs[get_instruction_def]) >>
  conj_tac
  >- (rpt strip_tac >> metis_tac[ev_reachable_next]) >>
  gvs[]
QED

Theorem ev_block_next_entry:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  (!i. active_inst fn i s ==> ev_reachable orc vs0 ctx p d fn i s) /\
  ev_block orc p d fuel ctx bb s = OK v /\ ~v.vs_halted /\
  enters_block fn v w /\ active_inst fn inst w ==>
  ev_reachable orc vs0 ctx p (SUC d) fn inst w
Proof
  strip_tac >> drule_all ev_block_exit >> strip_tac >>
  metis_tac[ev_reachable_block]
QED
