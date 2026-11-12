Theory fmpStageBlockSimEntryAssembly
Ancestors
  fmpStageRel fmpStageBlockSimEntryPhis fmpStageBlockSimEntryLedger
  fmpStageOpBase fmpStageReclaimSound fmpLowerDefs fmpLowerReclaimPlan
  o1FrameLockstep livenessProofs venomWfProps
  livenessDefs livenessTransferProofs o1PassContract unitShapeDefs
  venomWf venomInst venomExecSemantics
  rich_list finite_map list

Theorem fmp_entry_lowered_analysis:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE ==>
  ?states. fmp_reclaim_states infos fn = SOME states
Proof
  simp[fmp_stage_lowered_def] >> rpt strip_tac >>
  gvs[fmp_lower_function_with_info_def, AllCaseEqs()] >>
  metis_tac[analyze_fmp_reclaims_candidate]
QED

Theorem fmp_entry_effect_cases:
  !ins prev v u. phi_eff (SOME prev) v ins = SOME (Var u) ==>
    (u = v /\ EVERY (\q. ~MEM v q.inst_outputs) (collect_phis ins)) \/
    (?phi. MEM phi (collect_phis ins) /\ MEM v phi.inst_outputs /\
      resolve_phi prev phi.inst_operands = SOME (Var u))
Proof
  Induct >> simp[phi_eff_def, phi_read_def, collect_phis_def] >>
  rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  Cases_on `MEM v h.inst_outputs` >> simp[]
  >- (Cases_on `h.inst_outputs = [v]` >> simp[] >> metis_tac[]) >>
  first_x_assum (qspecl_then [`prev`,`v`,`u`] mp_tac) >>
  Cases_on `phi_read (SOME prev) v ins` >> simp[phi_eff_def] >>
  metis_tac[]
QED

Theorem fmp_entry_effect_live:
  wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
  fmp_reclaim_states infos fn = SOME states /\
  MEM pl (cfg_analyze fn).cfg_dfs_pre /\
  MEM sl (cfg_analyze fn).cfg_dfs_pre /\
  MEM sl (cfg_succs_of (cfg_analyze fn) pl) /\
  lookup_block pl fn.fn_blocks = SOME pb /\
  lookup_block sl fn.fn_blocks = SOME bb /\
  pb.bb_instructions <> [] /\
  MEM v (live_vars_at (liveness_analyze fn) sl
    (phi_prefix_length bb.bb_instructions)) /\
  phi_eff (SOME pl) v bb.bb_instructions = SOME (Var u) ==>
  MEM u (live_vars_at (liveness_analyze fn) pl
    (PRE (LENGTH pb.bb_instructions)))
Proof
  strip_tac >> drule_all fmp_stage_live_edge >> strip_tac >>
  drule fmp_entry_effect_cases >> strip_tac >> gvs[]
  >- (gvs[EVERY_MEM] >> metis_tac[]) >-
  (`phi = phi'` by
     (irule ssa_outputs_same_inst >>
      conj_tac >- (qexists `fn` >> simp[fn_insts_blocks_MEM] >>
        metis_tac[collect_phis_mem, lookup_block_mem]) >>
      qexists `v` >> simp[]) >>
   gvs[])
  >- gvs[EVERY_MEM] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem fmp_entry_effect_tracked:
  MEM bb fn.fn_blocks /\ ~retpc_var fn v /\
  phi_eff (SOME pl) v bb.bb_instructions = SOME (Var u) ==>
  ~retpc_var fn u
Proof
  strip_tac >> drule fmp_entry_effect_cases >> strip_tac >> gvs[] >>
  `MEM phi bb.bb_instructions /\ phi.inst_opcode = PHI` by
    metis_tac[collect_phis_mem] >>
  `MEM phi (fn_insts fn)` by
    (simp[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `MEM (Var u) phi.inst_operands` by
    metis_tac[venomExecProofsTheory.resolve_phi_MEM_el] >>
  gvs[retpc_var_def] >> metis_tac[copy_phi_var_phi]
QED
