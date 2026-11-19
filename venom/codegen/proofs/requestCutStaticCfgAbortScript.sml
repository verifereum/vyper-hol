Theory requestCutStaticCfgAbort
Ancestors
  requestCutStaticSuffix requestCutCfgStatic requestCutInvokeReady
  fnEntryStep analysisSimProofsBase dftGasInvCrossingProbe
  contextRawReachable contextCodegenRel unitShapeDefs stackPlanGen staticAbortDefs
  venomExecSemantics venomExecProofs venomInst venomWf venomState list arithmetic

Theorem request_cut_cfg_static_abort:
  cfg_norm_joint_cursors C8 unit.cu_context (schedules,(rounds,cells),saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
  in_static_abort_prefix fn8 s8 /\
  inv_memory_observation inst9.inst_opcode /\
  unit_shape_ok unit /\ codegen_ready unit.cu_context /\
  raw_reachable vs0 unit.cu_context fn9 inst9 s9 /\
  (!i l. MEM i (fn_insts fn9) /\ i.inst_opcode <> PHI /\
    MEM (Label l) (compute_operands i) ==> IS_SOME (FLOOKUP s9.vs_labels l)) ==>
  ?i t a post.
    raw_reachable vs0 unit.cu_context fn9 i t /\ i.inst_opcode <> INVOKE /\
    step_inst 0 unit.cu_context i t = Abort a post /\ t.vs_requests = s9.vs_requests
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all request_cut_cfg_static_prefix >>
  simp_tac bool_ss [in_static_abort_prefix_def, static_abort_at_def] >> strip_tac >>
  drule cfg_norm_joint_cursor_supply >> strip_tac >>
  `MEM bb fn9.fn_blocks /\ bb.bb_label = s9.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `s9.vs_inst_idx < LENGTH bb.bb_instructions /\ inst9 = EL s9.vs_inst_idx bb.bb_instructions` by
    (qpat_x_assum `active_inst fn9 inst9 s9` mp_tac >>
     simp[active_inst_def] >> strip_tac >>
     `bb' = bb` by (irule same_label_same_block >> metis_tac[]) >> gvs[]) >>
  `inst9.inst_opcode <> PHI /\ ~is_param_opcode inst9.inst_opcode` by
    fs[inv_memory_observation_def, is_param_opcode_def] >>
  `phi_prefix_length bb.bb_instructions <= s9.vs_inst_idx` by
    (CCONTR_TAC >> `s9.vs_inst_idx < phi_prefix_length bb.bb_instructions` by decide_tac >>
     `s9.vs_inst_idx < LENGTH (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)` by
       (simp[LENGTH_TAKE_EQ] >> decide_tac) >>
     mp_tac (Q.SPEC `s9.vs_inst_idx` (SIMP_RULE bool_ss [EVERY_EL]
       (Q.SPEC `bb.bb_instructions` phi_prefix_all_phi))) >>
     simp[EL_TAKE] >> metis_tac[]) >>
  `LENGTH (get_params bb.bb_instructions) <= s9.vs_inst_idx` by
    (CCONTR_TAC >> `s9.vs_inst_idx < LENGTH (get_params bb.bb_instructions)` by decide_tac >>
     metis_tac[get_params_el]) >>
  `codegen_ready_fn fn9 /\ fn_shape_ok fn9` by
    fs[codegen_ready_def, unit_shape_ok_def, EVERY_MEM] >>
  mp_tac (Q.SPECL [`j - s9.vs_inst_idx`, `s9`, `inst9`]
    (Q.INST [`fn` |-> `fn9`, `C` |-> `unit.cu_context`] request_cut_static_suffix_abort)) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
     (fs[static_abort_pair_def] >> decide_tac)))) >>
  simp[]
QED
