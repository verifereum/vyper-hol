Theory dftGasInvTerminalReach
Ancestors
  dftGasInvTerminalPrefix dftGasInvPairedHistory dftGasInvPairedPrefix
  dftGasInvPrefixReach dftGasInvPrefixRun dftGasInvFlexibleTrace
  dftGasOracleDefs dftRunRel dftStructural venomExecSemantics venomExecProps
  venomInst venomState venomWf o1PassContract unitShapeDefs contextCodegenRel list rich_list

Theorem inv_ev_ftrace_current_bb:
  !xs s t. inv_ev_ftrace orc p d ctx xs s t ==>
    t.vs_current_bb = s.vs_current_bb
Proof
  Induct >> simp[inv_ev_ftrace_def] >> rpt strip_tac >>
  drule_all ev_step_nonterm_current_bb >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem inv_reachable_dret_exact:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C initial.vs_labels /\ o1_run_state_ok initial /\
  ev_reachable orc initial C' p d fn' inst t /\ inst.inst_opcode = DRET ==>
  ?fn bb bb'. MEM fn C.ctx_functions /\ fn' = dft_fn fn /\ dft_fn_rel fn fn' /\
    ev_reachable orc initial C p d fn inst t /\
    lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb'
Proof
  strip_tac >> drule inv_paired_history >> disch_then (qspec_then `C` mp_tac) >>
  simp[] >> strip_tac >>
  drule_all inv_paired_prefix_cut >> strip_tac
  >- gvs[is_pseudo_def] >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `EVERY inst_shape_ok bb.bb_instructions` by
    (fs[o1_ctx_shape_def, EVERY_MEM] >>
     first_x_assum (drule_then assume_tac) >>
     fs[o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM, fn_insts_def] >>
     rpt strip_tac >> first_x_assum irule >>
     simp[fn_insts_blocks_MEM] >> qexists_tac `bb` >> simp[]) >>
  drule_all inv_lookup_dret_prefix >> strip_tac >>
  `t.vs_current_bb = s0.vs_current_bb` by
    metis_tac[inv_ev_ftrace_current_bb] >>
  `get_instruction bb t.vs_inst_idx = SOME inst` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  `bb.bb_label = s0.vs_current_bb` by metis_tac[lookup_block_label] >>
  `ev_reachable orc initial C p d fn inst t` by
    (irule inv_ev_prefix_reachable >>
     qexistsl_tac [`bb`, `startinst`, `LENGTH srcpre`, `s0`] >> simp[]) >>
  qexistsl_tac [`fn`, `bb`, `bb'`] >> metis_tac[]
QED
