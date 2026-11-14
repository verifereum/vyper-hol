(* Expose the source shadow prefix for an actually reached DFT observation. *)
Theory dftStaticMemoryObservation
Ancestors
  dftStaticShadowObservation dftStaticReachAvailability staticShadowEventReachable
  staticShadowDefs dftGasInvMemoryObservation dftGasInvPairedHistory
  dftGasInvPairedPrefix dftGasInvCrossingProbe dftGasInvFlexibleTrace dftGasInvTerminalReach
  dftGasInvPrefixRun dftGasOracleDefs dftGasInvExtraction dftRunRel dftScheduleOrder dftStructural dftDefs
  o1PassContract unitShapeDefs venomExecSemantics venomInst venomState
  venomWf venomExecProofs contextCodegenRel list

Definition ev_shadow_prefix_reachable_def:
  ev_shadow_prefix_reachable orc initial C p d fn inst sS <=>
    ?s0 startinst bb bb' pseudos srcpre srcpost scheduled targetpost t.
      MEM fn C.ctx_functions /\
      ev_reachable orc initial C p d fn startinst s0 /\
      lookup_block s0.vs_current_bb fn.fn_blocks = SOME bb /\
      lookup_block s0.vs_current_bb (dft_fn fn).fn_blocks = SOME bb' /\
      dftScheduleOrder$dft_block_rel bb bb' /\
      s0.vs_current_bb = t.vs_current_bb /\
      s0.vs_inst_idx = LENGTH pseudos /\
      bb.bb_instructions = pseudos ++ (srcpre ++ inst::srcpost) /\
      bb'.bb_instructions = pseudos ++ (scheduled ++ inst::targetpost) /\
      EVERY (\i. is_pseudo i.inst_opcode) pseudos /\
      EVERY (\i. ~is_pseudo i.inst_opcode) (srcpre ++ inst::srcpost) /\
      EVERY inst_shape_ok bb.bb_instructions /\
      dft_remaining_inv fn bb (srcpre ++ inst::srcpost) s0 /\
      inv_ev_ftrace orc p d C scheduled s0 t /\
      inv_ev_prefix orc p d C bb (LENGTH srcpre) (static_shadow s0) sS /\
      sS.vs_current_bb = s0.vs_current_bb /\
      sS.vs_inst_idx = LENGTH pseudos + LENGTH srcpre /\
      (!op. MEM op inst.inst_operands ==> eval_operand op sS = eval_operand op t) /\
      sS.vs_initial_fmp = t.vs_initial_fmp
End

Theorem inv_reachable_memory_observation_shadow_prefix:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C initial.vs_labels /\ o1_initial_state_ok initial /\
  initial.vs_fmp = initial.vs_initial_fmp /\ code_layout_valid initial /\
  initial.vs_call_ctx.cc_static /\
  ev_reachable orc initial C' p d fn' inst t /\
  inv_memory_observation inst.inst_opcode ==>
  ?fn s0 startinst bb bb' pseudos srcpre srcpost scheduled targetpost sS.
    MEM fn C.ctx_functions /\ fn' = dft_fn fn /\ dft_fn_rel fn fn' /\
    ev_reachable orc initial C p d fn startinst s0 /\
    lookup_block s0.vs_current_bb fn.fn_blocks = SOME bb /\
    lookup_block s0.vs_current_bb fn'.fn_blocks = SOME bb' /\
    s0.vs_current_bb = t.vs_current_bb /\ s0.vs_inst_idx = LENGTH pseudos /\
    bb.bb_instructions = pseudos ++ (srcpre ++ inst::srcpost) /\
    bb'.bb_instructions = pseudos ++ (scheduled ++ inst::targetpost) /\
    EVERY (\i. is_pseudo i.inst_opcode) pseudos /\
    EVERY (\i. ~is_pseudo i.inst_opcode) (srcpre ++ inst::srcpost) /\
    EVERY inst_shape_ok bb.bb_instructions /\
    dft_remaining_inv fn bb (srcpre ++ inst::srcpost) s0 /\
    inv_ev_ftrace orc p d C scheduled s0 t /\
    inv_ev_prefix orc p d C bb (LENGTH srcpre) (static_shadow s0) sS /\
    (!op. MEM op inst.inst_operands ==> eval_operand op sS = eval_operand op t) /\
    sS.vs_initial_fmp = t.vs_initial_fmp
Proof
  strip_tac >> drule inv_paired_history_static >> disch_then (qspec_then `C` mp_tac) >>
  simp[] >> strip_tac >>
  drule_all inv_paired_prefix_cut >> strip_tac
  >- metis_tac[inv_memory_observation_nonpseudo] >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions = pseudos /\
   FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions = sourcebody` by
    (`FILTER (\i. is_pseudo i.inst_opcode) pseudos = pseudos /\
      FILTER (\i. ~is_pseudo i.inst_opcode) pseudos = [] /\
      FILTER (\i. is_pseudo i.inst_opcode) sourcebody = [] /\
      FILTER (\i. ~is_pseudo i.inst_opcode) sourcebody = sourcebody` by
       (simp[FILTER_EQ_ID, FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >>
     asm_rewrite_tac[FILTER_APPEND_DISTRIB, APPEND_NIL, APPEND]) >>
  `from_block bb.bb_instructions inst` by
    (drule_all dft_fn_rel_lookup_order >> simp[dft_block_rel_def] >>
     strip_tac >> gvs[EVERY_MEM] >> metis_tac[MEM_APPEND, MEM]) >>
  `MEM inst bb.bb_instructions` by metis_tac[inv_memory_observation_original] >>
  `MEM inst sourcebody` by
    (gvs[EVERY_MEM] >> metis_tac[MEM_APPEND, inv_memory_observation_nonpseudo]) >>
  `?srcpre srcpost. sourcebody = srcpre ++ inst::srcpost` by metis_tac[MEM_SPLIT] >>
  `EVERY inst_shape_ok bb.bb_instructions` by
    (fs[o1_ctx_shape_def, EVERY_MEM] >>
     first_x_assum (drule_then assume_tac) >>
     fs[o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM, fn_insts_def] >>
     rpt strip_tac >> first_x_assum irule >>
     simp[fn_insts_blocks_MEM] >> qexists_tac `bb` >> simp[]) >>
  `s0.vs_call_ctx.cc_static` by metis_tac[static_shadow_ev_reachable] >>
  `dft_remaining_inv fn bb sourcebody s0` by
    (`s0.vs_inst_idx = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions)` by simp[] >>
     drule_all inv_ev_reachable_source_initialized_static >> simp[]) >>
  `?sS. inv_ev_prefix orc p d C bb (LENGTH srcpre) (static_shadow s0) sS /\
    sS.vs_inst_idx = LENGTH pseudos + LENGTH srcpre /\
    (!op. MEM op inst.inst_operands ==> eval_operand op sS = eval_operand op t) /\
    sS.vs_initial_fmp = t.vs_initial_fmp` by
    (irule inv_lookup_scheduled_observation_shadow >> simp[static_shadow_rel_initial] >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`bb'`, `fn`, `fn'`, `s0.vs_current_bb`, `scheduled`, `inst`, `targetpost`] >>
     gvs[] >>
     rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
     pure_asm_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >> simp[static_shadow_rel_initial]) >>
  `s0.vs_current_bb = t.vs_current_bb` by metis_tac[lookup_block_label] >>
  qexistsl_tac [`fn`, `s0`, `startinst`, `bb`, `bb'`, `pseudos`,
               `srcpre`, `srcpost`, `scheduled`, `targetpost`, `sS`] >> gvs[] >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  pure_asm_rewrite_tac [GSYM APPEND_ASSOC, APPEND]
QED

Theorem inv_reachable_memory_observation_shadow:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C initial.vs_labels /\ o1_initial_state_ok initial /\
  initial.vs_fmp = initial.vs_initial_fmp /\ code_layout_valid initial /\
  initial.vs_call_ctx.cc_static /\
  ev_reachable orc initial C' p d fn' inst t /\
  inv_memory_observation inst.inst_opcode ==>
  ?fn sS. MEM fn C.ctx_functions /\ fn' = dft_fn fn /\ dft_fn_rel fn fn' /\
    ev_shadow_prefix_reachable orc initial C p d fn inst sS /\
    active_inst fn inst sS /\ sS.vs_current_bb = t.vs_current_bb /\
    (!op. MEM op inst.inst_operands ==> eval_operand op sS = eval_operand op t) /\
    sS.vs_initial_fmp = t.vs_initial_fmp
Proof
  strip_tac >> drule_all inv_reachable_memory_observation_shadow_prefix >> strip_tac >>
  `dftScheduleOrder$dft_block_rel bb bb'` by metis_tac[dft_fn_rel_lookup_order] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s0.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `inv_ev_ftrace orc p d C srcpre (static_shadow s0) sS <=>
   inv_ev_prefix orc p d C bb (LENGTH srcpre) (static_shadow s0) sS` by
    (irule inv_ev_ftrace_slice >> qexistsl_tac [`pseudos`, `inst::srcpost`] >>
     simp[static_shadow_def, APPEND_ASSOC]) >>
  `inv_ev_ftrace orc p d C srcpre (static_shadow s0) sS` by metis_tac[] >>
  `sS.vs_current_bb = s0.vs_current_bb /\
   sS.vs_inst_idx = LENGTH pseudos + LENGTH srcpre` by
    (drule inv_ev_ftrace_current_bb >> drule inv_ev_ftrace_idx >>
     simp[static_shadow_def]) >>
  `active_inst fn inst sS` by
    (simp[active_inst_def] >> qexists_tac `bb` >> simp[EL_APPEND_EQN]) >>
  qexistsl_tac [`fn`, `sS`] >> simp[] >>
  simp[ev_shadow_prefix_reachable_def] >>
  qexistsl_tac [`s0`, `startinst`, `bb`, `bb'`, `pseudos`, `srcpre`,
               `srcpost`, `scheduled`, `targetpost`, `t`] >> gvs[] >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  pure_asm_rewrite_tac [GSYM APPEND_ASSOC, APPEND]
QED
