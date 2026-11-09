Theory dftGasInvMemoryObservation
Ancestors
  dftGasInvPairedHistory dftGasInvPairedPrefix dftGasInvExtraction
  dftGasInvCrossingProbe dftGasInvReachAvailability dftGasInvOracleFrame
  dftGasInvPrefixReach dftGasInvPrefixRun dftGasInvFlexibleTrace
  dftGasOracleDefs dftRunRel dftScheduleOrder dftStructural dftDefs
  venomEffects passSharedDefs
  o1PassContract unitShapeDefs venomExecSemantics venomExecProofs
  venomInst venomState venomWf contextCodegenRel list rich_list

Theorem inv_memory_observation_nonpseudo:
  inv_memory_observation opc ==> ~is_pseudo opc
Proof
  simp[inv_memory_observation_def] >> strip_tac >> gvs[is_pseudo_def]
QED

Theorem inv_flipped_memory_impossible[local]:
  is_flippable i.inst_opcode ==> ~inv_memory_observation (flip_operands i).inst_opcode
Proof
  Cases_on `i.inst_opcode` >>
  simp[is_flippable_def, is_commutative_def, is_comparator_def] >>
  namedCases_on `i.inst_operands` ["", "a rest"] >> simp[flip_operands_def, inv_memory_observation_def] >>
  namedCases_on `rest` ["", "b more"] >> simp[flip_operands_def, inv_memory_observation_def] >>
  Cases_on `more` >>
  simp[flip_operands_def, is_comparator_def, flip_comparison_opcode_def,
       inv_memory_observation_def]
QED

Theorem inv_memory_observation_original:
  from_block bi inst /\ inv_memory_observation inst.inst_opcode ==> MEM inst bi
Proof
  simp[from_block_def] >> strip_tac >> gvs[] >>
  metis_tac[inv_flipped_memory_impossible]
QED

Theorem inv_reachable_memory_observation:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C initial.vs_labels /\ o1_run_state_ok initial /\
  ev_reachable orc initial C' p d fn' inst t /\
  inv_memory_observation inst.inst_opcode ==>
  ?fn sS bb bb'. MEM fn C.ctx_functions /\ fn' = dft_fn fn /\ dft_fn_rel fn fn' /\
    ev_reachable orc initial C p d fn inst sS /\
    lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    sS.vs_current_bb = t.vs_current_bb /\
    (!op. MEM op inst.inst_operands ==> eval_operand op sS = eval_operand op t) /\
    sS.vs_initial_fmp = t.vs_initial_fmp
Proof
  strip_tac >> drule inv_paired_history >> disch_then (qspec_then `C` mp_tac) >>
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
  `~s0.vs_call_ctx.cc_static` by
    (irule inv_ev_reachable_nonstatic >> goal_assum (drule_at Any) >>
     gvs[o1_run_state_ok_def]) >>
  `dft_remaining_inv fn bb sourcebody s0` by
    (`s0.vs_inst_idx = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions)` by simp[] >>
     drule_all inv_ev_reachable_source_initialized >> simp[]) >>
  `?sS. inv_ev_prefix orc p d C bb (LENGTH srcpre) s0 sS /\
    sS.vs_inst_idx = LENGTH pseudos + LENGTH srcpre /\
    (!op. MEM op inst.inst_operands ==> eval_operand op sS = eval_operand op t) /\
    sS.vs_initial_fmp = t.vs_initial_fmp` by
    (irule inv_lookup_scheduled_observation >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`bb'`, `fn'`, `s0.vs_current_bb`, `scheduled`, `inst`, `targetpost`] >>
     gvs[] >>
     rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
     pure_asm_rewrite_tac [GSYM APPEND_ASSOC, APPEND]) >>
  suspend "reachable"

QED

Resume inv_reachable_memory_observation[reachable]:
  `sS.vs_current_bb = s0.vs_current_bb` by
    (qpat_x_assum `inv_ev_prefix _ _ _ C bb _ s0 sS` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     qid_spec_tac `sS` >> qid_spec_tac `s0` >>
     Q.SPEC_TAC (`LENGTH srcpre`, `nn:num`) >>
     Induct >> simp[inv_ev_prefix_suc] >>
     rpt strip_tac >> drule_all ev_step_nonterm_current_bb >>
     strip_tac >> first_x_assum drule >> simp[]) >>
  `bb.bb_label = s0.vs_current_bb` by metis_tac[lookup_block_label] >>
  `get_instruction bb sS.vs_inst_idx = SOME inst` by
    (simp[get_instruction_def, EL_APPEND_EQN]) >>
  `ev_reachable orc initial C p d fn inst sS` by
    (irule inv_ev_prefix_reachable >>
     qexistsl_tac [`bb`, `startinst`, `LENGTH srcpre`, `s0`] >> simp[]) >>
  qexistsl_tac [`fn`, `sS`, `bb`, `bb'`] >> simp[] >>
  metis_tac[lookup_block_label]
QED
Finalise inv_reachable_memory_observation
