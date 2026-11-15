Theory dftPacketObservationSuccess
Ancestors
  dftGasInvCallerExtract dftGasInvExtraction dftGasNativePrefixReplay
  dftRunRel dftStructural dftCorrectness dftGasInvPrefixRun
  gasOracleReplay dftScheduleOrder dftWf venomWf list rich_list sorting

Theorem packet_scheduled_observation_success[local]:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' /\
  bb.bb_instructions = pseudos ++ (srcpre ++ obs::srcpost) /\
  EVERY (\i. is_pseudo i.inst_opcode) pseudos /\
  EVERY (\i. ~is_pseudo i.inst_opcode) (srcpre ++ obs::srcpost) /\
  EVERY inst_shape_ok bb.bb_instructions /\
  bb'.bb_instructions = pseudos ++ (scheduled ++ targetobs::targetpost) /\
  targetobs.inst_id = obs.inst_id /\
  dft_remaining_inv fn bb (srcpre ++ obs::srcpost) s0 /\
  s0.vs_inst_idx = LENGTH pseudos /\
  inv_ev_ftrace orc p d ctx scheduled s0 sT /\
  inv_memory_observation obs.inst_opcode /\
  inv_ev_prefix orc p d ctx bb (LENGTH srcpre) s0 sS ==>
  sS.vs_inst_idx = LENGTH pseudos + LENGTH srcpre /\
  (!op. MEM op obs.inst_operands ==> eval_operand op sS = eval_operand op sT) /\
  sS.vs_initial_fmp = sT.vs_initial_fmp
Proof
  strip_tac >>
  `FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions = pseudos /\
   FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions = srcpre ++ obs::srcpost` by
    (`FILTER (\i. is_pseudo i.inst_opcode) pseudos = pseudos /\
      FILTER (\i. ~is_pseudo i.inst_opcode) pseudos = [] /\
      FILTER (\i. is_pseudo i.inst_opcode) (srcpre ++ obs::srcpost) = [] /\
      FILTER (\i. ~is_pseudo i.inst_opcode) (srcpre ++ obs::srcpost) = srcpre ++ obs::srcpost` by
       (simp[FILTER_EQ_ID, FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >>
     asm_rewrite_tac[FILTER_APPEND_DISTRIB, APPEND_NIL, APPEND]) >>
  drule_all dft_fn_rel_lookup_order >> strip_tac >>
  qpat_x_assum `dft_block_rel _ _` mp_tac >>
  simp[dft_block_rel_def] >> strip_tac >> gvs[] >>
  `EVERY (from_block bb.bb_instructions) scheduled /\
   EVERY (from_block bb.bb_instructions) targetpost` by metis_tac[APPEND_ASSOC, APPEND] >>
  drule_all inv_ftrace_original_representatives >> strip_tac >>
  rename1 `inv_ev_ftrace orc p d ctx originals s0 sT` >>
  qpat_assum `EVERY (from_block _) targetpost`
    (mp_tac o MATCH_MP inv_from_block_representatives) >> strip_tac >>
  rename1 `MAP (\i. i.inst_id) later = MAP (\i. i.inst_id) targetpost` >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[dft_fn_rel_def, wf_fn_block_inst_ids_distinct] >>
  `PERM (originals ++ obs::later) (srcpre ++ obs::srcpost)` by
    (irule inv_original_ids_perm >> conj_tac
     >- (qexists_tac `bb.bb_instructions` >>
         fs[EVERY_MEM] >> metis_tac[MEM_APPEND, MEM]) >>
     asm_rewrite_tac[MAP_APPEND, MAP] >>
     metis_tac[APPEND_ASSOC, APPEND]) >>
  `ALL_DISTINCT (srcpre ++ obs::srcpost)` by
    metis_tac[dft_remaining_inv_def] >>
  `MAP (\i. i.inst_id) bb'.bb_instructions =
    MAP (\i. i.inst_id) pseudos ++ MAP (\i. i.inst_id) (originals ++ obs::later)` by
    (asm_rewrite_tac[MAP_APPEND, MAP] >> metis_tac[APPEND_ASSOC, APPEND]) >>
  qpat_x_assum `!x y. _` kall_tac >>
  qpat_x_assum `!x y. _` kall_tac >>
  irule (Q.INST [`bb` |-> `bb`, `pseudos` |-> `pseudos`,
    `srcpre` |-> `srcpre`, `srcpost` |-> `srcpost`]
    inv_lookup_normalized_observation_success) >>
  simp[] >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[MAP_APPEND] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[MAP_APPEND] >>
  qexistsl_tac [`bb'`, `fn`, `fn'`, `name`] >>
  simp[MAP_APPEND]
QED
