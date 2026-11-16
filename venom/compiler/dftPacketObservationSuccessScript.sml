Theory dftPacketObservationSuccess
Ancestors
  dftGasInvCallerExtract dftGasInvExtraction dftGasNativePrefixReplay
  dftRunRel dftStructural dftCorrectness dftGasInvPrefixRun dftGasInvReachSlice
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

Theorem dft_packet_native_observation_success:
  !C C' func func' bb bb' name ps pre i post scheduled yi later
    be u b0 gs p d source_fuel target_fuel orc.
    LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
    dft_fn_rel func func' /\ MEM bb func.fn_blocks /\
    lookup_block name func.fn_blocks = SOME bb /\
    lookup_block name func'.fn_blocks = SOME bb' /\
    bb.bb_instructions = ps ++ (pre ++ i::post) /\
    EVERY (\x. is_pseudo x.inst_opcode) ps /\
    EVERY (\x. ~is_pseudo x.inst_opcode) (pre ++ i::post) /\
    EVERY inst_shape_ok bb.bb_instructions /\
    bb'.bb_instructions = ps ++ (scheduled ++ yi::later) /\
    yi.inst_id = i.inst_id /\
    dft_remaining_inv func bb (pre ++ i::post) be /\
    be.vs_inst_idx = LENGTH ps /\ inv_memory_observation i.inst_opcode /\
    EVERY (\x. ~is_terminator x.inst_opcode) pre /\
    EVERY (\x. ~is_terminator x.inst_opcode) scheduled /\
    FOLDR (dft_exec_cons source_fuel C) OK pre
      (be with vs_gas_readings := gs) = OK u /\
    FOLDR (dft_exec_cons target_fuel C') OK scheduled be = OK b0 /\
    dftGasFromListTraceDefs$trace_agrees orc
      (dftGasFromListTraceDefs$trace_block p d source_fuel C func
        (bb with bb_instructions :=
          TAKE (LENGTH ps + LENGTH pre) bb.bb_instructions)
        (be with vs_gas_readings := gs)) /\
    dftGasFromListTraceDefs$trace_agrees orc
      (dftGasFromListTraceDefs$trace_block p d target_fuel C' func'
        (bb' with bb_instructions :=
          TAKE (LENGTH ps + LENGTH scheduled) bb'.bb_instructions) be) ==>
    (!op. MEM op i.inst_operands ==> eval_operand op u = eval_operand op b0) /\
    u.vs_initial_fmp = b0.vs_initial_fmp
Proof
  rpt gen_tac >> strip_tac >>
  `inv_ev_prefix orc p d C bb (LENGTH pre)
     (be with vs_gas_readings := b0.vs_gas_readings)
     (u with vs_gas_readings := b0.vs_gas_readings)` by
    (qspecl_then [`source_fuel`, `C`, `func`, `bb`,
       `be with vs_gas_readings := gs`, `u`, `p`, `d`, `LENGTH pre`,
       `orc`, `b0.vs_gas_readings`] mp_tac native_prefix_oracle >>
     simp[DROP_APPEND, TAKE_APPEND, TAKE_LENGTH_TOO_LONG] >>
     disch_then irule >>
     qpat_x_assum `dftGasFromListTraceDefs$trace_agrees orc
       (dftGasFromListTraceDefs$trace_block _ _ source_fuel _ _ _ _)` mp_tac >>
     simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG]) >>
  `inv_ev_prefix orc p d C' bb' (LENGTH scheduled)
     (be with vs_gas_readings := b0.vs_gas_readings) b0` by
    (qspecl_then [`target_fuel`, `C'`, `func'`, `bb'`, `be`, `b0`,
       `p`, `d`, `LENGTH scheduled`, `orc`, `b0.vs_gas_readings`]
       mp_tac native_prefix_oracle >>
     simp[DROP_APPEND, TAKE_APPEND, TAKE_LENGTH_TOO_LONG] >>
     disch_then irule >>
     qpat_x_assum `dftGasFromListTraceDefs$trace_agrees orc
       (dftGasFromListTraceDefs$trace_block _ _ target_fuel _ _ _ _)` mp_tac >>
     simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG]) >>
  drule_all inv_ev_prefix_context_reflect >> strip_tac >>
  `inv_ev_ftrace orc p d C scheduled
     (be with vs_gas_readings := b0.vs_gas_readings) b0` by
    (drule_all inv_ev_prefix_ftrace >>
     simp[DROP_APPEND, TAKE_APPEND, TAKE_LENGTH_TOO_LONG]) >>
  `dft_remaining_inv func bb (pre ++ i::post)
     (be with vs_gas_readings := b0.vs_gas_readings)` by
    (irule dft_remaining_inv_gas_variant >> qexists_tac `be` >> simp[]) >>
  `(be with vs_gas_readings := b0.vs_gas_readings).vs_inst_idx = LENGTH ps` by simp[] >>
  drule_all packet_scheduled_observation_success >>
  simp[gasOracleReplayTheory.gas_eval_operand]
QED
