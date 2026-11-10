Theory dftGasInvCallerExtract
Ancestors
  dftGasInvCallerInput dftGasInvExtraction dftGasInvReachAvailability dftGasInvPrefixReach
  o1PassContract contextCodegenRel venomInstProofs1 venomExecProofs
  dftGasInvInversion dftGasInvFlexibleTrace dftGasInvResidualTrace
  dftGasInvSSAProbe dftGasInvOracleFrame dftGasInvCrossingProbe dftGasOracleDefs
  dftRunRel dftScheduleOrder dftCorrectness dftAvailability dftBlockSim dftStructural
  venomExecSemantics venomInst venomState list rich_list pred_set sorting
  dftSsaPreserve dftPermSim venomWf dftWf

Theorem inv_lookup_call_crossings[local]:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' /\
  bb.bb_instructions = pseudos ++ (srcpre ++ obs::srcpost) /\
  EVERY (\i. ~is_pseudo i.inst_opcode) (srcpre ++ obs::srcpost) /\
  MAP (\i. i.inst_id) bb'.bb_instructions =
    MAP (\i. i.inst_id) pseudos ++ MAP (\i. i.inst_id) (consumed ++ obs::later) /\
  ALL_DISTINCT (srcpre ++ obs::srcpost) /\
  PERM (consumed ++ obs::later) (srcpre ++ obs::srcpost) ==>
  EVERY (\x. dft_gas_swap_pair obs x /\ inst_wf x)
    (FILTER (\i. ~MEM i consumed) srcpre) /\
  EVERY (\x. dft_gas_swap_pair obs x /\ inst_wf x)
    (FILTER (\i. MEM i consumed) srcpost)
Proof
  strip_tac >> conj_tac >> simp[EVERY_MEM, MEM_FILTER] >>
  gen_tac >> strip_tac >>
  `MEM x bb.bb_instructions /\ MEM obs bb.bb_instructions /\
   ~is_pseudo x.inst_opcode /\ ~is_pseudo obs.inst_opcode` by
    (fs[EVERY_MEM] >> metis_tac[MEM_APPEND, MEM])
  >- (`x <> obs` by (gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
      `MEM x later` by
        (drule PERM_MEM_EQ >> disch_then (qspec_then `x` mp_tac) >> simp[]) >>
      `id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id obs.inst_id /\
       id_before (MAP (\i. i.inst_id) bb'.bb_instructions) obs.inst_id x.inst_id` by
        (asm_rewrite_tac[MAP_APPEND] >>
         simp[dftSsaPreserveTheory.id_before_append,
              dftSsaPreserveTheory.id_before_cons, MEM_MAP] >> metis_tac[]) >>
      drule_all inv_lookup_inversion_swap >> metis_tac[dft_gas_swap_pair_sym]) >>
  `id_before (MAP (\i. i.inst_id) bb.bb_instructions) obs.inst_id x.inst_id /\
   id_before (MAP (\i. i.inst_id) bb'.bb_instructions) x.inst_id obs.inst_id` by
    (asm_rewrite_tac[MAP_APPEND] >>
     simp[dftSsaPreserveTheory.id_before_append,
          dftSsaPreserveTheory.id_before_cons, MEM_MAP] >> metis_tac[]) >>
  drule_all inv_lookup_inversion_swap >> simp[]
QED

Theorem inv_lookup_normalized_invoke:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' /\
  bb.bb_instructions = pseudos ++ (srcpre ++ obs::srcpost) /\
  EVERY inst_shape_ok bb.bb_instructions /\
  EVERY (\i. ~is_pseudo i.inst_opcode) (srcpre ++ obs::srcpost) /\
  MAP (\i. i.inst_id) bb'.bb_instructions =
    MAP (\i. i.inst_id) pseudos ++
    MAP (\i. i.inst_id) (consumed ++ obs::later) /\
  ALL_DISTINCT (srcpre ++ obs::srcpost) /\
  PERM (consumed ++ obs::later) (srcpre ++ obs::srcpost) /\
  dft_remaining_inv fn bb (srcpre ++ obs::srcpost) s0 /\
  s0.vs_inst_idx = LENGTH pseudos /\ ~s0.vs_call_ctx.cc_static /\
  inv_ev_ftrace orc p d ctx consumed s0 sT /\ obs.inst_opcode = INVOKE ==>
  ?sS. inv_ev_prefix orc p d ctx bb (LENGTH srcpre) s0 sS /\
    sS.vs_inst_idx = LENGTH pseudos + LENGTH srcpre /\
    (!op. MEM op obs.inst_operands ==> eval_operand op sS = eval_operand op sT) /\
    (!callee args. setup_callee callee args sS = setup_callee callee args sT)
Proof
  strip_tac >>
  `ALL_DISTINCT consumed /\ ~MEM obs consumed /\
   EVERY (\i. MEM i (srcpre ++ obs::srcpost)) consumed` by
    (drule PERM_MEM_EQ >>
     `ALL_DISTINCT (consumed ++ obs::later)` by metis_tac[ALL_DISTINCT_PERM] >>
     gvs[ALL_DISTINCT_APPEND, EVERY_MEM] >> metis_tac[]) >>
  `wf_function fn /\ wf_ssa fn` by metis_tac[dft_fn_rel_def] >>
  drule_all inv_lookup_block_contract >> strip_tac >>
  drule_all inv_lookup_missing_predecessors >> strip_tac >>
  drule_all inv_lookup_call_crossings >> strip_tac >>
  `~sT.vs_call_ctx.cc_static` by metis_tac[inv_ftrace_call_ctx] >>
  `dft_remaining_inv fn bb
      (FILTER (\i. ~MEM i consumed) srcpre ++
       obs::FILTER (\i. ~MEM i consumed) srcpost) sT` by
    (drule_all inv_ftrace_remaining >> simp[FILTER_APPEND_DISTRIB]) >>
  `inv_memory_observation obs.inst_opcode` by simp[inv_memory_observation_def] >>
  `?u. inv_ev_trace orc p d 0 ctx (FILTER (\i. ~MEM i consumed) srcpre) sT u /\
       (!op. MEM op obs.inst_operands ==> eval_operand op u = eval_operand op sT)` by
    (drule_all inv_remaining_trace_extension >>
     simp[inv_memory_observation_def] >> metis_tac[]) >>
  `inv_ev_ftrace orc p d ctx (FILTER (\i. ~MEM i consumed) srcpre) sT u` by
    metis_tac[inv_ev_trace_ftrace] >>
  `!callee args. setup_callee callee args u = setup_callee callee args sT` by
    metis_tac[inv_ev_invoke_trace_setup] >>
  `inv_ev_ftrace orc p d ctx
     (consumed ++ FILTER (\i. ~MEM i consumed) srcpre) s0 u` by
    metis_tac[inv_ev_ftrace_append] >>
  drule_all inv_lookup_completed_sort >>
  simp[inv_ev_ftrace_append] >> strip_tac >>
  rename1 `inv_ev_ftrace orc p d ctx srcpre s0 sS` >>
  qexists_tac `sS` >> suspend "projection"
QED

Resume inv_lookup_normalized_invoke[projection]:
  `!callee args. setup_callee callee args u = setup_callee callee args sS` by
    metis_tac[inv_ev_invoke_trace_setup] >>
  `EVERY (\z. MEM z bb.bb_instructions /\ ~is_pseudo z.inst_opcode /\
     id_before (MAP (\i. i.inst_id) bb.bb_instructions) obs.inst_id z.inst_id /\
     id_before (MAP (\i. i.inst_id) bb'.bb_instructions) z.inst_id obs.inst_id)
     (FILTER (\i. MEM i consumed) srcpost)` by
    (simp[EVERY_MEM, MEM_FILTER] >> gen_tac >> strip_tac >>
     `MEM z bb.bb_instructions /\ ~is_pseudo z.inst_opcode` by
       (fs[EVERY_MEM] >> metis_tac[MEM_APPEND, MEM]) >>
     asm_rewrite_tac[MAP_APPEND] >>
     simp[dftSsaPreserveTheory.id_before_append,
          dftSsaPreserveTheory.id_before_cons, MEM_MAP] >> metis_tac[]) >>
  `MEM obs bb.bb_instructions /\ ~is_pseudo obs.inst_opcode` by
    (fs[EVERY_MEM] >> metis_tac[MEM_APPEND, MEM]) >>
  drule_all inv_lookup_trailing_trace_frame >> strip_tac >>
  `inv_ev_prefix orc p d ctx bb (LENGTH srcpre) s0 sS` by
    (qspecl_then [`srcpre`, `pseudos`, `s0`, `sS`] mp_tac
       (Q.INST [`b` |-> `obs::srcpost`] inv_ev_ftrace_slice) >>
     simp[APPEND_ASSOC]) >>
  qpat_assum `inv_ev_ftrace _ _ _ _ srcpre s0 sS`
    (mp_tac o MATCH_MP inv_ev_ftrace_idx) >>
  simp[] >> metis_tac[]
QED

Finalise inv_lookup_normalized_invoke

Theorem inv_lookup_scheduled_invoke:
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
  s0.vs_inst_idx = LENGTH pseudos /\ ~s0.vs_call_ctx.cc_static /\
  inv_ev_ftrace orc p d ctx scheduled s0 sT /\ obs.inst_opcode = INVOKE ==>
  ?sS. inv_ev_prefix orc p d ctx bb (LENGTH srcpre) s0 sS /\
    sS.vs_inst_idx = LENGTH pseudos + LENGTH srcpre /\
    (!op. MEM op obs.inst_operands ==> eval_operand op sS = eval_operand op sT) /\
    (!callee args. setup_callee callee args sS = setup_callee callee args sT)
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
  suspend "representatives"
QED

Resume inv_lookup_scheduled_invoke[representatives]:
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
  irule inv_lookup_normalized_invoke >>
  simp[] >> qexists_tac `bb'` >> qexists_tac `originals` >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Finalise inv_lookup_scheduled_invoke

Theorem inv_reachable_active[local]:
  !orc initial C p d fn inst s. ev_reachable orc initial C p d fn inst s ==>
    active_inst fn inst s
Proof
  ho_match_mp_tac ev_reachable_ind >> rpt strip_tac >> simp[]
QED

Theorem inv_source_reachable_invoke:
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  o1_ctx_shape C /\ ctx_labels_bound C initial.vs_labels /\ o1_run_state_ok initial /\
  ev_reachable orc initial C p d fn startinst s0 /\
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  lookup_block s0.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block s0.vs_current_bb fn'.fn_blocks = SOME bb' /\
  bb.bb_instructions = pseudos ++ (srcpre ++ obs::srcpost) /\
  EVERY (\i. is_pseudo i.inst_opcode) pseudos /\
  EVERY (\i. ~is_pseudo i.inst_opcode) (srcpre ++ obs::srcpost) /\
  EVERY inst_shape_ok bb.bb_instructions /\
  bb'.bb_instructions = pseudos ++ (scheduled ++ targetobs::targetpost) /\
  targetobs.inst_id = obs.inst_id /\
  s0.vs_inst_idx = LENGTH pseudos /\ ~s0.vs_call_ctx.cc_static /\
  inv_ev_ftrace orc p d C scheduled s0 sT /\ obs.inst_opcode = INVOKE ==>
  ?sS. ev_reachable orc initial C p d fn obs sS /\
    (!op. MEM op obs.inst_operands ==> eval_operand op sS = eval_operand op sT) /\
    (!callee args. setup_callee callee args sS = setup_callee callee args sT)
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
  `dft_remaining_inv fn bb (srcpre ++ obs::srcpost) s0` by
    (`s0.vs_inst_idx = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions)` by simp[] >>
     drule_all inv_ev_reachable_source_initialized >> simp[]) >>
  drule_all inv_lookup_scheduled_invoke >> strip_tac >>
  qexists_tac `sS` >> simp[] >>
  irule inv_ev_prefix_reachable >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  suspend "fetch"
QED

Resume inv_source_reachable_invoke[fetch]:
  `bb.bb_label = s0.vs_current_bb` by metis_tac[lookup_block_label] >>
  simp[] >> conj_tac
  >- (drule inv_reachable_active >>
      simp[active_inst_def] >> strip_tac >>
      rename1 `MEM activebb fn.fn_blocks` >>
      `wf_function fn` by gvs[dft_fn_rel_def] >>
      `lookup_block s0.vs_current_bb fn.fn_blocks = SOME activebb` by
        (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
      gvs[get_instruction_def]) >>
  simp[get_instruction_def, EL_APPEND_EQN]
QED

Finalise inv_source_reachable_invoke

Theorem inv_invoke_observation_decode:
  ev_reachable orc initial C p d fn obs sS /\
  (!op. MEM op obs.inst_operands ==> eval_operand op sS = eval_operand op sT) /\
  (!callee args. setup_callee callee args sS = setup_callee callee args sT) /\
  decode_invoke obs = SOME (name,argops) /\
  eval_operands argops sT = SOME args /\ setup_callee callee args sT = SOME cs ==>
  ev_reachable orc initial C p d fn obs sS /\
  decode_invoke obs = SOME (name,argops) /\
  eval_operands argops sS = SOME args /\ setup_callee callee args sS = SOME cs
Proof
  strip_tac >> simp[] >>
  `!op. MEM op argops ==> eval_operand op sS = eval_operand op sT` by
    (Cases_on `obs.inst_operands` >> gvs[decode_invoke_def, AllCaseEqs()] >>
     metis_tac[MEM]) >>
  `eval_operands argops sS = eval_operands argops sT` suffices_by simp[] >>
  qpat_x_assum `!op. MEM op argops ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  Induct_on `argops` >> simp[eval_operands_def] >> metis_tac[]
QED
