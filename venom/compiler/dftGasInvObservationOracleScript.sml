Theory dftGasInvObservationOracle
Ancestors
  dftGasInvExtraction
  dftGasInvInversion dftGasInvFlexibleTrace dftGasInvResidualTrace
  dftGasInvSSAProbe dftGasInvOracleFrame dftGasOracleDefs
  dftRunRel dftScheduleOrder dftCorrectness dftAvailability dftBlockSim dftStructural
  venomExecSemantics venomInst venomState list rich_list pred_set sorting
  dftSsaPreserve dftPermSim venomWf dftWf

(* A crossing instruction at a memory observation cannot consume an oracle
   outcome. Calls and invokes write memory, including computed precompiles. *)
Theorem inv_memory_write_at_request[local]:
  (x.inst_opcode = INVOKE \/ is_ext_call_op x.inst_opcode) ==>
  Eff_MEMORY IN write_effects x.inst_opcode
Proof
  Cases_on `x.inst_opcode` >>
  simp[is_ext_call_op_def, venomEffectsTheory.write_effects_def,
       venomEffectsTheory.all_effects_def]
QED

Theorem inv_request_not_before_memory[local]:
  (Eff_MEMORY IN read_effects y.inst_opcode \/ Eff_MEMORY IN write_effects y.inst_opcode) /\
  ~dft_must_order x y ==>
  x.inst_opcode <> INVOKE /\ ~is_ext_call_op x.inst_opcode
Proof
  simp[dft_must_order_def, IN_DISJOINT] >>
  metis_tac[inv_memory_write_at_request, IN_UNION]
QED

Theorem inv_request_not_after_memory[local]:
  (Eff_MEMORY IN read_effects x.inst_opcode \/ Eff_MEMORY IN write_effects x.inst_opcode) /\
  ~dft_must_order x y ==>
  y.inst_opcode <> INVOKE /\ ~is_ext_call_op y.inst_opcode
Proof
  simp[dft_must_order_def, IN_DISJOINT] >>
  metis_tac[inv_memory_write_at_request, IN_UNION]
QED

Theorem inv_ev_ftrace_oracle[local]:
  !xs s t.
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_ext_call_op i.inst_opcode) xs /\
  inv_ev_ftrace orc p d ctx xs s t ==>
  t.vs_outcomes = s.vs_outcomes /\ t.vs_requests = s.vs_requests
Proof
  Induct >> simp[inv_ev_ftrace_def] >> rpt strip_tac >>
  `u.vs_outcomes = s.vs_outcomes /\ u.vs_requests = s.vs_requests` by
    (Cases_on `h.inst_opcode = GAS`
     >- gvs[ev_step_def, ev_gas_def, update_var_def, AllCaseEqs()] >>
     `step_inst fuel ctx h s = OK u` by gvs[ev_step_def, step_inst_def] >>
     `h.inst_opcode <> CALL /\ h.inst_opcode <> STATICCALL /\
      h.inst_opcode <> DELEGATECALL /\ h.inst_opcode <> CREATE /\
      h.inst_opcode <> CREATE2` by
       (Cases_on `h.inst_opcode` >> fs[is_ext_call_op_def]) >>
     drule_all oracleExecPropsTheory.step_inst_noninvoke_oracle >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED

(* The completed and sorted traces differ at the observation only by
   instructions that commute across it. Neither extra trace consumes an
   outcome or appends a request. *)
Theorem inv_completed_observation_oracle:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' /\
  bb.bb_instructions = pseudos ++ (srcpre ++ obs::srcpost) /\
  EVERY (\i. ~is_pseudo i.inst_opcode) (srcpre ++ obs::srcpost) /\
  MAP (\i. i.inst_id) bb'.bb_instructions =
    MAP (\i. i.inst_id) pseudos ++ MAP (\i. i.inst_id) (consumed ++ obs::later) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb'.bb_instructions) /\
  inv_memory_observation obs.inst_opcode /\
  EVERY (\i. inst_shape_ok i /\ ~is_terminator i.inst_opcode /\ ~dft_must_order i obs)
    (FILTER (\i. ~MEM i consumed) srcpre) /\
  s0.vs_inst_idx = LENGTH pseudos /\
  inv_ev_trace orc p d 0 ctx (FILTER (\i. ~MEM i consumed) srcpre) sT u /\
  (!op. MEM op obs.inst_operands ==> eval_operand op u = eval_operand op sT) /\
  inv_ev_ftrace orc p d ctx srcpre s0 sS /\
  inv_ev_ftrace orc p d ctx (FILTER (\i. MEM i consumed) srcpost) sS u ==>
  inv_ev_prefix orc p d ctx bb (LENGTH srcpre) s0 sS /\
  sS.vs_inst_idx = LENGTH pseudos + LENGTH srcpre /\
  (!op. MEM op obs.inst_operands ==> eval_operand op sS = eval_operand op sT) /\
  sS.vs_initial_fmp = sT.vs_initial_fmp /\
  sS.vs_outcomes = sT.vs_outcomes /\ sS.vs_requests = sT.vs_requests
Proof
  strip_tac >>
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
    (qspecl_then [`srcpre`, `pseudos`, `s0`, `sS`] mp_tac (Q.INST [`b` |-> `obs::srcpost`] inv_ev_ftrace_slice) >>
     simp[APPEND_ASSOC]) >>
  `sS.vs_inst_idx = LENGTH pseudos + LENGTH srcpre /\
   (!op. MEM op obs.inst_operands ==> eval_operand op sS = eval_operand op sT) /\
   sS.vs_initial_fmp = sT.vs_initial_fmp` by
    (qpat_assum `inv_ev_ftrace _ _ _ _ srcpre s0 sS`
        (mp_tac o MATCH_MP inv_ev_ftrace_idx) >> simp[] >>
      metis_tac[inv_ev_ftrace_initial_fmp, inv_ev_trace_ftrace]) >>
  qpat_assum `inv_memory_observation obs.inst_opcode`
    (assume_tac o MATCH_MP dftGasInvCrossingProbeTheory.inv_memory_observation_touches_memory) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_ext_call_op i.inst_opcode)
    (FILTER (\i. ~MEM i consumed) srcpre)` by
    (fs[EVERY_MEM] >> metis_tac[inv_request_not_before_memory]) >>
  `u.vs_outcomes = sT.vs_outcomes /\ u.vs_requests = sT.vs_requests` by
    metis_tac[inv_ev_trace_ftrace, inv_ev_ftrace_oracle] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_ext_call_op i.inst_opcode)
    (FILTER (\i. MEM i consumed) srcpost)` by
    (drule_all dft_fn_rel_lookup_order >> strip_tac >>
     simp[EVERY_MEM, MEM_FILTER] >> gen_tac >> strip_tac >>
     qpat_x_assum `EVERY _ (FILTER (\i. MEM i consumed) srcpost)`
       (mp_tac o Q.SPEC `i` o REWRITE_RULE [EVERY_MEM]) >> simp[MEM_FILTER] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     `~dft_must_order obs i` by
       (irule dft_inversion_not_must_order >> simp[] >>
        qexistsl_tac [`bb`, `bb'`] >> simp[]) >>
     drule_all inv_request_not_after_memory >> simp[]) >>
  `u.vs_outcomes = sS.vs_outcomes /\ u.vs_requests = sS.vs_requests` by
    metis_tac[inv_ev_ftrace_oracle] >>
  metis_tac[]
QED

Theorem inv_lookup_normalized_observation_oracle:
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
  inv_ev_ftrace orc p d ctx consumed s0 sT /\
  inv_memory_observation obs.inst_opcode ==>
  ?sS. inv_ev_prefix orc p d ctx bb (LENGTH srcpre) s0 sS /\
    sS.vs_inst_idx = LENGTH pseudos + LENGTH srcpre /\
    (!op. MEM op obs.inst_operands ==> eval_operand op sS = eval_operand op sT) /\
    sS.vs_initial_fmp = sT.vs_initial_fmp /\
    sS.vs_outcomes = sT.vs_outcomes /\ sS.vs_requests = sT.vs_requests
Proof
  strip_tac >>
  `ALL_DISTINCT (consumed ++ obs::later)` by metis_tac[ALL_DISTINCT_PERM] >>
  `ALL_DISTINCT consumed /\ ~MEM obs consumed` by
    (fs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `EVERY (\i. MEM i (srcpre ++ obs::srcpost)) consumed` by
    (simp[EVERY_MEM] >> gen_tac >> strip_tac >>
     drule PERM_MEM_EQ >> disch_then (qspec_then `i` mp_tac) >> simp[]) >>
  `wf_function fn /\ wf_ssa fn` by metis_tac[dft_fn_rel_def] >>
  drule_all inv_lookup_block_contract >> strip_tac >>
  drule_all inv_lookup_missing_predecessors >> strip_tac >>
  `~sT.vs_call_ctx.cc_static` by metis_tac[inv_ftrace_call_ctx] >>
  `dft_remaining_inv fn bb
      (FILTER (\i. ~MEM i consumed) srcpre ++
       obs::FILTER (\i. ~MEM i consumed) srcpost) sT` by
    (drule_all inv_ftrace_remaining >> simp[FILTER_APPEND_DISTRIB]) >>
  `?u. inv_ev_trace orc p d 0 ctx (FILTER (\i. ~MEM i consumed) srcpre) sT u /\
       (!op. MEM op obs.inst_operands ==> eval_operand op u = eval_operand op sT)` by
    (drule_all inv_remaining_trace_extension >> metis_tac[]) >>
  `inv_ev_ftrace orc p d ctx
     (consumed ++ FILTER (\i. ~MEM i consumed) srcpre) s0 u` by
    metis_tac[inv_ev_trace_ftrace, inv_ev_ftrace_append] >>
  drule_all inv_lookup_completed_sort >>
  simp[inv_ev_ftrace_append] >> strip_tac >>
  rename1 `inv_ev_ftrace orc p d ctx srcpre s0 sS` >>
  qexists_tac `sS` >> drule_all inv_completed_observation_oracle >> simp[]
QED

Theorem inv_lookup_scheduled_observation_oracle:
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
  inv_ev_ftrace orc p d ctx scheduled s0 sT /\
  inv_memory_observation obs.inst_opcode ==>
  ?sS. inv_ev_prefix orc p d ctx bb (LENGTH srcpre) s0 sS /\
    sS.vs_inst_idx = LENGTH pseudos + LENGTH srcpre /\
    (!op. MEM op obs.inst_operands ==> eval_operand op sS = eval_operand op sT) /\
    sS.vs_initial_fmp = sT.vs_initial_fmp /\
    sS.vs_outcomes = sT.vs_outcomes /\ sS.vs_requests = sT.vs_requests
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
  irule inv_lookup_normalized_observation_oracle >>
  simp[] >> qexists_tac `bb'` >> qexists_tac `originals` >>
  goal_assum (drule_at Any) >> simp[MAP_APPEND] >>
  metis_tac[]
QED
