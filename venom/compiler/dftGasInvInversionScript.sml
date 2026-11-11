Theory dftGasInvInversion
Ancestors
  dftGasInvContractBoundary dftGasInvFlexibleTrace dftGasInvResidualTrace
  dftRunRel dftScheduleOrder dftBlockSim dftStructural dftCorrectness venomWf
  dftWf sorting
  dftGasInvSSAProbe dftGasInvCallPartner dftGasOracleDefs ctxLookupAgreeHelpers
  venomExecSemantics venomInstProofs1
  venomInst venomState venomEffects list pred_set

Theorem inv_lookup_block_contract:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' ==>
  EVERY inst_wf bb.bb_instructions /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb'.bb_instructions)
Proof
  strip_tac >>
  conj_tac
  >- (gvs[dft_fn_rel_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[dft_fn_rel_def, wf_fn_block_inst_ids_distinct] >>
  drule_all dft_fn_rel_lookup_order >> strip_tac >>
  qpat_x_assum `dft_block_rel _ _` mp_tac >>
  simp[dft_block_rel_def] >> strip_tac >> gvs[] >>
  rename1 `EVERY (from_block bb.bb_instructions) scheduled` >>
  `ALL_DISTINCT (MAP (\i. i.inst_id)
      (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions)) /\
   ALL_DISTINCT (MAP (\i. i.inst_id)
      (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions))` by
    (conj_tac >> irule all_distinct_map_filter >> simp[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) scheduled)` by metis_tac[ALL_DISTINCT_PERM] >>
  simp[MAP_APPEND, ALL_DISTINCT_APPEND] >> rpt strip_tac >>
  `MEM e (MAP (\i. i.inst_id)
      (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions))` by
    metis_tac[PERM_MEM_EQ] >>
  gvs[MEM_MAP, MEM_FILTER] >> metis_tac[all_distinct_map_mem_inj]
QED

Theorem inv_lookup_inversion_swap:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' /\
  MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
  ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
  id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id /\
  id_before (MAP (\i. i.inst_id) bb'.bb_instructions) y.inst_id x.inst_id ==>
  dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  ~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
    write_effects x.inst_opcode = empty_effects)
Proof
  strip_tac >> drule_all inv_lookup_block_contract >> strip_tac >>
  drule_all dft_fn_rel_lookup_order >> strip_tac >>
  `~dft_must_order x y` by metis_tac[dft_inversion_not_must_order] >>
  `dft_abort_compatible x.inst_opcode y.inst_opcode` by
    metis_tac[dft_inversion_compatible] >>
  drule_all inv_dft_fn_rel_block_no_alloca >> strip_tac >>
  irule dft_crossing_swap_pair >> gvs[dft_fn_rel_def] >> metis_tac[]
QED

Theorem inv_ev_step_initial_fmp:
  ev_step orc p d fuel ctx i s = OK t ==>
  t.vs_initial_fmp = s.vs_initial_fmp
Proof
  Cases_on `i.inst_opcode = INVOKE`
  >- (simp[ev_step_def] >> strip_tac >> gvs[AllCaseEqs()] >>
      drule bind_outputs_initial_fmp >> simp[]) >>
  Cases_on `i.inst_opcode = GAS`
  >- (simp[ev_step_def, ev_gas_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
  simp[ev_step_def] >> metis_tac[step_inst_base_initial_fmp]
QED

Theorem inv_ev_swap_operand_frame:
  dft_gas_swap_pair y z /\ inst_wf z /\
  ev_step orc p d fuel ctx z s = OK t ==>
  !op. MEM op y.inst_operands ==>
    eval_operand op (t with vs_inst_idx := SUC s.vs_inst_idx) = eval_operand op s
Proof
  strip_tac >>
  `~is_terminator z.inst_opcode /\ z.inst_opcode <> PHI` by
    (gvs[dft_gas_swap_pair_def] >> Cases_on `z.inst_opcode` >>
     gvs[is_pseudo_def]) >>
  drule_all inv_ev_step_availability >> strip_tac >>
  Cases >> simp[eval_operand_def] >> strip_tac
  >- (rename1 `MEM (Var v) y.inst_operands` >>
      `~MEM v z.inst_outputs` by
        (gvs[dft_gas_swap_pair_def, inst_defs_def, inst_uses_def,
             DISJOINT_DEF, EXTENSION] >> metis_tac[mem_var_operand_vars]) >>
      `lookup_var v t = lookup_var v s` by
        (Cases_on `z.inst_opcode = INVOKE`
         >- (irule inv_ev_call_lookup_outside >> metis_tac[]) >>
         irule inv_ev_noninvoke_nonoutput >> metis_tac[]) >>
      fs[lookup_var_def]) >> simp[]
QED

Theorem inv_ev_trailing_trace_frame:
  !zs s t. EVERY (\z. dft_gas_swap_pair y z /\ inst_wf z) zs /\
  inv_ev_ftrace orc p d ctx zs s t ==>
  (!op. MEM op y.inst_operands ==> eval_operand op t = eval_operand op s) /\
  t.vs_initial_fmp = s.vs_initial_fmp
Proof
  Induct >> simp[inv_ev_ftrace_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  gvs[] >> metis_tac[inv_ev_swap_operand_frame, inv_ev_step_initial_fmp]
QED

Theorem inv_from_block_unique_source:
  ALL_DISTINCT (MAP (\j. j.inst_id) bi) /\ from_block bi i ==>
  ?!j. MEM j bi /\ j.inst_id = i.inst_id /\ ~is_pseudo j.inst_opcode /\
       (i = j \/ (i = flip_operands j /\ is_flippable j.inst_opcode))
Proof
  strip_tac >> rw[EXISTS_UNIQUE_THM]
  >- (gvs[from_block_def] >> metis_tac[flip_operands_inst_id]) >>
  metis_tac[all_distinct_map_mem_inj, flip_operands_inst_id]
QED

Theorem inv_lookup_trailing_trace_frame:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' /\
  MEM y bb.bb_instructions /\ ~is_pseudo y.inst_opcode /\
  EVERY (\z. MEM z bb.bb_instructions /\ ~is_pseudo z.inst_opcode /\
    id_before (MAP (\i. i.inst_id) bb.bb_instructions) y.inst_id z.inst_id /\
    id_before (MAP (\i. i.inst_id) bb'.bb_instructions) z.inst_id y.inst_id) zs /\
  inv_ev_ftrace orc p d ctx zs s t ==>
  (!op. MEM op y.inst_operands ==> eval_operand op t = eval_operand op s) /\
  t.vs_initial_fmp = s.vs_initial_fmp
Proof
  strip_tac >> irule inv_ev_trailing_trace_frame >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `EVERY _ zs` mp_tac >> simp[EVERY_MEM] >>
  metis_tac[inv_lookup_inversion_swap]
QED
