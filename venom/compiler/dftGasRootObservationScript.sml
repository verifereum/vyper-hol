Theory dftGasRootObservation
Ancestors
  dftGasProvenance dftOrbitObservation dftRootedGasOrbit
  dftPositionalRuntime dftPositionalGasSegment dftPositionalEdit
  dftPositionalRoot dftPositionalPhase dftPositionalPendingGas
  dftPositionalPendingOrbit dftPendingObservation dftOccurrenceMachine
  dftRootedMixedOrbit dftOriginalScheduleRuntime dftPositionalOrientation list

Theorem dft_indexed_gas_root_observation:
  dft_original_context Corig C /\
  D = dft_pos_edit_ctx fi bi pre x y post C /\
  dft_pos_runtime_ready C fi bi pre x y post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  j < LENGTH C.ctx_functions ==>
  dft_orbit_observation w C D
    (dft_occ_init (DftOpen (DftEnter (EL j C.ctx_functions) 0 s) [] n))
    (dft_occ_init (DftOpen (DftEnter (EL j D.ctx_functions) 0 s) [] n)) /\
  dft_orbit_observation w D C
    (dft_occ_init (DftOpen (DftEnter (EL j D.ctx_functions) 0 s) [] n))
    (dft_occ_init (DftOpen (DftEnter (EL j C.ctx_functions) 0 s) [] n))
Proof
  strip_tac >>
  `fi < LENGTH C.ctx_functions /\
   bi < LENGTH (EL fi C.ctx_functions).fn_blocks /\
   (EL bi (EL fi C.ctx_functions).fn_blocks).bb_instructions =
      pre ++ [x;y] ++ post` by fs[dft_pos_runtime_ready_def] >>
  `MEM x (EL bi (EL fi C.ctx_functions).fn_blocks).bb_instructions /\
   MEM y (EL bi (EL fi C.ctx_functions).fn_blocks).bb_instructions` by simp[] >>
  `?u. x.inst_outputs = [u]` by metis_tac[dft_indexed_gas_shape] >>
  `?v. y.inst_outputs = [v]` by metis_tac[dft_indexed_gas_shape] >>
  `!z. MEM z x.inst_outputs ==> ~MEM z y.inst_outputs` by
    metis_tac[dft_indexed_adjacent_outputs_disjoint] >>
  `u <> v` by (gvs[] >> metis_tac[]) >>
  `dft_pos_functions C D (EL j C.ctx_functions) (EL j D.ctx_functions)` by
    (simp[dft_pos_functions_def] >> qexists `j` >> simp[]) >>
  drule_all dft_pos_gas_root_orbit_segments >>
  disch_then (qspecl_then [`w`, `s`, `n`] strip_assume_tac) >>
  metis_tac[dft_gas_orbit_observation_forward, dft_gas_orbit_observation_backward]
QED

Theorem dft_indexed_pending_root:
  dft_original_context Corig C /\ dft_original_context Corig D /\
  j < LENGTH C.ctx_functions /\
  fn_entry_label (EL j C.ctx_functions) = SOME s.vs_current_bb ==>
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post [] []
    (dft_occ_init (DftOpen (DftEnter (EL j C.ctx_functions) 0 s) [] n))
    (dft_occ_init (DftOpen (DftEnter (EL j D.ctx_functions) 0 s) [] n))
Proof
  strip_tac >>
  drule_all (Q.INST [`nL` |-> `n`, `nR` |-> `n`] dft_pos_original_entry_roots) >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  `dft_pos_functions C D (EL j C.ctx_functions) (EL j D.ctx_functions)` by
    (simp[dft_pos_functions_def] >> qexists `j` >> simp[]) >>
  irule dft_pos_pending_aligned_root >> simp[dft_occ_init_def] >>
  fs[dft_pos_phase_def, dft_occ_init_def]
QED


Theorem dft_indexed_pending_root_observation:
  dft_original_context Corig C /\ dft_original_context Corig D /\
  D = dft_pos_edit_ctx fi bi pre gas call post C /\
  dft_pos_runtime_ready C fi bi pre gas call post /\
  gas.inst_opcode = GAS /\ call.inst_opcode = INVOKE /\
  (~dft_must_order gas call \/ ~dft_must_order call gas) /\
  j < LENGTH C.ctx_functions /\
  fn_entry_label (EL j C.ctx_functions) = SOME s.vs_current_bb ==>
  dft_orbit_observation w C D
    (dft_occ_init (DftOpen (DftEnter (EL j C.ctx_functions) 0 s) [] n))
    (dft_occ_init (DftOpen (DftEnter (EL j D.ctx_functions) 0 s) [] n)) /\
  dft_orbit_observation w D C
    (dft_occ_init (DftOpen (DftEnter (EL j D.ctx_functions) 0 s) [] n))
    (dft_occ_init (DftOpen (DftEnter (EL j C.ctx_functions) 0 s) [] n))
Proof
  strip_tac >>
  `fi < LENGTH C.ctx_functions /\
   bi < LENGTH (EL fi C.ctx_functions).fn_blocks /\
   (EL bi (EL fi C.ctx_functions).fn_blocks).bb_instructions =
      pre ++ [gas;call] ++ post` by fs[dft_pos_runtime_ready_def] >>
  `MEM gas (EL bi (EL fi C.ctx_functions).fn_blocks).bb_instructions` by simp[] >>
  `?v. gas.inst_outputs = [v]` by metis_tac[dft_indexed_gas_shape] >>
  `~is_pseudo gas.inst_opcode` by simp[venomInstTheory.is_pseudo_def] >>
  `fi < LENGTH D.ctx_functions /\
   bi < LENGTH (EL fi D.ctx_functions).fn_blocks /\
   (EL bi (EL fi D.ctx_functions).fn_blocks).bb_instructions =
      pre ++ [call;gas] ++ post` by
    gvs[dft_pos_edit_ctx_def, dft_pos_edit_fn_def, dft_pos_replace_el] >>
  `~is_pseudo call.inst_opcode` by simp[venomInstTheory.is_pseudo_def] >>
  `~MEM (Var v) call.inst_operands` by
    metis_tac[dft_indexed_adjacent_forward_nonuse,
      dft_indexed_adjacent_backward_nonuse, MEM] >>
  `~MEM v call.inst_outputs` by
    metis_tac[dft_indexed_adjacent_outputs_disjoint, MEM] >>
  `dft_pos_pending_aligned_phase w C D fi bi pre gas call post []
    ([] : (instruction # (num # num) list) list)
    (dft_occ_init (DftOpen (DftEnter (EL j C.ctx_functions) 0 s) [] n))
    (dft_occ_init (DftOpen (DftEnter (EL j D.ctx_functions) 0 s) [] n))` by
    (irule dft_indexed_pending_root >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac
    `dft_pos_pending_aligned_phase w C D fi bi pre gas call post [] [] l r` >>
  qspecl_then [`l`, `r`] mp_tac
    (Q.GENL [`l`, `r`] (Q.INST [`Dorig` |-> `Corig`, `zs` |-> `[]`, `H` |-> `[]`]
      dftPositionalPendingOrbitTheory.dft_pending_cofinal_segments_retired)) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  qpat_x_assum `D = _` SUBST_ALL_TAC >>
  (conj_tac
   >- (irule dft_pending_observation_forward >>
       goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
   irule dft_pending_observation_backward >>
   goal_assum (drule_at Any) >> simp[] >>
   qexistsl_tac [`bi`, `call`, `fi`, `gas`, `post`, `pre`] >> simp[])
QED

Theorem dft_indexed_mixed_root_observation:
  dft_original_context Corig C /\ dft_original_context Corig D /\
  D = dft_pos_edit_ctx fi bi pre gas inst post C /\
  dft_pos_runtime_ready C fi bi pre gas inst post /\
  gas.inst_opcode = GAS /\ inst.inst_opcode <> GAS /\
  inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
  ~is_pseudo inst.inst_opcode /\
  (~dft_must_order gas inst \/ ~dft_must_order inst gas) /\
  ctx_labels_bound Corig s.vs_labels /\ o1_ctx_shape Corig /\
  (!fn i. MEM fn Corig.ctx_functions /\ MEM i (fn_insts fn) ==> inst_wf i) /\
  (!fn i. MEM fn Corig.ctx_functions /\ MEM i (fn_insts fn) ==> i.inst_opcode <> ALLOCA) /\
  j < LENGTH C.ctx_functions /\
  fn_entry_label (EL j C.ctx_functions) = SOME s.vs_current_bb ==>
  dft_orbit_observation w C D
    (dft_occ_init (DftOpen (DftEnter (EL j C.ctx_functions) 0 s) [] n))
    (dft_occ_init (DftOpen (DftEnter (EL j D.ctx_functions) 0 s) [] n)) /\
  dft_orbit_observation w D C
    (dft_occ_init (DftOpen (DftEnter (EL j D.ctx_functions) 0 s) [] n))
    (dft_occ_init (DftOpen (DftEnter (EL j C.ctx_functions) 0 s) [] n))
Proof
  strip_tac >>
  `fi < LENGTH C.ctx_functions /\
   bi < LENGTH (EL fi C.ctx_functions).fn_blocks /\
   (EL bi (EL fi C.ctx_functions).fn_blocks).bb_instructions =
      pre ++ [gas;inst] ++ post` by fs[dft_pos_runtime_ready_def] >>
  `MEM gas (EL bi (EL fi C.ctx_functions).fn_blocks).bb_instructions` by simp[] >>
  `?v. gas.inst_outputs = [v]` by metis_tac[dft_indexed_gas_shape] >>
  `~is_pseudo gas.inst_opcode` by simp[venomInstTheory.is_pseudo_def] >>
  `~MEM v inst.inst_outputs` by
    metis_tac[dft_indexed_adjacent_outputs_disjoint, MEM] >>
  `dft_pos_functions C D (EL j C.ctx_functions) (EL j D.ctx_functions)` by
    (simp[dft_pos_functions_def] >> qexists `j` >> simp[]) >>
  `dft_original_function (EL j Corig.ctx_functions) (EL j C.ctx_functions) /\
   dft_original_function (EL j Corig.ctx_functions) (EL j D.ctx_functions)` by
    (fs[dft_original_context_def, LIST_REL_EL_EQN] >> metis_tac[]) >>
  `fn_entry_label (EL j D.ctx_functions) = SOME s.vs_current_bb` by
    metis_tac[dft_original_function_entry] >>
  `LENGTH D.ctx_functions = LENGTH C.ctx_functions` by
    gvs[dft_pos_edit_ctx_def] >>
  `fi < LENGTH D.ctx_functions /\
   bi < LENGTH (EL fi D.ctx_functions).fn_blocks /\
   (EL bi (EL fi D.ctx_functions).fn_blocks).bb_instructions =
      pre ++ [inst;gas] ++ post` by
    (gvs[dft_pos_edit_ctx_selected, dft_pos_edit_fn_def, dft_pos_replace_el]) >>
  `~MEM (Var v) inst.inst_operands` by
    metis_tac[dft_indexed_adjacent_forward_nonuse,
      dft_indexed_adjacent_backward_nonuse, MEM] >>
  `?A B. dft_pos_mixed_orbit_cuts C D w fi bi pre gas inst
    (dft_occ_init (DftOpen (DftEnter (EL j C.ctx_functions) 0 s) [] n))
    (dft_occ_init (DftOpen (DftEnter (EL j D.ctx_functions) 0 s) [] n)) A B` by
    (irule dft_pos_rooted_mixed_orbit_segments >>
     simp[dft_pos_gas_phase_root] >>
     qexistsl_tac [`Corig`, `0`, `n`, `EL j D.ctx_functions`, `s`] >>
     qpat_x_assum `D = _` (SUBST_ALL_TAC o SYM) >> simp[EL_MEM] >>
     metis_tac[]) >>
  metis_tac[dft_mixed_orbit_observation_forward, dft_mixed_orbit_observation_backward]
QED

Theorem dft_indexed_original_entry_pair[local]:
  dft_original_context Corig C /\ dft_original_context Corig D /\
  j < LENGTH C.ctx_functions /\
  fn_entry_label (EL j C.ctx_functions) = SOME s.vs_current_bb ==>
  j < LENGTH D.ctx_functions /\
  fn_entry_label (EL j D.ctx_functions) = SOME s.vs_current_bb
Proof
  strip_tac >>
  `dft_original_function (EL j Corig.ctx_functions) (EL j C.ctx_functions) /\
   dft_original_function (EL j Corig.ctx_functions) (EL j D.ctx_functions)` by
    (fs[dft_original_context_def, LIST_REL_EL_EQN] >> metis_tac[]) >>
  conj_tac >- fs[dft_original_context_def, LIST_REL_EL_EQN] >>
  metis_tac[dft_original_function_entry]
QED

Theorem dft_indexed_reverse_pending_root_observation:
  dft_original_context Corig C /\ dft_original_context Corig D /\
  D = dft_pos_edit_ctx fi bi pre call gas post C /\
  dft_pos_runtime_ready C fi bi pre call gas post /\
  gas.inst_opcode = GAS /\ call.inst_opcode = INVOKE /\
  ~dft_must_order call gas /\ j < LENGTH C.ctx_functions /\
  fn_entry_label (EL j C.ctx_functions) = SOME s.vs_current_bb ==>
  dft_orbit_observation w C D
    (dft_occ_init (DftOpen (DftEnter (EL j C.ctx_functions) 0 s) [] n))
    (dft_occ_init (DftOpen (DftEnter (EL j D.ctx_functions) 0 s) [] n)) /\
  dft_orbit_observation w D C
    (dft_occ_init (DftOpen (DftEnter (EL j D.ctx_functions) 0 s) [] n))
    (dft_occ_init (DftOpen (DftEnter (EL j C.ctx_functions) 0 s) [] n))
Proof
  strip_tac >>
  drule_all dft_indexed_original_entry_pair >> strip_tac >>
  drule_all dft_pos_runtime_ready_reverse >> strip_tac >>
  drule_all dft_pos_edit_ctx_reverse >> strip_tac >>
  once_rewrite_tac[CONJ_COMM] >>
  irule dft_indexed_pending_root_observation >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `D = _` kall_tac >> simp[] >> metis_tac[]
QED

Theorem dft_indexed_reverse_mixed_root_observation:
  dft_original_context Corig C /\ dft_original_context Corig D /\
  D = dft_pos_edit_ctx fi bi pre inst gas post C /\
  dft_pos_runtime_ready C fi bi pre inst gas post /\
  gas.inst_opcode = GAS /\ inst.inst_opcode <> GAS /\
  inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
  ~is_pseudo inst.inst_opcode /\ ~dft_must_order inst gas /\
  ctx_labels_bound Corig s.vs_labels /\ o1_ctx_shape Corig /\
  (!fn i. MEM fn Corig.ctx_functions /\ MEM i (fn_insts fn) ==> inst_wf i) /\
  (!fn i. MEM fn Corig.ctx_functions /\ MEM i (fn_insts fn) ==> i.inst_opcode <> ALLOCA) /\
  j < LENGTH C.ctx_functions /\
  fn_entry_label (EL j C.ctx_functions) = SOME s.vs_current_bb ==>
  dft_orbit_observation w C D
    (dft_occ_init (DftOpen (DftEnter (EL j C.ctx_functions) 0 s) [] n))
    (dft_occ_init (DftOpen (DftEnter (EL j D.ctx_functions) 0 s) [] n)) /\
  dft_orbit_observation w D C
    (dft_occ_init (DftOpen (DftEnter (EL j D.ctx_functions) 0 s) [] n))
    (dft_occ_init (DftOpen (DftEnter (EL j C.ctx_functions) 0 s) [] n))
Proof
  strip_tac >>
  drule_all dft_indexed_original_entry_pair >> strip_tac >>
  drule_all dft_pos_runtime_ready_reverse >> strip_tac >>
  drule_all dft_pos_edit_ctx_reverse >> strip_tac >>
  once_rewrite_tac[CONJ_COMM] >>
  irule dft_indexed_mixed_root_observation >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `D = _` kall_tac >> simp[] >> metis_tac[]
QED
