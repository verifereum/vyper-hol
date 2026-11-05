Theory dftOrdinaryRootObservation
Ancestors
  dftOrdinaryObservation dftGasProvenance dftEdgeReadiness
  dftPositionalLifecycle dftPositionalRootedOrbit dftPositionalProvenance
  dftPositionalSchedule dftOriginalScheduleRuntime dftPositionalRoot
  dftPositionalRuntime dftProtectedRuntime o1PassContract venomInst list arithmetic

Theorem dft_pos_rooted_phase_initial:
  dft_pos_phase C D fi bi pre x call post l r ==>
  dft_pos_rooted_phase w C D fi bi pre x call post l r l r
Proof
  simp[dft_pos_rooted_phase_def] >> strip_tac >>
  conj_tac >> qexists `0` >> simp[]
QED

Theorem dft_indexed_ordinary_root_phase:
  dft_original_context Corig C /\ dft_original_context Corig D /\
  j < LENGTH C.ctx_functions /\
  fn_entry_label (EL j C.ctx_functions) = SOME s.vs_current_bb ==>
  dft_pos_rooted_phase w C D fi bi pre x call post
    (dft_occ_init (DftOpen (DftEnter (EL j C.ctx_functions) 0 s) [] n))
    (dft_occ_init (DftOpen (DftEnter (EL j D.ctx_functions) 0 s) [] n))
    (dft_occ_init (DftOpen (DftEnter (EL j C.ctx_functions) 0 s) [] n))
    (dft_occ_init (DftOpen (DftEnter (EL j D.ctx_functions) 0 s) [] n))
Proof
  strip_tac >> irule dft_pos_rooted_phase_initial >>
  metis_tac[dft_pos_original_entry_roots]
QED

Theorem dft_indexed_ordinary_call_root_observation:
  dft_original_context Corig C /\ dft_original_context Corig D /\
  D = dft_pos_edit_ctx fi bi pre x call post C /\
  dft_pos_runtime_ready C fi bi pre x call post /\
  dft_pos_provenance_guard Corig Cdest fi bi pre x call post /\
  ~dft_must_order x call /\ call.inst_opcode = INVOKE /\
  x.inst_opcode <> GAS /\ x.inst_opcode <> INVOKE /\
  ctx_labels_bound Corig s.vs_labels /\
  (!fn i. MEM fn Corig.ctx_functions /\ MEM i (fn_insts fn) ==> i.inst_opcode <> ALLOCA) /\
  j < LENGTH C.ctx_functions /\
  fn_entry_label (EL j C.ctx_functions) = SOME s.vs_current_bb ==>
  dft_orbit_observation w C D
    (dft_occ_init (DftOpen (DftEnter (EL j C.ctx_functions) 0 s) [] n))
    (dft_occ_init (DftOpen (DftEnter (EL j D.ctx_functions) 0 s) [] n))
Proof
  strip_tac >>
  `~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode` by
    fs[dft_pos_provenance_guard_def, dft_pos_schedule_guard_def] >>
  `fi < LENGTH C.ctx_functions /\
   bi < LENGTH (EL fi C.ctx_functions).fn_blocks /\
   (EL bi (EL fi C.ctx_functions).fn_blocks).bb_instructions =
     pre ++ [x;call] ++ post` by fs[dft_pos_runtime_ready_def] >>
  `dft_original_block (EL fi Corig.ctx_functions)
    (EL bi (EL fi Corig.ctx_functions).fn_blocks)
    (EL bi (EL fi C.ctx_functions).fn_blocks)` by
    metis_tac[dft_original_indexed_block] >>
  `x.inst_opcode <> ALLOCA` by
    (`MEM x (EL bi (EL fi Corig.ctx_functions).fn_blocks).bb_instructions` by
       (drule dft_original_block_mem >> simp[] >> metis_tac[]) >>
     `MEM (EL bi (EL fi Corig.ctx_functions).fn_blocks)
       (EL fi Corig.ctx_functions).fn_blocks` by
       metis_tac[dft_original_block_def, dft_original_schedule_def] >>
     `MEM x (fn_insts (EL fi Corig.ctx_functions))` by
       (simp[fn_insts_def, fn_insts_blocks_MEM] >> goal_assum (drule_at Any) >> simp[]) >>
     `LENGTH C.ctx_functions = LENGTH Corig.ctx_functions` by
       metis_tac[dft_original_context_def, LIST_REL_LENGTH] >>
     `MEM (EL fi Corig.ctx_functions) Corig.ctx_functions` by simp[EL_MEM] >>
     first_x_assum drule_all >> simp[]) >>
  `?A B. dft_pos_rooted_orbit_cuts w C D fi bi pre x call post
    (dft_occ_init (DftOpen (DftEnter (EL j C.ctx_functions) 0 s) [] n))
    (dft_occ_init (DftOpen (DftEnter (EL j D.ctx_functions) 0 s) [] n)) A B` by
    (irule dft_pos_rooted_orbit_segments >>
     simp[dft_indexed_ordinary_root_phase] >>
     conj_tac
     >- (qexistsl_tac [`Corig`, `n`, `EL j C.ctx_functions`, `s`] >> simp[EL_MEM]) >>
     conj_tac >- metis_tac[] >>
     irule dft_indexed_ordinary_root_phase >> metis_tac[]) >>
  metis_tac[dft_ordinary_orbit_observation_forward]
QED
