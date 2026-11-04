Theory dftPositionalStep
Ancestors
  dftPositionalReturn dftPositionalPhase dftPositionalRuntime
  dftRecursiveFixedStep dftOccurrenceReplay dftOccurrenceMachine
  dftOpenMachine dftOpenErase dftOriginalRuntime
  venomExecSemantics venomState venomInst list arithmetic

Theorem dft_pos_blocks_slot:
  dft_pos_blocks C D f g b b' ==> ?j k. dft_pos_slot C D j k f g b b'
Proof simp[dft_pos_blocks_def, dft_pos_slot_def]
QED

Theorem dft_pos_entry_not_interior[local]:
  dft_pos_runtime_ready C fi bi pre x call post /\
  dft_pos_slot C D j k f g b b' ==>
  ~(j = fi /\ k = bi /\ phi_prefix_length b.bb_instructions = SUC (LENGTH pre))
Proof
  strip_tac >> Cases_on `j = fi /\ k = bi` >> gvs[] >>
  fs[dft_pos_runtime_ready_def, dft_pos_slot_def] >> gvs[] >>
  `phi_prefix_length (pre ++ [x;call] ++ post) <= LENGTH pre` by
    (irule dft_fixed_phi_bound >> simp[]) >> decide_tac
QED

Theorem dft_pos_enter_next:
  D = dft_pos_edit_ctx fi bi pre x call post C /\
  dft_pos_runtime_ready C fi bi pre x call post /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_pos_phase C D fi bi pre x call post l r /\
  l.dft_occ_core = DftOpen (DftEnter f 0 s) ls nL /\
  r.dft_occ_core = DftOpen (DftEnter g 0 s) rs nR ==>
  dft_pos_phase C D fi bi pre x call post
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w D r)
Proof
  strip_tac >>
  `dft_original_ready (dft_occ_oracle_next w C l) /\
   dft_original_ready (dft_occ_oracle_next w D r)` by
    (fs[dft_pos_phase_def] >> metis_tac[dft_original_runtime_next]) >>
  `dft_pos_functions C D f g /\
   ?certs. dft_pos_stack C D fi bi pre x call post certs ls rs /\
    LENGTH l.dft_occ_saved = LENGTH certs` by
    (fs[dft_pos_phase_def, dft_pos_control_def] >> metis_tac[]) >>
  drule dft_pos_stack_fill >> strip_tac >>
  drule_all dft_pos_stack_saved_empty >> strip_tac >>
  `OPTREL (dft_pos_blocks C D f g)
    (lookup_block s.vs_current_bb f.fn_blocks) (lookup_block s.vs_current_bb g.fn_blocks)` by
    metis_tac[dft_pos_edit_block_lookup] >>
  Cases_on `lookup_block s.vs_current_bb f.fn_blocks`
  >- suspend "missing" >>
  rename1 `lookup_block s.vs_current_bb f.fn_blocks = SOME bb` >>
  fs[optionTheory.OPTREL_def] >>
  rename1 `lookup_block s.vs_current_bb g.fn_blocks = SOME bb'` >>
  `eval_phis s bb.bb_instructions = eval_phis s bb'.bb_instructions /\
   phi_prefix_length bb.bb_instructions = phi_prefix_length bb'.bb_instructions` by
    (fs[dft_pos_runtime_ready_def] >> metis_tac[dft_pos_edit_block_phis]) >>
  drule dft_pos_blocks_slot >> strip_tac >>
  drule_all dft_pos_entry_not_interior >> strip_tac >>
  suspend "found"
QED

Resume dft_pos_enter_next[missing]:
  fs[optionTheory.OPTREL_def] >>
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_erase_def, dft_occ_update_def] >>
  simp[dft_pos_phase_def, dft_pos_control_def, dft_pos_stack_def] >>
  fs[dft_pos_phase_def] >> metis_tac[]
QED
Resume dft_pos_enter_next[found]:
  `!fr. dft_fill_frame 0 (dft_fill_frame 1 fr) = dft_fill_frame 0 fr` by
    (Cases >> simp[dft_fill_frame_def]) >>
  Cases_on `eval_phis s bb'.bb_instructions` >>
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_erase_def, MAP_MAP_o, combinTheory.o_DEF, dft_occ_update_def] >>
  simp[dft_pos_phase_def, dft_pos_control_def] >>
  qexists `certs` >> simp[] >>
  Cases_on `ls` >> Cases_on `rs` >> gvs[SF ETA_ss] >>
  fs[dft_pos_phase_def] >> metis_tac[]
QED
Finalise dft_pos_enter_next

(* Half-open one-step Enter segments have no instruction cut and no GAS
   event; their two counters need not start equal. *)
Theorem dft_pos_enter_count:
  c.dft_occ_core = DftOpen (DftEnter f 0 s) stack n ==>
  dft_occ_count (dft_occ_oracle_next w C c) = n
Proof metis_tac[dft_fixed_enter_count]
QED

Theorem dft_pos_enter_no_observe:
  c.dft_occ_core = DftOpen (DftEnter f fuel s) stack n ==>
  ~dft_open_observe g inst t c.dft_occ_core
Proof simp[dft_fixed_enter_no_observe]
QED

Theorem dft_pos_enter_no_event:
  c.dft_occ_core = DftOpen (DftEnter f fuel s) stack n ==>
  ~dft_occ_event inst addr c
Proof simp[dft_occ_event_def]
QED

Theorem dft_pos_enter_no_gas_event:
  c.dft_occ_core = DftOpen (DftEnter f fuel s) stack n ==>
  ~dft_occ_gas_event inst addr c
Proof simp[dft_occ_gas_event_def, dft_occ_event_def]
QED
