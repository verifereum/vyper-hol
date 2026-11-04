Theory dftRecursiveFixedStep
Ancestors
  dftRecursiveFixedPhase dftRecursiveReturnPhase dftRecursiveCallProvenance
  dftRecursiveCallResidual dftOccurrenceGasEdit dftOccurrenceReplay
  dftOccurrenceMachine dftOpenErase dftOpenMachine dftOpenHistory dftOriginalRuntime
  venomExecSemantics venomState venomInst list arithmetic

Theorem dft_fixed_instruction_outside:
  q.bb_instructions = pre ++ [x;call] ++ post /\
  ~(bb = q /\ i = LENGTH pre) /\
  ~(bb = q /\ i = SUC (LENGTH pre)) ==>
  get_instruction (dft_gas_edit_block q pre x call post bb) i =
    get_instruction bb i
Proof
  strip_tac >> irule dft_gas_edit_instruction_outside >> simp[] >> metis_tac[]
QED

Theorem dft_fixed_phi_bound:
  !pre. x.inst_opcode <> PHI ==>
  phi_prefix_length (pre ++ [x;call] ++ post) <= LENGTH pre
Proof
  Induct >> simp[phi_prefix_length_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[]
QED

Theorem dft_fixed_entry_not_interior:
  q.bb_instructions = pre ++ [x;call] ++ post /\ x.inst_opcode <> PHI ==>
  ~(bb = q /\ phi_prefix_length bb.bb_instructions = SUC (LENGTH pre))
Proof
  strip_tac >> Cases_on `bb = q` >> simp[] >>
  `phi_prefix_length (pre ++ [x;call] ++ post) <= LENGTH pre` by
    (irule dft_fixed_phi_bound >> simp[]) >> decide_tac
QED

Theorem dft_fixed_enter_next:
  q.bb_instructions = pre ++ [x;call] ++ post /\
  x.inst_opcode <> PHI /\ call.inst_opcode <> PHI /\
  c.dft_occ_core = DftOpen (DftEnter fn 0 s) ls nL /\
  d.dft_occ_core = DftOpen (DftEnter (dft_gas_edit_fn q pre x call post fn) 0 s) rs nR /\
  dft_fixed_stack q pre x call post certs ls rs /\
  c.dft_occ_path = d.dft_occ_path /\ c.dft_occ_visit = d.dft_occ_visit /\
  c.dft_occ_saved = d.dft_occ_saved /\ LENGTH c.dft_occ_saved = LENGTH certs /\
  dft_original_ready c /\ dft_original_ready d /\
  dft_original_context Corig C /\
  dft_original_context Dorig (dft_gas_edit_ctx q pre x call post C) ==>
  dft_fixed_phase q pre x call post
    (dft_occ_oracle_next w C c)
    (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d)
Proof
  strip_tac >>
  `dft_original_ready (dft_occ_oracle_next w C c)` by
    metis_tac[dft_original_runtime_next] >>
  `dft_original_ready (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d)` by
    metis_tac[dft_original_runtime_next] >>
  `dft_provenanced_frames (dft_gas_edit_fn q pre x call post)
    (dft_gas_edit_block q pre x call post) certs ls rs` by fs[dft_fixed_stack_def] >>
  drule dft_provenanced_frames_fill >> strip_tac >>
  drule_all dft_provenanced_frames_saved_empty >> strip_tac >>
  `!fr. dft_fill_frame 0 (dft_fill_frame 1 fr) = dft_fill_frame 0 fr` by
    (Cases >> simp[dft_fill_frame_def]) >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_gas_edit_lookup_block] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
        dft_fill_def, dft_fill_control_def, dft_open_next_def,
        dft_gas_edit_lookup_block, dft_erase_def, dft_occ_update_def] >>
      simp[dft_fixed_phase_def, dft_fixed_control_def] >>
      qexists `[]` >> simp[]) >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  `~(bb = q /\ phi_prefix_length bb.bb_instructions = SUC (LENGTH pre))` by
    metis_tac[dft_fixed_entry_not_interior] >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_gas_edit_lookup_block, dft_nonphi_edit_phis, dft_nonphi_edit_phi_length,
    dft_erase_def, MAP_MAP_o, combinTheory.o_DEF, dft_fill_frame_def,
    dft_occ_update_def] >>
  simp[dft_fixed_phase_def, dft_fixed_control_def] >>
  qexists `certs` >> simp[] >>
  Cases_on `ls` >> Cases_on `rs` >> gvs[SF ETA_ss]
QED

Theorem dft_fixed_at_observe:
  q.bb_instructions = pre ++ [x;call] ++ post /\
  ~(bb = q /\ s.vs_inst_idx = LENGTH pre) /\
  ~(bb = q /\ s.vs_inst_idx = SUC (LENGTH pre)) ==>
  (dft_open_observe (dft_gas_edit_fn q pre x call post fn) inst s
    (DftOpen (DftAt (dft_gas_edit_fn q pre x call post fn) 0
      (dft_gas_edit_block q pre x call post bb) s) rs nR) <=>
   dft_open_observe fn inst s (DftOpen (DftAt fn 0 bb s) ls nL))
Proof
  strip_tac >> drule_all dft_fixed_instruction_outside >>
  simp[dft_open_observe_def]
QED

Theorem dft_fixed_enter_count:
  c.dft_occ_core = DftOpen (DftEnter fn 0 s) ls n ==>
  dft_occ_count (dft_occ_oracle_next w C c) = n
Proof
  strip_tac >>
  simp[dft_occ_count_def, dft_occ_oracle_next_def, dft_occ_next_def,
    dft_next_inf_def, dft_fill_def, dft_fill_control_def, dft_open_next_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[dft_erase_def, dft_fill_def, dft_fill_control_def] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  simp[dft_erase_def, dft_fill_def, dft_fill_control_def]
QED

Theorem dft_fixed_ordinary_next:
  q.bb_instructions = pre ++ [x;call] ++ post /\
  ~(bb = q /\ s.vs_inst_idx = LENGTH pre) /\
  ~(bb = q /\ s.vs_inst_idx = SUC (LENGTH pre)) /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) ls nL /\
  d.dft_occ_core = DftOpen (DftAt (dft_gas_edit_fn q pre x call post fn) 0
    (dft_gas_edit_block q pre x call post bb) s) rs nR /\
  dft_fixed_stack q pre x call post certs ls rs /\
  c.dft_occ_path = d.dft_occ_path /\ c.dft_occ_visit = d.dft_occ_visit /\
  c.dft_occ_saved = d.dft_occ_saved /\ LENGTH c.dft_occ_saved = LENGTH certs /\
  dft_original_ready c /\ dft_original_ready d /\
  dft_original_context Corig C /\
  dft_original_context Dorig (dft_gas_edit_ctx q pre x call post C) ==>
  dft_fixed_phase q pre x call post (dft_occ_oracle_next w C c)
    (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d)
Proof
  strip_tac >>
  drule_all dft_fixed_instruction_outside >> strip_tac >>
  `dft_original_ready (dft_occ_oracle_next w C c)` by
    metis_tac[dft_original_runtime_next] >>
  `dft_original_ready (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d)` by
    metis_tac[dft_original_runtime_next] >>
  `dft_provenanced_frames (dft_gas_edit_fn q pre x call post)
    (dft_gas_edit_block q pre x call post) certs ls rs` by fs[dft_fixed_stack_def] >>
  drule dft_provenanced_frames_fill >> strip_tac >>
  drule_all dft_provenanced_frames_saved_empty >> strip_tac >>
  `!fr. dft_fill_frame 0 (dft_fill_frame 1 fr) = dft_fill_frame 0 fr` by
    (Cases >> simp[dft_fill_frame_def]) >>
  Cases_on `step_inst_base inst s`
  >- (Cases_on `is_terminator inst.inst_opcode`
      >- (Cases_on `v.vs_halted` >>
          gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
            dft_fill_def, dft_fill_control_def, dft_open_next_def,
            dft_open_deliver_def, dft_open_continue_def, dft_erase_def,
            MAP_MAP_o, combinTheory.o_DEF, dft_occ_update_def, SF ETA_ss] >>
          simp[dft_fixed_phase_def, dft_fixed_control_def] >>
          qexists `certs` >> simp[] >>
          Cases_on `ls` >> Cases_on `rs` >> gvs[]) >>
      gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
        dft_fill_def, dft_fill_control_def, dft_open_next_def,
        dft_open_deliver_def, dft_open_continue_def, dft_erase_def,
        MAP_MAP_o, combinTheory.o_DEF, dft_occ_update_def, SF ETA_ss] >>
      simp[dft_fixed_phase_def, dft_fixed_control_def] >>
      qexists `certs` >> simp[] >>
      Cases_on `ls` >> Cases_on `rs` >> gvs[]) >>
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_open_deliver_def, dft_erase_def,
    MAP_MAP_o, combinTheory.o_DEF, dft_occ_update_def, SF ETA_ss] >>
  simp[dft_fixed_phase_def, dft_fixed_control_def] >>
  qexists `certs` >> simp[] >>
  Cases_on `ls` >> Cases_on `rs` >> gvs[]
QED

Theorem dft_fixed_gas_next:
  q.bb_instructions = pre ++ [x;call] ++ post /\
  ~(bb = q /\ s.vs_inst_idx = LENGTH pre) /\
  ~(bb = q /\ s.vs_inst_idx = SUC (LENGTH pre)) /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_opcode = GAS /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) ls nL /\
  d.dft_occ_core = DftOpen (DftAt (dft_gas_edit_fn q pre x call post fn) 0
    (dft_gas_edit_block q pre x call post bb) s) rs nR /\
  dft_fixed_stack q pre x call post certs ls rs /\
  c.dft_occ_path = d.dft_occ_path /\ c.dft_occ_visit = d.dft_occ_visit /\
  c.dft_occ_saved = d.dft_occ_saved /\ LENGTH c.dft_occ_saved = LENGTH certs /\
  dft_original_ready c /\ dft_original_ready d /\
  dft_original_context Corig C /\
  dft_original_context Dorig (dft_gas_edit_ctx q pre x call post C) ==>
  dft_fixed_phase q pre x call post (dft_occ_oracle_next w C c)
    (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d)
Proof
  strip_tac >> drule_all dft_fixed_instruction_outside >> strip_tac >>
  `dft_original_ready (dft_occ_oracle_next w C c)` by
    metis_tac[dft_original_runtime_next] >>
  `dft_original_ready (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d)` by
    metis_tac[dft_original_runtime_next] >>
  `dft_provenanced_frames (dft_gas_edit_fn q pre x call post)
    (dft_gas_edit_block q pre x call post) certs ls rs` by fs[dft_fixed_stack_def] >>
  drule dft_provenanced_frames_fill >> strip_tac >>
  drule_all dft_provenanced_frames_saved_empty >> strip_tac >>
  `!fr. dft_fill_frame 0 (dft_fill_frame 1 fr) = dft_fill_frame 0 fr` by
    (Cases >> simp[dft_fill_frame_def]) >>
  Cases_on `inst.inst_outputs` >>
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_erase_def, dft_occ_update_def, dft_occ_address_def] 
  >- (simp[dft_fixed_phase_def, dft_fixed_control_def] >> qexists `[]` >> simp[]) >>
  Cases_on `t` >>
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_open_deliver_def, dft_open_continue_def, is_terminator_def,
    dft_erase_def, MAP_MAP_o, combinTheory.o_DEF, dft_occ_update_def,
    dft_occ_address_def, SF ETA_ss] 
  >- (simp[dft_fixed_phase_def, dft_fixed_control_def] >>
      qexists `certs` >> simp[] >> Cases_on `ls` >> Cases_on `rs` >> gvs[]) >>
  simp[dft_fixed_phase_def, dft_fixed_control_def] >> qexists `[]` >> simp[]
QED

Theorem dft_fixed_invoke_next:
  q.bb_instructions = pre ++ [x;call] ++ post /\
  ~(bb = q /\ s.vs_inst_idx = LENGTH pre) /\
  ~(bb = q /\ s.vs_inst_idx = SUC (LENGTH pre)) /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_opcode = INVOKE /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) ls nL /\
  d.dft_occ_core = DftOpen (DftAt (dft_gas_edit_fn q pre x call post fn) 0
    (dft_gas_edit_block q pre x call post bb) s) rs nR /\
  dft_fixed_stack q pre x call post certs ls rs /\
  c.dft_occ_path = d.dft_occ_path /\ c.dft_occ_visit = d.dft_occ_visit /\
  c.dft_occ_saved = d.dft_occ_saved /\ LENGTH c.dft_occ_saved = LENGTH certs /\
  dft_original_ready c /\ dft_original_ready d /\
  dft_original_context Corig C /\
  dft_original_context Dorig (dft_gas_edit_ctx q pre x call post C) ==>
  dft_fixed_phase q pre x call post (dft_occ_oracle_next w C c)
    (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d)
Proof
  strip_tac >> drule_all dft_fixed_instruction_outside >> strip_tac >>
  `dft_original_ready (dft_occ_oracle_next w C c)` by
    metis_tac[dft_original_runtime_next] >>
  `dft_original_ready (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d)` by
    metis_tac[dft_original_runtime_next] >>
  Cases_on `decode_invoke inst`
  >- (gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
        dft_fill_def, dft_fill_control_def, dft_open_next_def,
        dft_open_invoke_def, dft_erase_def, dft_occ_update_def] >>
      simp[dft_fixed_phase_def, dft_fixed_control_def] >> qexists `[]` >> simp[]) >>
  PairCases_on `x'` >>
  Cases_on `lookup_function x'0 C.ctx_functions`
  >- (gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
        dft_fill_def, dft_fill_control_def, dft_open_next_def,
        dft_open_invoke_def, dft_gas_edit_lookup_function,
        dft_erase_def, dft_occ_update_def] >>
      simp[dft_fixed_phase_def, dft_fixed_control_def] >> qexists `[]` >> simp[]) >>
  Cases_on `eval_operands x'1 s`
  >- (gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
        dft_fill_def, dft_fill_control_def, dft_open_next_def,
        dft_open_invoke_def, dft_gas_edit_lookup_function,
        dft_erase_def, dft_occ_update_def] >>
      simp[dft_fixed_phase_def, dft_fixed_control_def] >> qexists `[]` >> simp[]) >>
  rename1 `lookup_function x'0 C.ctx_functions = SOME callee` >>
  rename1 `eval_operands x'1 s = SOME args` >>
  Cases_on `setup_callee callee args s`
  >- (gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
        dft_fill_def, dft_fill_control_def, dft_open_next_def,
        dft_open_invoke_def, dft_gas_edit_lookup_function, dft_gas_edit_setup_callee,
        dft_erase_def, dft_occ_update_def] >>
      simp[dft_fixed_phase_def, dft_fixed_control_def] >> qexists `[]` >> simp[]) >>
  `dft_fixed_stack q pre x call post (NONE::certs)
    (DftCaller fn 0 bb inst s::ls)
    (DftCaller (dft_gas_edit_fn q pre x call post fn) 0
      (dft_gas_edit_block q pre x call post bb) inst s::rs)` by
    (irule dft_fixed_plain_push >> simp[] >>
     simp[dft_provenanced_frame_def, dft_recursive_frame_def, dft_recursive_payload_def] >>
     metis_tac[]) >>
  `dft_provenanced_frames (dft_gas_edit_fn q pre x call post)
    (dft_gas_edit_block q pre x call post) certs ls rs` by fs[dft_fixed_stack_def] >>
  drule dft_provenanced_frames_fill >> strip_tac >>
  `!fr. dft_fill_frame 0 (dft_fill_frame 1 fr) = dft_fill_frame 0 fr` by
    (Cases >> simp[dft_fill_frame_def]) >>
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_open_invoke_def, dft_gas_edit_lookup_function, dft_gas_edit_setup_callee,
    dft_erase_def, MAP_MAP_o, combinTheory.o_DEF, dft_fill_frame_def,
    dft_occ_update_def, SF ETA_ss] >>
  simp[dft_fixed_phase_def, dft_fixed_control_def] >>
  qexists `NONE::certs` >> simp[]
QED

Theorem dft_fixed_at_next:
  q.bb_instructions = pre ++ [x;call] ++ post /\
  ~(bb = q /\ s.vs_inst_idx = LENGTH pre) /\
  ~(bb = q /\ s.vs_inst_idx = SUC (LENGTH pre)) /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) ls nL /\
  d.dft_occ_core = DftOpen (DftAt (dft_gas_edit_fn q pre x call post fn) 0
    (dft_gas_edit_block q pre x call post bb) s) rs nR /\
  dft_fixed_stack q pre x call post certs ls rs /\
  c.dft_occ_path = d.dft_occ_path /\ c.dft_occ_visit = d.dft_occ_visit /\
  c.dft_occ_saved = d.dft_occ_saved /\ LENGTH c.dft_occ_saved = LENGTH certs /\
  dft_original_ready c /\ dft_original_ready d /\
  dft_original_context Corig C /\
  dft_original_context Dorig (dft_gas_edit_ctx q pre x call post C) ==>
  dft_fixed_phase q pre x call post (dft_occ_oracle_next w C c)
    (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d)
Proof
  strip_tac >> Cases_on `get_instruction bb s.vs_inst_idx`
  >- (drule_all dft_fixed_instruction_outside >> strip_tac >>
      `dft_original_ready (dft_occ_oracle_next w C c)` by
        metis_tac[dft_original_runtime_next] >>
      `dft_original_ready (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d)` by
        metis_tac[dft_original_runtime_next] >>
      gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
        dft_fill_def, dft_fill_control_def, dft_open_next_def,
        dft_erase_def, dft_occ_update_def] >>
      simp[dft_fixed_phase_def, dft_fixed_control_def] >> qexists `[]` >> simp[]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (irule dft_fixed_invoke_next >> simp[] >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = GAS`
  >- (irule dft_fixed_gas_next >> simp[] >> metis_tac[]) >>
  irule dft_fixed_ordinary_next >> simp[] >> metis_tac[]
QED

Theorem dft_fixed_counter_fill[local,simp]:
  dft_history_counter (dft_fill k core) = dft_history_counter core
Proof
  Cases_on `core` >> simp[dft_fill_def, dft_history_counter_def]
QED

Theorem dft_fixed_occ_counter[local]:
  dft_occ_count (dft_occ_oracle_next w C c) =
    dft_history_counter (dft_open_next (\n. w (dft_occ_address c)) C
      (dft_fill 1 c.dft_occ_core))
Proof
  simp[dft_occ_count_def, dft_occ_oracle_next_def, dft_occ_next_def,
    dft_next_inf_def, dft_erase_def] >>
  Cases_on `dft_open_next (\n. w (dft_occ_address c)) C (dft_fill 1 c.dft_occ_core)` >>
  simp[dft_fill_def, dft_history_counter_def]
QED

Theorem dft_fixed_invoke_counter[local,simp]:
  dft_history_counter (dft_open_invoke C fn b bb inst s stack n) = n
Proof
  simp[dft_open_invoke_def] >> CASE_TAC >> simp[dft_history_counter_def] >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >> simp[] >>
  CASE_TAC >> simp[dft_history_counter_def] >>
  CASE_TAC >> simp[dft_history_counter_def] >>
  CASE_TAC >> simp[dft_history_counter_def]
QED

Theorem dft_fixed_at_count:
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) ls n ==>
  dft_occ_count (dft_occ_oracle_next w C c) = n +
    (if ?inst out. get_instruction bb s.vs_inst_idx = SOME inst /\
         inst.inst_opcode = GAS /\ inst.inst_outputs = [out] then 1 else 0)
Proof
  strip_tac >> simp[dft_fixed_occ_counter, dft_fill_def, dft_fill_control_def,
    dft_open_next_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[dft_history_counter_def] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  Cases_on `inst.inst_opcode = INVOKE` >> simp[] >>
  Cases_on `inst.inst_opcode = GAS` >> simp[] >>
  Cases_on `inst.inst_outputs` >> simp[dft_history_counter_def] >>
  Cases_on `t` >> simp[dft_history_counter_def]
QED

Theorem dft_fixed_at_count_agree:
  q.bb_instructions = pre ++ [x;call] ++ post /\
  ~(bb = q /\ s.vs_inst_idx = LENGTH pre) /\
  ~(bb = q /\ s.vs_inst_idx = SUC (LENGTH pre)) /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) ls nL /\
  d.dft_occ_core = DftOpen (DftAt (dft_gas_edit_fn q pre x call post fn) 0
    (dft_gas_edit_block q pre x call post bb) s) rs nR ==>
  dft_occ_count (dft_occ_oracle_next w C c) - dft_occ_count c =
  dft_occ_count (dft_occ_oracle_next w D d) - dft_occ_count d
Proof
  strip_tac >> drule_all dft_fixed_instruction_outside >> strip_tac >>
  qpat_assum `c.dft_occ_core = _` (mp_then Any mp_tac dft_fixed_at_count) >>
  disch_then (qspecl_then [`w`,`C`] assume_tac) >>
  qpat_assum `d.dft_occ_core = _` (mp_then Any mp_tac dft_fixed_at_count) >>
  disch_then (qspecl_then [`w`,`D`] assume_tac) >>
  simp[dft_occ_count_def]
QED

Theorem dft_fixed_at_event_agree:
  q.bb_instructions = pre ++ [x;call] ++ post /\
  ~(bb = q /\ s.vs_inst_idx = LENGTH pre) /\
  ~(bb = q /\ s.vs_inst_idx = SUC (LENGTH pre)) /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) ls nL /\
  d.dft_occ_core = DftOpen (DftAt (dft_gas_edit_fn q pre x call post fn) 0
    (dft_gas_edit_block q pre x call post bb) s) rs nR /\
  c.dft_occ_path = d.dft_occ_path /\ c.dft_occ_visit = d.dft_occ_visit ==>
  (dft_occ_event inst addr c <=> dft_occ_event inst addr d)
Proof
  strip_tac >> drule_all dft_fixed_instruction_outside >>
  simp[dft_occ_event_def]
QED

Theorem dft_fixed_enter_no_observe:
  ~dft_open_observe f inst t (DftOpen (DftEnter fn b s) ls n)
Proof
  simp[dft_open_observe_def]
QED
