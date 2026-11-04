Theory dftPositionalStep
Ancestors
  dftPositionalReturn dftPositionalPhase dftPositionalRuntime dftRelationalEdit
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

Theorem dft_pos_slot_instruction_outside:
  D = dft_pos_edit_ctx fi bi pre x call post C /\
  dft_pos_runtime_ready C fi bi pre x call post /\
  dft_pos_slot C D j k f g b b' /\
  (j <> fi \/ k <> bi \/ (i <> LENGTH pre /\ i <> SUC (LENGTH pre))) ==>
  get_instruction b i = get_instruction b' i
Proof
  strip_tac >> fs[dft_pos_runtime_ready_def, dft_pos_slot_def] >>
  metis_tac[dft_pos_edit_instruction_outside]
QED

Theorem dft_pos_at_outside_next:
  D = dft_pos_edit_ctx fi bi pre x call post C /\
  dft_pos_runtime_ready C fi bi pre x call post /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_pos_phase C D fi bi pre x call post l r /\
  l.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  r.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR /\
  dft_pos_slot C D j k f g b b' /\
  (j <> fi \/ k <> bi \/
    (s.vs_inst_idx <> LENGTH pre /\ s.vs_inst_idx <> SUC (LENGTH pre))) ==>
  dft_pos_phase C D fi bi pre x call post
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w D r)
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `get_instruction b s.vs_inst_idx = get_instruction b' s.vs_inst_idx` by
    metis_tac[dft_pos_slot_instruction_outside] >>
  `dft_original_ready (dft_occ_oracle_next w C l) /\
   dft_original_ready (dft_occ_oracle_next w D r)` by
    (fs[dft_pos_phase_def] >> metis_tac[dft_original_runtime_next]) >>
  `?certs. dft_pos_stack C D fi bi pre x call post certs ls rs /\
    LENGTH l.dft_occ_saved = LENGTH certs` by
    (fs[dft_pos_phase_def] >> metis_tac[]) >>
  drule dft_pos_stack_fill >> strip_tac >>
  drule_all dft_pos_stack_saved_empty >> strip_tac >>
  `!fr. dft_fill_frame 0 (dft_fill_frame 1 fr) = dft_fill_frame 0 fr` by
    (Cases >> simp[dft_fill_frame_def]) >>
  Cases_on `get_instruction b' s.vs_inst_idx`
  >- suspend "missing_at" >>
  rename1 `get_instruction b' s.vs_inst_idx = SOME inst` >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- suspend "invoke_at" >>
  Cases_on `inst.inst_opcode = GAS`
  >- suspend "gas_at" >>
  suspend "ordinary_at"
QED

Resume dft_pos_at_outside_next[missing_at]:
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_erase_def, dft_occ_update_def] >>
  simp[dft_pos_phase_def, dft_pos_control_def, dft_pos_stack_def] >>
  fs[dft_pos_phase_def] >> metis_tac[]
QED

Resume dft_pos_at_outside_next[ordinary_at]:
  `dft_pos_functions C D f g` by
    (fs[dft_pos_slot_def, dft_pos_functions_def] >> metis_tac[]) >>
  Cases_on `step_inst_base inst s`
  >- (Cases_on `is_terminator inst.inst_opcode`
      >- (Cases_on `v.vs_halted` >>
          gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
            dft_fill_def, dft_fill_control_def, dft_open_next_def,
            dft_open_deliver_def, dft_open_continue_def, dft_erase_def,
            MAP_MAP_o, combinTheory.o_DEF, dft_occ_update_def, SF ETA_ss] >>
          simp[dft_pos_phase_def, dft_pos_control_def] >>
          qexists `certs` >> simp[] >>
          Cases_on `ls` >> Cases_on `rs` >> gvs[] >>
          fs[dft_pos_phase_def] >> metis_tac[]) >>
      gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
        dft_fill_def, dft_fill_control_def, dft_open_next_def,
        dft_open_deliver_def, dft_open_continue_def, dft_erase_def,
        MAP_MAP_o, combinTheory.o_DEF, dft_occ_update_def, SF ETA_ss] >>
      simp[dft_pos_phase_def, dft_pos_control_def] >>
      qexists `certs` >> simp[] >>
      Cases_on `ls` >> Cases_on `rs` >> gvs[] >>
      fs[dft_pos_phase_def] >> metis_tac[]) >>
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_open_deliver_def, dft_erase_def,
    MAP_MAP_o, combinTheory.o_DEF, dft_occ_update_def, SF ETA_ss] >>
  simp[dft_pos_phase_def, dft_pos_control_def] >>
  qexists `certs` >> simp[] >>
  Cases_on `ls` >> Cases_on `rs` >> gvs[] >>
  fs[dft_pos_phase_def] >> metis_tac[]
QED

Resume dft_pos_at_outside_next[gas_at]:
  Cases_on `inst.inst_outputs` >>
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_erase_def, dft_occ_update_def, dft_occ_address_def]
  >- (simp[dft_pos_phase_def, dft_pos_control_def, dft_pos_stack_def] >>
      fs[dft_pos_phase_def] >> metis_tac[]) >>
  Cases_on `t` >>
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_open_deliver_def, dft_open_continue_def, is_terminator_def,
    dft_erase_def, MAP_MAP_o, combinTheory.o_DEF, dft_occ_update_def,
    dft_occ_address_def, SF ETA_ss]
  >- (simp[dft_pos_phase_def, dft_pos_control_def] >>
      qexists `certs` >> simp[] >> Cases_on `ls` >> Cases_on `rs` >> gvs[] >>
      fs[dft_pos_phase_def] >> metis_tac[]) >>
  simp[dft_pos_phase_def, dft_pos_control_def, dft_pos_stack_def] >>
  fs[dft_pos_phase_def] >> metis_tac[]
QED

Resume dft_pos_at_outside_next[invoke_at]:
  `dft_rel_interface C D (dft_pos_functions C D) (dft_pos_blocks C D)` by
    metis_tac[dft_pos_runtime_ready_interface] >>
  Cases_on `decode_invoke inst`
  >- suspend "bad_decode" >>
  PairCases_on `x'` >>
  `OPTREL (dft_pos_functions C D)
    (lookup_function x'0 C.ctx_functions) (lookup_function x'0 D.ctx_functions)` by
    fs[dft_rel_interface_def] >>
  Cases_on `lookup_function x'0 C.ctx_functions`
  >- suspend "bad_lookup" >>
  fs[optionTheory.OPTREL_def] >>
  rename1 `lookup_function x'0 C.ctx_functions = SOME callee` >>
  rename1 `lookup_function x'0 D.ctx_functions = SOME callee'` >>
  `!args. setup_callee callee args s = setup_callee callee' args s` by
    metis_tac[dft_rel_interface_def] >>
  Cases_on `eval_operands x'1 s`
  >- suspend "bad_args" >>
  rename1 `eval_operands x'1 s = SOME args` >>
  Cases_on `setup_callee callee' args s`
  >- suspend "bad_setup" >>
  `dft_pos_stack C D fi bi pre x call post (NONE::certs)
    (DftCaller f 0 b inst s::ls) (DftCaller g 0 b' inst s::rs)` by
    (simp[dft_pos_stack_def] >> irule dft_pos_plain_frame >> simp[] >> metis_tac[]) >>
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_open_invoke_def, dft_erase_def, MAP_MAP_o, combinTheory.o_DEF,
    dft_fill_frame_def, dft_occ_update_def, SF ETA_ss] >>
  simp[dft_pos_phase_def, dft_pos_control_def] >>
  qexists `NONE::certs` >> simp[] >>
  fs[dft_pos_phase_def] >> metis_tac[]
QED

Resume dft_pos_at_outside_next[bad_decode]:
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_open_invoke_def, dft_erase_def, dft_occ_update_def] >>
  simp[dft_pos_phase_def, dft_pos_control_def, dft_pos_stack_def] >>
  fs[dft_pos_phase_def] >> metis_tac[]
QED
Resume dft_pos_at_outside_next[bad_lookup]:
  fs[optionTheory.OPTREL_def] >>
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_open_invoke_def, dft_erase_def, dft_occ_update_def] >>
  simp[dft_pos_phase_def, dft_pos_control_def, dft_pos_stack_def] >>
  fs[dft_pos_phase_def] >> metis_tac[]
QED
Resume dft_pos_at_outside_next[bad_args]:
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_open_invoke_def, dft_erase_def, dft_occ_update_def] >>
  simp[dft_pos_phase_def, dft_pos_control_def, dft_pos_stack_def] >>
  fs[dft_pos_phase_def] >> metis_tac[]
QED
Resume dft_pos_at_outside_next[bad_setup]:
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_open_invoke_def, dft_erase_def, dft_occ_update_def] >>
  simp[dft_pos_phase_def, dft_pos_control_def, dft_pos_stack_def] >>
  fs[dft_pos_phase_def] >> metis_tac[]
QED
Finalise dft_pos_at_outside_next

Theorem dft_pos_at_outside_count:
  D = dft_pos_edit_ctx fi bi pre x call post C /\
  dft_pos_runtime_ready C fi bi pre x call post /\
  dft_pos_slot C D j k f g b b' /\
  (j <> fi \/ k <> bi \/
    (s.vs_inst_idx <> LENGTH pre /\ s.vs_inst_idx <> SUC (LENGTH pre))) /\
  l.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  r.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR ==>
  dft_occ_count (dft_occ_oracle_next w C l) - dft_occ_count l =
  dft_occ_count (dft_occ_oracle_next w D r) - dft_occ_count r
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `get_instruction b s.vs_inst_idx = get_instruction b' s.vs_inst_idx` by
    metis_tac[dft_pos_slot_instruction_outside] >>
  qpat_assum `l.dft_occ_core = _` (mp_then Any mp_tac dft_fixed_at_count) >>
  disch_then (qspecl_then [`w`,`C`] assume_tac) >>
  qpat_assum `r.dft_occ_core = _` (mp_then Any mp_tac dft_fixed_at_count) >>
  disch_then (qspecl_then [`w`,`D`] assume_tac) >>
  simp[dft_occ_count_def]
QED

Theorem dft_pos_at_outside_event:
  D = dft_pos_edit_ctx fi bi pre x call post C /\
  dft_pos_runtime_ready C fi bi pre x call post /\
  dft_pos_slot C D j k f g b b' /\
  (j <> fi \/ k <> bi \/
    (s.vs_inst_idx <> LENGTH pre /\ s.vs_inst_idx <> SUC (LENGTH pre))) /\
  l.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  r.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR /\
  l.dft_occ_path = r.dft_occ_path /\ l.dft_occ_visit = r.dft_occ_visit ==>
  (dft_occ_gas_event inst addr l <=> dft_occ_gas_event inst addr r)
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `get_instruction b s.vs_inst_idx = get_instruction b' s.vs_inst_idx` by
    metis_tac[dft_pos_slot_instruction_outside] >>
  simp[dft_occ_gas_event_def, dft_occ_event_def]
QED

Theorem dft_pos_at_outside_observe:
  D = dft_pos_edit_ctx fi bi pre x call post C /\
  dft_pos_runtime_ready C fi bi pre x call post /\
  dft_pos_slot C D j k f g b b' /\
  (j <> fi \/ k <> bi \/
    (s.vs_inst_idx <> LENGTH pre /\ s.vs_inst_idx <> SUC (LENGTH pre))) /\
  l.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  r.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR ==>
  (dft_open_observe f inst t l.dft_occ_core <=>
   dft_open_observe g inst t r.dft_occ_core)
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `get_instruction b s.vs_inst_idx = get_instruction b' s.vs_inst_idx` by
    metis_tac[dft_pos_slot_instruction_outside] >>
  simp[dft_open_observe_def] >> metis_tac[]
QED

Theorem dft_pos_at_outside_memory_forward:
  D = dft_pos_edit_ctx fi bi pre x call post C /\
  dft_pos_runtime_ready C fi bi pre x call post /\
  dft_pos_slot C D j k f g b b' /\
  (j <> fi \/ k <> bi \/
    (s.vs_inst_idx <> LENGTH pre /\ s.vs_inst_idx <> SUC (LENGTH pre))) /\
  l.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  r.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR /\
  dft_open_observe h inst t l.dft_occ_core ==>
  ?h' t'. dft_open_observe h' inst t' r.dft_occ_core /\
    dft_pos_functions C D h h' /\ t.vs_memory = t'.vs_memory /\
    inst_mem_ranges inst t = inst_mem_ranges inst t'
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `get_instruction b s.vs_inst_idx = get_instruction b' s.vs_inst_idx` by
    metis_tac[dft_pos_slot_instruction_outside] >>
  gvs[dft_open_observe_def] >>
  fs[dft_pos_functions_def, dft_pos_slot_def] >> metis_tac[]
QED

Theorem dft_pos_at_outside_memory_backward:
  D = dft_pos_edit_ctx fi bi pre x call post C /\
  dft_pos_runtime_ready C fi bi pre x call post /\
  dft_pos_slot C D j k f g b b' /\
  (j <> fi \/ k <> bi \/
    (s.vs_inst_idx <> LENGTH pre /\ s.vs_inst_idx <> SUC (LENGTH pre))) /\
  l.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  r.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR /\
  dft_open_observe h' inst t' r.dft_occ_core ==>
  ?h t. dft_open_observe h inst t l.dft_occ_core /\
    dft_pos_functions C D h h' /\ t.vs_memory = t'.vs_memory /\
    inst_mem_ranges inst t = inst_mem_ranges inst t'
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `get_instruction b s.vs_inst_idx = get_instruction b' s.vs_inst_idx` by
    metis_tac[dft_pos_slot_instruction_outside] >>
  gvs[dft_open_observe_def] >>
  fs[dft_pos_functions_def, dft_pos_slot_def] >> metis_tac[]
QED
