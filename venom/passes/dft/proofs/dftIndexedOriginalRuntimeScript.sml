Theory dftIndexedOriginalRuntime
Ancestors
  dftOriginalRuntime dftOriginalCutLifecycle dftOriginalScheduleRuntime
  dftProtectedRuntime dftOccurrenceAvailability dftOccurrenceReplay dftOccurrenceMachine
  dftOpenErase dftOriginalSuccessor dftOpenMachine venomExecSemantics venomExecProofs venomWf venomInst venomState list arithmetic

Definition dft_all_original_control_def:
  (dft_all_original_control (DftEnter fn k s) <=>
    k = 0 /\ (!f. dft_original_function f fn ==>
      fn_reachable f s.vs_current_bb /\ strict_dom_vars_defined f s)) /\
  (dft_all_original_control (DftAt fn k q s) <=>
    k = 0 /\ MEM q fn.fn_blocks /\
    (!f. dft_original_function f fn ==>
      fn_reachable f s.vs_current_bb /\
      (!b. dft_original_block f b q ==> dft_original_cut f b q s))) /\
  (dft_all_original_control (DftDone r) <=> T)
End

Definition dft_all_original_frame_def:
  dft_all_original_frame (DftCaller fn k q inst s) <=>
    dft_all_original_control (DftAt fn k q s) /\
    get_instruction q s.vs_inst_idx = SOME inst /\ inst.inst_opcode = INVOKE
End

Definition dft_all_original_core_def:
  dft_all_original_core (DftOpen ctl stack n) <=>
    dft_all_original_control ctl /\ EVERY dft_all_original_frame stack
End

Definition dft_all_original_ready_def:
  dft_all_original_ready c <=> dft_all_original_core c.dft_occ_core
End

Theorem dft_all_original_root:
  fn_entry_label fn = SOME s.vs_current_bb ==>
  dft_all_original_ready (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))
Proof
  simp[dft_all_original_ready_def, dft_occ_init_def,
       dft_all_original_core_def, dft_all_original_control_def] >>
  rpt strip_tac
  >- (drule dft_original_function_entry >>
      simp[fn_reachable_def] >> metis_tac[relationTheory.RTC_REFL]) >>
  metis_tac[dft_original_root_dom]
QED

Theorem dft_all_original_entry_cut:
  dft_all_original_control (DftEnter fn 0 s) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME q /\
  eval_phis s q.bb_instructions = OK sp ==>
  dft_all_original_control (DftAt fn 0 q
    (sp with vs_inst_idx := phi_prefix_length q.bb_instructions))
Proof
  simp[dft_all_original_control_def] >> strip_tac >>
  `MEM q fn.fn_blocks /\ q.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  simp[] >> rpt strip_tac
  >- (drule_all dft_original_function_lookup_block >> strip_tac >>
      `dft_original_cut f b q
        (sp with vs_inst_idx := phi_prefix_length q.bb_instructions)` by
        metis_tac[dft_original_cut_phis_entry] >>
      fs[dft_original_cut_def, dft_activation_cut_def] >> metis_tac[]) >>
  metis_tac[dft_original_cut_phis_entry]
QED

Theorem dft_all_original_return_cut:
  dft_all_original_frame (DftCaller fn 0 q inst caller) /\
  c.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller fn 0 q inst caller::stack) n /\
  (dft_occ_oracle_next w C c).dft_occ_core = DftOpen (DftAt fn 0 q t) stack' n' ==>
  dft_all_original_control (DftAt fn 0 q t)
Proof
  simp[dft_all_original_frame_def, dft_all_original_control_def] >>
  strip_tac >> simp[] >> rpt strip_tac
  >- (drule_all dft_occ_return_control >> simp[]) >>
  metis_tac[dft_original_cut_return]
QED

Theorem dft_all_original_frame_erase[local,simp]:
  dft_all_original_frame (dft_fill_frame 0 (dft_fill_frame k f)) =
  dft_all_original_frame (dft_fill_frame 0 f)
Proof
  Cases_on `f` >> simp[dft_fill_frame_def]
QED

Theorem dft_all_original_frames_erase[local]:
  EVERY dft_all_original_frame stack ==>
  EVERY dft_all_original_frame (MAP (dft_fill_frame 0) stack)
Proof
  simp[EVERY_MEM, MEM_MAP] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> Cases_on `y` >>
  simp[dft_all_original_frame_def, dft_all_original_control_def, dft_fill_frame_def]
QED

Theorem dft_all_original_entry[local]:
  dft_all_original_core (DftOpen (DftEnter fn 0 s) stack n) ==>
  dft_all_original_core (dft_next_inf a C (DftOpen (DftEnter fn 0 s) stack n))
Proof
  simp[dft_all_original_core_def] >> strip_tac >>
  drule dft_all_original_frames_erase >> strip_tac >> fs[EVERY_MAP] >>
  simp[dft_next_inf_def, dft_fill_def, dft_fill_control_def,
       dft_open_next_def, dft_erase_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  simp[dft_fill_def, dft_fill_control_def, dft_all_original_core_def,
       dft_all_original_control_def, EVERY_MAP, combinTheory.o_DEF] >>
  rename1 `lookup_block _ _ = SOME q` >>
  Cases_on `eval_phis s q.bb_instructions` >>
  simp[dft_fill_def, dft_fill_control_def, dft_all_original_core_def,
       dft_all_original_control_def, EVERY_MAP, combinTheory.o_DEF] >>
  drule_all dft_all_original_entry_cut >> simp[dft_all_original_control_def]
QED

Theorem dft_all_original_nonphi[local]:
  dft_all_original_control (DftAt fn 0 q s) /\
  c.dft_occ_core = DftOpen (DftAt fn 0 q s) stack n /\
  get_instruction q s.vs_inst_idx = SOME inst /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  (dft_occ_oracle_next w C c).dft_occ_core = DftOpen (DftAt fn 0 q t) stack' n'
  ==> dft_all_original_control (DftAt fn 0 q t)
Proof
  strip_tac >> simp[dft_all_original_control_def] >>
  `MEM q fn.fn_blocks` by fs[dft_all_original_control_def] >>
  simp[] >> gen_tac >> strip_tac >>
  `fn_reachable f s.vs_current_bb` by metis_tac[dft_all_original_control_def] >>
  `?b. dft_original_block f b q` by
    (fs[dft_original_function_def] >> metis_tac[LIST_REL_MEM_IMP_R]) >>
  `dft_original_cut f b q s` by metis_tac[dft_all_original_control_def] >>
  `MEM inst q.bb_instructions` by
    (fs[get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
  `MEM inst b.bb_instructions` by metis_tac[dft_original_block_mem] >>
  `EVERY inst_wf b.bb_instructions` by
    fs[dft_original_cut_def, dft_original_schedule_def] >>
  `inst_wf inst` by fs[EVERY_MEM] >>
  drule_all dft_occ_continuation_nonphi >> strip_tac >>
  conj_tac
  >- (drule_all dft_original_cut_nonphi >>
      fs[dft_original_cut_def, dft_activation_cut_def] >> metis_tac[]) >>
  rpt strip_tac >> irule dft_original_cut_nonphi >>
  goal_assum drule >> simp[] >> metis_tac[dft_all_original_control_def]
QED

Theorem dft_all_original_successor[local]:
  dft_all_original_control (DftAt fn 0 q s) /\
  c.dft_occ_core = DftOpen (DftAt fn 0 q s) stack n /\
  get_instruction q s.vs_inst_idx = SOME inst /\ is_terminator inst.inst_opcode /\
  (dft_occ_oracle_next w C c).dft_occ_core = DftOpen (DftEnter fn 0 t) stack' n'
  ==> dft_all_original_control (DftEnter fn 0 t)
Proof
  strip_tac >> simp[dft_all_original_control_def] >> rpt strip_tac >>
  `MEM q fn.fn_blocks` by fs[dft_all_original_control_def] >>
  `?b. dft_original_block f b q` by
    (fs[dft_original_function_def] >> metis_tac[LIST_REL_MEM_IMP_R]) >>
  `fn_reachable f s.vs_current_bb /\ dft_original_cut f b q s` by
    metis_tac[dft_all_original_control_def] >>
  drule_all dft_original_occ_successor_available >> simp[]
QED

Theorem dft_all_original_callee[local]:
  setup_callee callee args s = SOME cs ==>
  dft_all_original_control (DftEnter callee 0 cs)
Proof
  strip_tac >> simp[dft_all_original_control_def] >> rpt strip_tac >>
  drule_all dft_original_callee_dom >> strip_tac >>
  `fn_entry_label f = SOME cs.vs_current_bb` by
    (drule dft_original_function_entry >>
     gvs[setup_callee_def, fn_entry_label_def, entry_block_def, AllCaseEqs()]) >>
  simp[fn_reachable_def] >> metis_tac[relationTheory.RTC_REFL]
QED

Theorem dft_all_original_invoke[local]:
  dft_all_original_control (DftAt fn 0 q s) /\
  EVERY dft_all_original_frame stack /\
  get_instruction q s.vs_inst_idx = SOME inst /\ inst.inst_opcode = INVOKE ==>
  dft_all_original_core (dft_erase
    (dft_open_invoke C fn 1 q inst s (MAP (dft_fill_frame 1) stack) n))
Proof
  strip_tac >> drule dft_all_original_frames_erase >> strip_tac >> fs[EVERY_MAP] >>
  simp[dft_open_invoke_def] >>
  Cases_on `decode_invoke inst` >>
  simp[dft_erase_def, dft_fill_def, dft_fill_control_def,
       dft_all_original_core_def, dft_all_original_control_def] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `lookup_function x0 C.ctx_functions` >>
  simp[dft_erase_def, dft_fill_def, dft_fill_control_def,
       dft_all_original_core_def, dft_all_original_control_def] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  Cases_on `eval_operands x1 s` >>
  simp[dft_erase_def, dft_fill_def, dft_fill_control_def,
       dft_all_original_core_def, dft_all_original_control_def] >>
  rename1 `eval_operands _ _ = SOME args` >>
  Cases_on `setup_callee callee args s` >>
  simp[dft_erase_def, dft_fill_def, dft_fill_control_def,
       dft_all_original_core_def, dft_all_original_control_def,
       dft_fill_frame_def, EVERY_MAP, combinTheory.o_DEF] >>
  drule dft_all_original_callee >>
  simp[dft_all_original_control_def, dft_all_original_frame_def]
QED

Theorem dft_all_original_deliver[local]:
  dft_all_original_control (DftAt fn 0 bb s) /\
  EVERY dft_all_original_frame stack /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_opcode <> INVOKE /\
  (dft_occ_oracle_next w C c).dft_occ_core =
    dft_erase (dft_open_deliver fn 1 bb inst s
      (MAP (dft_fill_frame 1) stack) m result) ==>
  dft_all_original_ready (dft_occ_oracle_next w C c)
Proof
  strip_tac >> drule dft_all_original_frames_erase >> strip_tac >>
  fs[EVERY_MAP] >> Cases_on `result` >>
  gvs[dft_open_deliver_def, dft_erase_def, dft_fill_def,
      dft_fill_control_def, dft_all_original_ready_def, dft_all_original_core_def,
      dft_open_continue_def, dft_all_original_control_def,
      EVERY_MAP, combinTheory.o_DEF] >>
  rename1 `if is_terminator inst.inst_opcode then _ else _` >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (Cases_on `v.vs_halted` >>
      gvs[dft_fill_control_def, dft_all_original_core_def,
          dft_all_original_control_def, EVERY_MAP, combinTheory.o_DEF] >>
      `dft_all_original_control (DftEnter fn 0 v)` by
        (irule dft_all_original_successor >> goal_assum drule >> simp[] >>
         metis_tac[dft_all_original_control_def]) >>
      fs[dft_all_original_control_def] >> metis_tac[]) >>
  gvs[dft_fill_control_def, dft_all_original_core_def,
      dft_all_original_control_def, EVERY_MAP, combinTheory.o_DEF] >>
  `dft_all_original_control
    (DftAt fn 0 bb (v with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule dft_all_original_nonphi >> goal_assum drule >> simp[] >>
     metis_tac[dft_all_original_control_def]) >>
  fs[dft_all_original_control_def] >> metis_tac[]
QED

Theorem dft_all_original_at[local]:
  dft_all_original_control (DftAt fn 0 bb s) /\
  EVERY dft_all_original_frame stack /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n ==>
  dft_all_original_ready (dft_occ_oracle_next w C c)
Proof
  strip_tac >> Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[dft_all_original_ready_def, dft_occ_oracle_next_def, dft_next_inf_def,
          dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_erase_def,
          dft_all_original_core_def, dft_all_original_control_def] >>
  rename1 `get_instruction _ _ = SOME inst` >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (drule_all dft_all_original_invoke >> disch_then (qspec_then `n` mp_tac) >>
      simp[dft_all_original_ready_def, dft_occ_oracle_next_def, dft_next_inf_def,
           dft_fill_def, dft_fill_control_def, dft_open_next_def,
           dft_open_invoke_def]) >>
  Cases_on `inst.inst_opcode = GAS`
  >- (Cases_on `inst.inst_outputs`
      >- simp[dft_all_original_ready_def, dft_occ_oracle_next_def, dft_next_inf_def,
           dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_erase_def,
           dft_all_original_core_def, dft_all_original_control_def] >>
      rename1 `inst.inst_outputs = out::outs` >> reverse (Cases_on `outs`)
      >- simp[dft_all_original_ready_def, dft_occ_oracle_next_def, dft_next_inf_def,
           dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_erase_def,
           dft_all_original_core_def, dft_all_original_control_def] >>
      irule dft_all_original_deliver >> goal_assum drule >> simp[] >>
      qexistsl [`SUC n`, `OK (update_var out (w (dft_occ_address c)) s)`] >>
      simp[dft_occ_oracle_next_def, dft_next_inf_def, dft_fill_def,
           dft_fill_control_def, dft_open_next_def, dft_open_deliver_def,
           dft_open_continue_def, dft_erase_def, is_terminator_def]) >>
  irule dft_all_original_deliver >> goal_assum drule >> simp[] >>
  qexistsl [`n`, `step_inst_base inst s`] >>
  simp[dft_occ_oracle_next_def, dft_next_inf_def, dft_fill_def,
       dft_fill_control_def, dft_open_next_def]
QED

Theorem dft_all_original_resume[local]:
  dft_all_original_frame (DftCaller fn 0 bb inst caller) /\
  EVERY dft_all_original_frame stack /\
  c.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller fn 0 bb inst caller::stack) n ==>
  dft_all_original_ready (dft_occ_oracle_next w C c)
Proof
  strip_tac >> drule dft_all_original_frames_erase >> strip_tac >>
  fs[EVERY_MAP] >>
  `inst.inst_opcode = INVOKE` by fs[dft_all_original_frame_def] >>
  Cases_on `bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs))`
  >- simp[dft_all_original_ready_def, dft_occ_oracle_next_def, dft_next_inf_def,
          dft_fill_def, dft_fill_control_def, dft_fill_frame_def,
          dft_open_next_def, dft_open_return_def, dft_erase_def,
          dft_all_original_core_def, dft_all_original_control_def] >>
  rename1 `bind_outputs _ _ _ = SOME after` >>
  `(dft_occ_oracle_next w C c).dft_occ_core =
    DftOpen (DftAt fn 0 bb (after with vs_inst_idx := SUC caller.vs_inst_idx))
      (MAP (dft_fill_frame 0) (MAP (dft_fill_frame 1) stack)) n` by
    simp[dft_occ_oracle_next_def, dft_next_inf_def,
         dft_fill_def, dft_fill_control_def, dft_fill_frame_def,
         dft_open_next_def, dft_open_return_def, dft_open_deliver_def,
         dft_open_continue_def, is_terminator_def, dft_erase_def] >>
  drule_all dft_all_original_return_cut >>
  simp[dft_all_original_ready_def, dft_all_original_core_def,
       EVERY_MAP, combinTheory.o_DEF]
QED

Theorem dft_all_original_done[local]:
  EVERY dft_all_original_frame stack /\
  c.dft_occ_core = DftOpen (DftDone result) stack n ==>
  dft_all_original_ready (dft_occ_oracle_next w C c)
Proof
  strip_tac >> Cases_on `result` >>
  simp[dft_all_original_ready_def, dft_occ_oracle_next_def, dft_next_inf_def,
       dft_fill_def, dft_fill_control_def, dft_open_next_def,
       dft_open_return_def, dft_erase_def, dft_all_original_core_def,
       dft_all_original_control_def] >>
  Cases_on `stack` >> simp[dft_fill_def, dft_fill_control_def,
    dft_all_original_core_def, dft_all_original_control_def] >>
  rename1 `c.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (frame::rest) n` >>
  Cases_on `frame` >> rename1 `DftCaller fn budget bb inst caller` >>
  gvs[dft_all_original_frame_def, dft_all_original_control_def] >>
  `dft_all_original_frame (DftCaller fn 0 bb inst caller)` by
    (simp[dft_all_original_frame_def, dft_all_original_control_def] >> metis_tac[]) >>
  drule_all dft_all_original_resume >>
  simp[dft_all_original_ready_def, dft_occ_oracle_next_def, dft_next_inf_def,
       dft_fill_def, dft_fill_control_def, dft_fill_frame_def, dft_open_next_def,
       dft_open_return_def, dft_erase_def]
QED

Theorem dft_all_original_next:
  dft_original_context Corig C /\ dft_all_original_ready c ==>
  dft_all_original_ready (dft_occ_oracle_next w C c)
Proof
  strip_tac >> Cases_on `c.dft_occ_core` >>
  rename1 `c.dft_occ_core = DftOpen ctl stack n` >> Cases_on `ctl`
  >- (rename1 `DftEnter fn budget s` >>
      `budget = 0` by
        fs[dft_all_original_ready_def, dft_all_original_core_def,
           dft_all_original_control_def] >> gvs[] >>
      simp[dft_all_original_ready_def, dft_occ_oracle_next_def] >>
      irule dft_all_original_entry >> fs[dft_all_original_ready_def])
  >- (rename1 `DftAt fn budget bb s` >>
      `budget = 0 /\ dft_all_original_control (DftAt fn budget bb s) /\
       EVERY dft_all_original_frame stack` by
        (fs[dft_all_original_ready_def, dft_all_original_core_def,
           dft_all_original_control_def] >> metis_tac[]) >> gvs[] >>
      irule dft_all_original_at >> simp[] >> goal_assum drule >> simp[]) >>
  irule dft_all_original_done >> simp[] >>
  fs[dft_all_original_ready_def, dft_all_original_core_def]
QED

Theorem dft_all_original_iter:
  !k c. dft_original_context Corig C /\ dft_all_original_ready c ==>
    dft_all_original_ready (FUNPOW (dft_occ_oracle_next w C) k c)
Proof
  Induct >> simp[FUNPOW_SUC] >> metis_tac[dft_all_original_next]
QED

Theorem dft_all_original_indexed_at:
  dft_original_context Corig D /\ dft_all_original_ready c /\
  fi < LENGTH D.ctx_functions /\
  bi < LENGTH (EL fi D.ctx_functions).fn_blocks /\
  c.dft_occ_core = DftOpen
    (DftAt (EL fi D.ctx_functions) k (EL bi (EL fi D.ctx_functions).fn_blocks) s)
    stack n ==>
  dft_original_cut (EL fi Corig.ctx_functions)
    (EL bi (EL fi Corig.ctx_functions).fn_blocks)
    (EL bi (EL fi D.ctx_functions).fn_blocks) s
Proof
  strip_tac >>
  `dft_original_function (EL fi Corig.ctx_functions) (EL fi D.ctx_functions)` by
    (fs[dft_original_context_def, LIST_REL_EL_EQN] >> metis_tac[]) >>
  `dft_original_block (EL fi Corig.ctx_functions)
    (EL bi (EL fi Corig.ctx_functions).fn_blocks)
    (EL bi (EL fi D.ctx_functions).fn_blocks)` by
    (fs[dft_original_function_def, LIST_REL_EL_EQN] >> metis_tac[]) >>
  fs[dft_all_original_ready_def, dft_all_original_core_def,
     dft_all_original_control_def] >> metis_tac[]
QED

Theorem dft_all_original_indexed_frame:
  dft_original_context Corig D /\ dft_all_original_ready c /\
  fi < LENGTH D.ctx_functions /\
  bi < LENGTH (EL fi D.ctx_functions).fn_blocks /\
  c.dft_occ_core = DftOpen ctl stack n /\
  MEM (DftCaller (EL fi D.ctx_functions) k
    (EL bi (EL fi D.ctx_functions).fn_blocks) inst s) stack ==>
  dft_original_cut (EL fi Corig.ctx_functions)
    (EL bi (EL fi Corig.ctx_functions).fn_blocks)
    (EL bi (EL fi D.ctx_functions).fn_blocks) s
Proof
  strip_tac >>
  `dft_original_function (EL fi Corig.ctx_functions) (EL fi D.ctx_functions)` by
    (fs[dft_original_context_def, LIST_REL_EL_EQN] >> metis_tac[]) >>
  `dft_original_block (EL fi Corig.ctx_functions)
    (EL bi (EL fi Corig.ctx_functions).fn_blocks)
    (EL bi (EL fi D.ctx_functions).fn_blocks)` by
    (fs[dft_original_function_def, LIST_REL_EL_EQN] >> metis_tac[]) >>
  `dft_all_original_frame (DftCaller (EL fi D.ctx_functions) k
    (EL bi (EL fi D.ctx_functions).fn_blocks) inst s)` by
    (fs[dft_all_original_ready_def, dft_all_original_core_def, EVERY_MEM] >>
     metis_tac[]) >>
  fs[dft_all_original_frame_def, dft_all_original_control_def] >> metis_tac[]
QED
