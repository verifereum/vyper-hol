Theory dftOriginalRuntime
Ancestors
  dftOccurrenceOrdinaryClosure
  dftOriginalSuccessor dftOriginalCutLifecycle dftOriginalScheduleRuntime
  dftProtectedRuntime dftOccurrenceAvailability dftOccurrenceReplay
  dftOccurrenceMachine dftOpenErase dftOpenMachine venomExecProofs venomWf
  venomInst venomExecSemantics venomState list arithmetic

Definition dft_original_control_ready_def:
  (dft_original_control_ready (DftEnter fn k s) <=>
    k = 0 /\ ?f. dft_original_function f fn /\
      fn_reachable f s.vs_current_bb /\ strict_dom_vars_defined f s) /\
  (dft_original_control_ready (DftAt fn k q s) <=>
    k = 0 /\ MEM q fn.fn_blocks /\ ?f b.
      dft_original_function f fn /\ dft_original_block f b q /\
      fn_reachable f s.vs_current_bb /\ dft_original_cut f b q s) /\
  (dft_original_control_ready (DftDone r) <=> T)
End

Definition dft_original_frame_ready_def:
  dft_original_frame_ready (DftCaller fn k q inst s) <=>
    dft_original_control_ready (DftAt fn k q s) /\
    get_instruction q s.vs_inst_idx = SOME inst /\ inst.inst_opcode = INVOKE
End

Definition dft_original_core_ready_def:
  dft_original_core_ready (DftOpen ctl stack n) <=>
    dft_original_control_ready ctl /\ EVERY dft_original_frame_ready stack
End

Definition dft_original_ready_def:
  dft_original_ready c <=> dft_original_core_ready c.dft_occ_core
End

Theorem dft_original_runtime_root:
  dft_original_function f fn /\ fn_reachable f s.vs_current_bb /\
  strict_dom_vars_defined f s ==>
  dft_original_ready (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))
Proof
  simp[dft_original_ready_def, dft_occ_init_def, dft_original_core_ready_def,
       dft_original_control_ready_def] >> metis_tac[]
QED

Theorem dft_original_runtime_frame_erase[local,simp]:
  dft_original_frame_ready (dft_fill_frame 0 (dft_fill_frame k f)) =
  dft_original_frame_ready (dft_fill_frame 0 f)
Proof
  Cases_on `f` >> simp[dft_fill_frame_def]
QED

Theorem dft_original_runtime_frames_erase[local]:
  EVERY dft_original_frame_ready stack ==>
  EVERY dft_original_frame_ready (MAP (dft_fill_frame 0) stack)
Proof
  simp[EVERY_MEM, MEM_MAP] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >>
  Cases_on `y` >> simp[dft_original_frame_ready_def,
    dft_original_control_ready_def, dft_fill_frame_def]
QED

Theorem dft_original_runtime_entry[local]:
  dft_original_core_ready (DftOpen (DftEnter fn 0 s) stack n) ==>
  dft_original_core_ready (dft_next_inf a C (DftOpen (DftEnter fn 0 s) stack n))
Proof
  simp[dft_original_core_ready_def, dft_original_control_ready_def] >> strip_tac >>
  drule dft_original_runtime_frames_erase >> strip_tac >> fs[EVERY_MAP] >>
  simp[dft_next_inf_def, dft_fill_def, dft_fill_control_def,
       dft_open_next_def, dft_erase_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  simp[dft_fill_def, dft_fill_control_def, dft_original_core_ready_def,
       dft_original_control_ready_def, EVERY_MAP, combinTheory.o_DEF] >>
  rename1 `lookup_block _ _ = SOME q` >>
  `MEM q fn.fn_blocks /\ q.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  drule_all dft_original_function_lookup_block >> strip_tac >>
  Cases_on `eval_phis s q.bb_instructions` >>
  simp[dft_fill_def, dft_fill_control_def, dft_original_core_ready_def,
       dft_original_control_ready_def, EVERY_MAP, combinTheory.o_DEF] >>
  rename1 `eval_phis _ _ = OK sp` >>
  `dft_original_cut f b q
    (sp with vs_inst_idx := phi_prefix_length q.bb_instructions)` by
    metis_tac[dft_original_cut_phis_entry] >>
  fs[dft_original_cut_def, dft_activation_cut_def] >> metis_tac[]
QED

Theorem dft_original_runtime_nonphi[local]:
  dft_original_control_ready (DftAt fn 0 q s) /\
  c.dft_occ_core = DftOpen (DftAt fn 0 q s) stack n /\
  get_instruction q s.vs_inst_idx = SOME inst /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  (dft_occ_oracle_next w C c).dft_occ_core = DftOpen (DftAt fn 0 q t) stack' n'
  ==> dft_original_control_ready (DftAt fn 0 q t)
Proof
  strip_tac >>
  `?f b. dft_original_function f fn /\ dft_original_block f b q /\
    fn_reachable f s.vs_current_bb /\ dft_original_cut f b q s` by
    (fs[dft_original_control_ready_def] >> metis_tac[]) >>
  `MEM inst q.bb_instructions` by
    (fs[get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
  `MEM inst b.bb_instructions` by metis_tac[dft_original_block_mem] >>
  `EVERY inst_wf b.bb_instructions` by
    fs[dft_original_cut_def, dft_original_schedule_def] >>
  `inst_wf inst` by fs[EVERY_MEM] >>
  drule_all dft_occ_continuation_nonphi >> strip_tac >>
  drule_all dft_original_cut_nonphi >> strip_tac >>
  fs[dft_original_control_ready_def, dft_original_cut_def,
     dft_activation_cut_def] >> metis_tac[]
QED

Theorem dft_original_runtime_successor[local]:
  dft_original_control_ready (DftAt fn 0 q s) /\
  c.dft_occ_core = DftOpen (DftAt fn 0 q s) stack n /\
  get_instruction q s.vs_inst_idx = SOME inst /\ is_terminator inst.inst_opcode /\
  (dft_occ_oracle_next w C c).dft_occ_core = DftOpen (DftEnter fn 0 t) stack' n'
  ==> dft_original_control_ready (DftEnter fn 0 t)
Proof
  strip_tac >>
  `?f b. dft_original_function f fn /\ dft_original_block f b q /\
    fn_reachable f s.vs_current_bb /\ dft_original_cut f b q s` by
    (fs[dft_original_control_ready_def] >> metis_tac[]) >>
  drule_all dft_original_occ_successor_available >>
  simp[dft_original_control_ready_def] >> metis_tac[]
QED

Theorem dft_original_runtime_return[local]:
  dft_original_frame_ready (DftCaller fn 0 q inst caller) /\
  c.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller fn 0 q inst caller::stack) n /\
  (dft_occ_oracle_next w C c).dft_occ_core = DftOpen (DftAt fn 0 q t) stack' n'
  ==> dft_original_control_ready (DftAt fn 0 q t)
Proof
  strip_tac >>
  `?f b. dft_original_function f fn /\ dft_original_block f b q /\
    fn_reachable f caller.vs_current_bb /\ dft_original_cut f b q caller` by
    (fs[dft_original_frame_ready_def, dft_original_control_ready_def] >> metis_tac[]) >>
  `get_instruction q caller.vs_inst_idx = SOME inst /\ inst.inst_opcode = INVOKE` by
    fs[dft_original_frame_ready_def] >>
  drule_all dft_original_cut_return >> strip_tac >>
  fs[dft_original_frame_ready_def, dft_original_control_ready_def,
     dft_original_cut_def, dft_activation_cut_def] >> metis_tac[]
QED

Theorem dft_original_runtime_callee[local]:
  dft_original_function f callee /\ setup_callee callee args s = SOME cs ==>
  dft_original_control_ready (DftEnter callee 0 cs)
Proof
  strip_tac >> drule_all dft_original_callee_dom >> strip_tac >>
  `fn_entry_label f = SOME cs.vs_current_bb` by
    (drule dft_original_function_entry >>
     gvs[setup_callee_def, fn_entry_label_def, entry_block_def, AllCaseEqs()]) >>
  `fn_reachable f cs.vs_current_bb` by
    (simp[fn_reachable_def] >> metis_tac[relationTheory.RTC_REFL]) >>
  simp[dft_original_control_ready_def] >> metis_tac[]
QED

Theorem dft_original_runtime_invoke[local]:
  dft_original_context Corig C /\
  dft_original_control_ready (DftAt fn 0 q s) /\
  EVERY dft_original_frame_ready stack /\
  get_instruction q s.vs_inst_idx = SOME inst /\ inst.inst_opcode = INVOKE ==>
  dft_original_core_ready (dft_erase
    (dft_open_invoke C fn 1 q inst s (MAP (dft_fill_frame 1) stack) n))
Proof
  strip_tac >> drule dft_original_runtime_frames_erase >> strip_tac >> fs[EVERY_MAP] >>
  simp[dft_open_invoke_def] >>
  Cases_on `decode_invoke inst` >>
  simp[dft_erase_def, dft_fill_def, dft_fill_control_def,
       dft_original_core_ready_def, dft_original_control_ready_def] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `lookup_function x0 C.ctx_functions` >>
  simp[dft_erase_def, dft_fill_def, dft_fill_control_def,
       dft_original_core_ready_def, dft_original_control_ready_def] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  drule_all dft_original_context_lookup_function >> strip_tac >>
  Cases_on `eval_operands x1 s` >>
  simp[dft_erase_def, dft_fill_def, dft_fill_control_def,
       dft_original_core_ready_def, dft_original_control_ready_def] >>
  rename1 `eval_operands _ _ = SOME args` >>
  Cases_on `setup_callee callee args s` >>
  simp[dft_erase_def, dft_fill_def, dft_fill_control_def,
       dft_original_core_ready_def, dft_original_control_ready_def,
       dft_fill_frame_def, EVERY_MAP, combinTheory.o_DEF] >>
  drule_all dft_original_runtime_callee >>
  simp[dft_original_control_ready_def, dft_original_frame_ready_def]
QED

Theorem dft_original_runtime_deliver[local]:
  dft_original_control_ready (DftAt fn 0 bb s) /\
  EVERY dft_original_frame_ready stack /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_opcode <> INVOKE /\
  (dft_occ_oracle_next w C c).dft_occ_core =
    dft_erase (dft_open_deliver fn 1 bb inst s
      (MAP (dft_fill_frame 1) stack) m result) ==>
  dft_original_ready (dft_occ_oracle_next w C c)
Proof
  strip_tac >> drule dft_original_runtime_frames_erase >> strip_tac >>
  fs[EVERY_MAP] >> Cases_on `result` >>
  gvs[dft_open_deliver_def, dft_erase_def, dft_fill_def,
      dft_fill_control_def, dft_original_ready_def, dft_original_core_ready_def,
      dft_open_continue_def, dft_original_control_ready_def,
      EVERY_MAP, combinTheory.o_DEF] >>
  rename1 `if is_terminator inst.inst_opcode then _ else _` >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (Cases_on `v.vs_halted` >>
      gvs[dft_fill_control_def, dft_original_core_ready_def,
          dft_original_control_ready_def, EVERY_MAP, combinTheory.o_DEF] >>
      `dft_original_control_ready (DftEnter fn 0 v)` by
        (irule dft_original_runtime_successor >> goal_assum drule >> simp[] >>
         metis_tac[dft_original_control_ready_def]) >>
      fs[dft_original_control_ready_def] >> metis_tac[]) >>
  gvs[dft_fill_control_def, dft_original_core_ready_def,
      dft_original_control_ready_def, EVERY_MAP, combinTheory.o_DEF] >>
  `dft_original_control_ready
    (DftAt fn 0 bb (v with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule dft_original_runtime_nonphi >> goal_assum drule >> simp[] >>
     metis_tac[dft_original_control_ready_def]) >>
  fs[dft_original_control_ready_def] >> metis_tac[]
QED

Theorem dft_original_runtime_at[local]:
  dft_original_context Corig C /\
  dft_original_control_ready (DftAt fn 0 bb s) /\
  EVERY dft_original_frame_ready stack /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n ==>
  dft_original_ready (dft_occ_oracle_next w C c)
Proof
  strip_tac >> Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[dft_original_ready_def, dft_occ_oracle_next_def, dft_next_inf_def,
          dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_erase_def,
          dft_original_core_ready_def, dft_original_control_ready_def] >>
  rename1 `get_instruction _ _ = SOME inst` >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (drule_all dft_original_runtime_invoke >> disch_then (qspec_then `n` mp_tac) >>
      simp[dft_original_ready_def, dft_occ_oracle_next_def, dft_next_inf_def,
           dft_fill_def, dft_fill_control_def, dft_open_next_def,
           dft_open_invoke_def]) >>
  Cases_on `inst.inst_opcode = GAS`
  >- (Cases_on `inst.inst_outputs`
      >- simp[dft_original_ready_def, dft_occ_oracle_next_def, dft_next_inf_def,
           dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_erase_def,
           dft_original_core_ready_def, dft_original_control_ready_def] >>
      rename1 `inst.inst_outputs = out::outs` >> reverse (Cases_on `outs`)
      >- simp[dft_original_ready_def, dft_occ_oracle_next_def, dft_next_inf_def,
           dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_erase_def,
           dft_original_core_ready_def, dft_original_control_ready_def] >>
      irule dft_original_runtime_deliver >> goal_assum drule >> simp[] >>
      qexistsl [`SUC n`, `OK (update_var out (w (dft_occ_address c)) s)`] >>
      simp[dft_occ_oracle_next_def, dft_next_inf_def, dft_fill_def,
           dft_fill_control_def, dft_open_next_def, dft_open_deliver_def,
           dft_open_continue_def, dft_erase_def, is_terminator_def]) >>
  irule dft_original_runtime_deliver >> goal_assum drule >> simp[] >>
  qexistsl [`n`, `step_inst_base inst s`] >>
  simp[dft_occ_oracle_next_def, dft_next_inf_def, dft_fill_def,
       dft_fill_control_def, dft_open_next_def]
QED

Theorem dft_original_runtime_resume[local]:
  dft_original_frame_ready (DftCaller fn 0 bb inst caller) /\
  EVERY dft_original_frame_ready stack /\
  c.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller fn 0 bb inst caller::stack) n ==>
  dft_original_ready (dft_occ_oracle_next w C c)
Proof
  strip_tac >> drule dft_original_runtime_frames_erase >> strip_tac >>
  fs[EVERY_MAP] >>
  `inst.inst_opcode = INVOKE` by fs[dft_original_frame_ready_def] >>
  Cases_on `bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs))`
  >- simp[dft_original_ready_def, dft_occ_oracle_next_def, dft_next_inf_def,
          dft_fill_def, dft_fill_control_def, dft_fill_frame_def,
          dft_open_next_def, dft_open_return_def, dft_erase_def,
          dft_original_core_ready_def, dft_original_control_ready_def] >>
  rename1 `bind_outputs _ _ _ = SOME after` >>
  `(dft_occ_oracle_next w C c).dft_occ_core =
    DftOpen (DftAt fn 0 bb (after with vs_inst_idx := SUC caller.vs_inst_idx))
      (MAP (dft_fill_frame 0) (MAP (dft_fill_frame 1) stack)) n` by
    simp[dft_occ_oracle_next_def, dft_next_inf_def,
         dft_fill_def, dft_fill_control_def, dft_fill_frame_def,
         dft_open_next_def, dft_open_return_def, dft_open_deliver_def,
         dft_open_continue_def, is_terminator_def, dft_erase_def] >>
  drule_all dft_original_runtime_return >>
  simp[dft_original_ready_def, dft_original_core_ready_def,
       EVERY_MAP, combinTheory.o_DEF]
QED

Theorem dft_original_runtime_done[local]:
  EVERY dft_original_frame_ready stack /\
  c.dft_occ_core = DftOpen (DftDone result) stack n ==>
  dft_original_ready (dft_occ_oracle_next w C c)
Proof
  strip_tac >> Cases_on `result` >>
  simp[dft_original_ready_def, dft_occ_oracle_next_def, dft_next_inf_def,
       dft_fill_def, dft_fill_control_def, dft_open_next_def,
       dft_open_return_def, dft_erase_def, dft_original_core_ready_def,
       dft_original_control_ready_def] >>
  Cases_on `stack` >> simp[dft_fill_def, dft_fill_control_def,
    dft_original_core_ready_def, dft_original_control_ready_def] >>
  rename1 `c.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (frame::rest) n` >>
  Cases_on `frame` >> rename1 `DftCaller fn budget bb inst caller` >>
  gvs[dft_original_frame_ready_def, dft_original_control_ready_def] >>
  `dft_original_frame_ready (DftCaller fn 0 bb inst caller)` by
    (simp[dft_original_frame_ready_def, dft_original_control_ready_def] >> metis_tac[]) >>
  drule_all dft_original_runtime_resume >>
  simp[dft_original_ready_def, dft_occ_oracle_next_def, dft_next_inf_def,
       dft_fill_def, dft_fill_control_def, dft_fill_frame_def, dft_open_next_def,
       dft_open_return_def, dft_erase_def]
QED

Theorem dft_original_runtime_next:
  dft_original_context Corig C /\ dft_original_ready c ==>
  dft_original_ready (dft_occ_oracle_next w C c)
Proof
  strip_tac >> Cases_on `c.dft_occ_core` >>
  rename1 `c.dft_occ_core = DftOpen ctl stack n` >> Cases_on `ctl`
  >- (rename1 `DftEnter fn budget s` >>
      `budget = 0` by
        fs[dft_original_ready_def, dft_original_core_ready_def,
           dft_original_control_ready_def] >> gvs[] >>
      simp[dft_original_ready_def, dft_occ_oracle_next_def] >>
      irule dft_original_runtime_entry >>
      fs[dft_original_ready_def])
  >- (rename1 `DftAt fn budget bb s` >>
      `budget = 0 /\ dft_original_control_ready (DftAt fn budget bb s) /\
       EVERY dft_original_frame_ready stack` by
        (fs[dft_original_ready_def, dft_original_core_ready_def,
           dft_original_control_ready_def] >> metis_tac[]) >> gvs[] >>
      irule dft_original_runtime_at >> simp[] >> goal_assum drule >> simp[]) >>
  irule dft_original_runtime_done >> simp[] >>
  fs[dft_original_ready_def, dft_original_core_ready_def]
QED

Theorem dft_original_runtime_iter:
  !k c. dft_original_context Corig C /\ dft_original_ready c ==>
    dft_original_ready (FUNPOW (dft_occ_oracle_next w C) k c)
Proof
  Induct >> simp[FUNPOW_SUC] >> metis_tac[dft_original_runtime_next]
QED

(* Label provenance is the existing independent invariant: it fixes the
   complete label map in live controls and suspended callers. *)
Definition dft_original_label_ready_def:
  dft_original_label_ready C L c <=>
    dft_original_ready c /\ dft_source_provenance C L c
End

Theorem dft_original_label_root:
  dft_original_function f fn /\ fn_reachable f s.vs_current_bb /\
  strict_dom_vars_defined f s /\ MEM fn C.ctx_functions /\ s.vs_labels = L ==>
  dft_original_label_ready C L (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))
Proof
  simp[dft_original_label_ready_def] >>
  metis_tac[dft_original_runtime_root, dft_source_root]
QED

Theorem dft_original_label_next:
  dft_original_context Corig C /\ dft_original_label_ready C L c ==>
  dft_original_label_ready C L (dft_occ_oracle_next w C c)
Proof
  simp[dft_original_label_ready_def] >>
  metis_tac[dft_original_runtime_next, dft_source_step]
QED

Theorem dft_original_label_iter:
  !k c. dft_original_context Corig C /\ dft_original_label_ready C L c ==>
    dft_original_label_ready C L (FUNPOW (dft_occ_oracle_next w C) k c)
Proof
  Induct >> simp[FUNPOW_SUC] >> metis_tac[dft_original_label_next]
QED

Theorem dft_original_runtime_at_projection:
  dft_original_ready c /\ c.dft_occ_core = DftOpen (DftAt fn k q s) stack n ==>
  k = 0 /\ MEM q fn.fn_blocks /\ ?f b.
    dft_original_function f fn /\ dft_original_block f b q /\
    fn_reachable f s.vs_current_bb /\ dft_original_cut f b q s
Proof
  strip_tac >> fs[dft_original_ready_def, dft_original_core_ready_def,
       dft_original_control_ready_def] >> metis_tac[]
QED

Theorem dft_original_runtime_frame_projection:
  dft_original_ready c /\ c.dft_occ_core = DftOpen ctl stack n /\
  MEM (DftCaller fn k q inst s) stack ==>
  k = 0 /\ MEM q fn.fn_blocks /\
  get_instruction q s.vs_inst_idx = SOME inst /\ inst.inst_opcode = INVOKE /\
  ?f b. dft_original_function f fn /\ dft_original_block f b q /\
    fn_reachable f s.vs_current_bb /\ dft_original_cut f b q s
Proof
  strip_tac >> fs[dft_original_ready_def, dft_original_core_ready_def, EVERY_MEM] >>
  first_x_assum drule >>
  simp[dft_original_frame_ready_def, dft_original_control_ready_def] >> metis_tac[]
QED
