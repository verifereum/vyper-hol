Theory dftOccurrenceRuntime
Ancestors
  dftOccurrenceAvailability dftOccurrenceReplay dftOccurrenceMachine
  dftOpenErase dftOpenMachine venomExecProofs venomWf venomInst list
  venomExecSemantics venomState sccpCorrectnessProofs arithmetic

Definition dft_runtime_fn_ok_def:
  dft_runtime_fn_ok fn <=> wf_function fn /\ ssa_form fn /\
    EVERY (\bb. EVERY inst_wf bb.bb_instructions) fn.fn_blocks
End

Definition dft_runtime_control_ready_def:
  (dft_runtime_control_ready (DftEnter fn b s) <=>
    b = 0 /\ dft_runtime_fn_ok fn /\
    fn_reachable fn s.vs_current_bb /\ strict_dom_vars_defined fn s) /\
  (dft_runtime_control_ready (DftAt fn b bb s) <=>
    b = 0 /\ dft_runtime_fn_ok fn /\ MEM bb fn.fn_blocks /\
    fn_reachable fn s.vs_current_bb /\ dft_activation_cut fn bb s) /\
  (dft_runtime_control_ready (DftDone r) <=> T)
End

Definition dft_runtime_frame_ready_def:
  dft_runtime_frame_ready (DftCaller fn b bb inst s) <=>
    dft_runtime_control_ready (DftAt fn b bb s) /\
    get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_opcode = INVOKE
End

Definition dft_runtime_core_ready_def:
  dft_runtime_core_ready (DftOpen ctl stack n) <=>
    dft_runtime_control_ready ctl /\ EVERY dft_runtime_frame_ready stack
End

Definition dft_runtime_ready_def:
  dft_runtime_ready c <=> dft_runtime_core_ready c.dft_occ_core
End

Theorem dft_runtime_lookup:
  EVERY dft_runtime_fn_ok C.ctx_functions /\
  lookup_function nm C.ctx_functions = SOME fn ==> dft_runtime_fn_ok fn
Proof
  strip_tac >> drule lookup_function_MEM >> fs[EVERY_MEM]
QED

Theorem dft_runtime_root:
  dft_runtime_fn_ok fn /\ fn_reachable fn s.vs_current_bb /\
  strict_dom_vars_defined fn s ==>
  dft_runtime_ready (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))
Proof
  simp[dft_runtime_ready_def, dft_occ_init_def, dft_runtime_core_ready_def,
       dft_runtime_control_ready_def]
QED

Theorem dft_runtime_frame_erase[local,simp]:
  dft_runtime_frame_ready (dft_fill_frame 0 (dft_fill_frame b f)) =
  dft_runtime_frame_ready (dft_fill_frame 0 f)
Proof
  Cases_on `f` >> simp[dft_fill_frame_def]
QED

Theorem dft_runtime_frames_erase[local]:
  EVERY dft_runtime_frame_ready stack ==>
  EVERY dft_runtime_frame_ready (MAP (dft_fill_frame 0) stack)
Proof
  simp[EVERY_MEM, MEM_MAP] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >>
  Cases_on `y` >> simp[dft_runtime_frame_ready_def,
    dft_runtime_control_ready_def, dft_fill_frame_def]
QED

Theorem dft_runtime_entry[local]:
  dft_runtime_core_ready (DftOpen (DftEnter fn 0 s) stack n) ==>
  dft_runtime_core_ready (dft_next_inf a C (DftOpen (DftEnter fn 0 s) stack n))
Proof
  simp[dft_runtime_core_ready_def, dft_runtime_control_ready_def] >> strip_tac >>
  drule dft_runtime_frames_erase >> strip_tac >> fs[EVERY_MAP] >>
  simp[dft_next_inf_def, dft_fill_def, dft_fill_control_def,
       dft_open_next_def, dft_erase_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  simp[dft_fill_def, dft_fill_control_def, dft_runtime_core_ready_def,
       dft_runtime_control_ready_def, EVERY_MAP, combinTheory.o_DEF] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  simp[dft_fill_def, dft_fill_control_def, dft_runtime_core_ready_def,
       dft_runtime_control_ready_def, EVERY_MAP, combinTheory.o_DEF] >>
  rename1 `eval_phis _ _ = OK sp` >>
  `dft_activation_cut fn bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    metis_tac[dft_activation_cut_phis] >>
  fs[dft_activation_cut_def] >> metis_tac[]
QED

Theorem dft_runtime_nonphi[local]:
  dft_runtime_control_ready (DftAt fn 0 bb s) /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  (dft_occ_oracle_next w C c).dft_occ_core = DftOpen (DftAt fn 0 bb t) stack' n'
  ==> dft_runtime_control_ready (DftAt fn 0 bb t)
Proof
  strip_tac >>
  `inst_wf inst` by
    (fs[dft_runtime_control_ready_def, dft_runtime_fn_ok_def, EVERY_MEM,
        get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
  drule_all dft_occ_continuation_nonphi >> strip_tac >>
  `dft_activation_cut fn bb s` by fs[dft_runtime_control_ready_def] >>
  drule_all dft_activation_cut_nonphi >> strip_tac >>
  fs[dft_runtime_control_ready_def, dft_activation_cut_def] >> metis_tac[]
QED

Theorem dft_runtime_successor[local]:
  dft_runtime_control_ready (DftAt fn 0 bb s) /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ is_terminator inst.inst_opcode /\
  (dft_occ_oracle_next w C c).dft_occ_core = DftOpen (DftEnter fn 0 t) stack' n'
  ==> dft_runtime_control_ready (DftEnter fn 0 t)
Proof
  strip_tac >>
  `wf_function fn /\ ssa_form fn /\ MEM bb fn.fn_blocks /\
   EVERY inst_wf bb.bb_instructions /\ fn_reachable fn s.vs_current_bb /\
   dft_activation_cut fn bb s` by
    (fs[dft_runtime_control_ready_def, dft_runtime_fn_ok_def, EVERY_MEM] >> metis_tac[]) >>
  drule_all dft_occ_successor_available >>
  fs[dft_runtime_control_ready_def]
QED

Theorem dft_runtime_return[local]:
  dft_runtime_frame_ready (DftCaller fn 0 bb inst caller) /\
  c.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller fn 0 bb inst caller::stack) n /\
  (dft_occ_oracle_next w C c).dft_occ_core = DftOpen (DftAt fn 0 bb t) stack' n'
  ==> dft_runtime_control_ready (DftAt fn 0 bb t)
Proof
  strip_tac >>
  `dft_activation_cut fn bb caller /\
   get_instruction bb caller.vs_inst_idx = SOME inst /\ inst.inst_opcode = INVOKE` by
    fs[dft_runtime_frame_ready_def, dft_runtime_control_ready_def] >>
  drule_all dft_activation_cut_return >> strip_tac >>
  fs[dft_runtime_frame_ready_def, dft_runtime_control_ready_def,
     dft_activation_cut_def] >> metis_tac[]
QED

Theorem dft_runtime_callee[local]:
  dft_runtime_fn_ok callee /\ setup_callee callee args s = SOME cs ==>
  dft_runtime_control_ready (DftEnter callee 0 cs)
Proof
  strip_tac >> drule dft_setup_callee_dom >> strip_tac >>
  simp[dft_runtime_control_ready_def] >>
  gvs[setup_callee_def, fn_reachable_def, fn_entry_label_def,
      entry_block_def, AllCaseEqs()] >>
  metis_tac[relationTheory.RTC_REFL]
QED

Theorem dft_runtime_invoke[local]:
  EVERY dft_runtime_fn_ok C.ctx_functions /\
  dft_runtime_control_ready (DftAt fn 0 bb s) /\
  EVERY dft_runtime_frame_ready stack /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_opcode = INVOKE ==>
  dft_runtime_core_ready (dft_erase
    (dft_open_invoke C fn 1 bb inst s (MAP (dft_fill_frame 1) stack) n))
Proof
  strip_tac >> drule dft_runtime_frames_erase >> strip_tac >> fs[EVERY_MAP] >>
  simp[dft_open_invoke_def] >>
  Cases_on `decode_invoke inst` >>
  simp[dft_erase_def, dft_fill_def, dft_fill_control_def,
       dft_runtime_core_ready_def, dft_runtime_control_ready_def] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `lookup_function x0 C.ctx_functions` >>
  simp[dft_erase_def, dft_fill_def, dft_fill_control_def,
       dft_runtime_core_ready_def, dft_runtime_control_ready_def] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  `dft_runtime_fn_ok callee` by metis_tac[dft_runtime_lookup] >>
  Cases_on `eval_operands x1 s` >>
  simp[dft_erase_def, dft_fill_def, dft_fill_control_def,
       dft_runtime_core_ready_def, dft_runtime_control_ready_def] >>
  rename1 `eval_operands _ _ = SOME args` >>
  Cases_on `setup_callee callee args s` >>
  simp[dft_erase_def, dft_fill_def, dft_fill_control_def,
       dft_runtime_core_ready_def, dft_runtime_control_ready_def,
       dft_fill_frame_def, EVERY_MAP, combinTheory.o_DEF] >>
  drule_all dft_runtime_callee >>
  simp[dft_runtime_control_ready_def, dft_runtime_frame_ready_def]
QED

Theorem dft_runtime_deliver[local]:
  dft_runtime_control_ready (DftAt fn 0 bb s) /\
  EVERY dft_runtime_frame_ready stack /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_opcode <> INVOKE /\
  (dft_occ_oracle_next w C c).dft_occ_core =
    dft_erase (dft_open_deliver fn 1 bb inst s
      (MAP (dft_fill_frame 1) stack) m result) ==>
  dft_runtime_ready (dft_occ_oracle_next w C c)
Proof
  strip_tac >> drule dft_runtime_frames_erase >> strip_tac >>
  fs[EVERY_MAP] >> Cases_on `result` >>
  gvs[dft_open_deliver_def, dft_erase_def, dft_fill_def,
      dft_fill_control_def, dft_runtime_ready_def, dft_runtime_core_ready_def,
      dft_open_continue_def, dft_runtime_control_ready_def,
      EVERY_MAP, combinTheory.o_DEF] >>
  rename1 `if is_terminator inst.inst_opcode then _ else _` >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (Cases_on `v.vs_halted` >>
      gvs[dft_fill_control_def, dft_runtime_core_ready_def,
          dft_runtime_control_ready_def, EVERY_MAP, combinTheory.o_DEF] >>
      `dft_runtime_control_ready (DftEnter fn 0 v)` by
        (irule dft_runtime_successor >> goal_assum drule >> simp[] >>
         metis_tac[dft_runtime_control_ready_def]) >>
      fs[dft_runtime_control_ready_def]) >>
  gvs[dft_fill_control_def, dft_runtime_core_ready_def,
      dft_runtime_control_ready_def, EVERY_MAP, combinTheory.o_DEF] >>
  `dft_runtime_control_ready
    (DftAt fn 0 bb (v with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule dft_runtime_nonphi >> goal_assum drule >> simp[] >>
     metis_tac[dft_runtime_control_ready_def]) >>
  fs[dft_runtime_control_ready_def]
QED

Theorem dft_runtime_at[local]:
  EVERY dft_runtime_fn_ok C.ctx_functions /\
  dft_runtime_control_ready (DftAt fn 0 bb s) /\
  EVERY dft_runtime_frame_ready stack /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n ==>
  dft_runtime_ready (dft_occ_oracle_next w C c)
Proof
  strip_tac >> Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[dft_runtime_ready_def, dft_occ_oracle_next_def, dft_next_inf_def,
          dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_erase_def,
          dft_runtime_core_ready_def, dft_runtime_control_ready_def] >>
  rename1 `get_instruction _ _ = SOME inst` >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (drule_all dft_runtime_invoke >> disch_then (qspec_then `n` mp_tac) >>
      simp[dft_runtime_ready_def, dft_occ_oracle_next_def, dft_next_inf_def,
           dft_fill_def, dft_fill_control_def, dft_open_next_def,
           dft_open_invoke_def]) >>
  Cases_on `inst.inst_opcode = GAS`
  >- (Cases_on `inst.inst_outputs`
      >- simp[dft_runtime_ready_def, dft_occ_oracle_next_def, dft_next_inf_def,
           dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_erase_def,
           dft_runtime_core_ready_def, dft_runtime_control_ready_def] >>
      rename1 `inst.inst_outputs = out::outs` >> reverse (Cases_on `outs`)
      >- simp[dft_runtime_ready_def, dft_occ_oracle_next_def, dft_next_inf_def,
           dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_erase_def,
           dft_runtime_core_ready_def, dft_runtime_control_ready_def] >>
      irule dft_runtime_deliver >> goal_assum drule >> simp[] >>
      qexistsl [`SUC n`, `OK (update_var out (w (dft_occ_address c)) s)`] >>
      simp[dft_occ_oracle_next_def, dft_next_inf_def, dft_fill_def,
           dft_fill_control_def, dft_open_next_def, dft_open_deliver_def,
           dft_open_continue_def, dft_erase_def, is_terminator_def]) >>
  irule dft_runtime_deliver >> goal_assum drule >> simp[] >>
  qexistsl [`n`, `step_inst_base inst s`] >>
  simp[dft_occ_oracle_next_def, dft_next_inf_def, dft_fill_def,
       dft_fill_control_def, dft_open_next_def]
QED

Theorem dft_runtime_resume[local]:
  dft_runtime_frame_ready (DftCaller fn 0 bb inst caller) /\
  EVERY dft_runtime_frame_ready stack /\
  c.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller fn 0 bb inst caller::stack) n ==>
  dft_runtime_ready (dft_occ_oracle_next w C c)
Proof
  strip_tac >> drule dft_runtime_frames_erase >> strip_tac >>
  fs[EVERY_MAP] >>
  `inst.inst_opcode = INVOKE` by fs[dft_runtime_frame_ready_def] >>
  Cases_on `bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs))`
  >- simp[dft_runtime_ready_def, dft_occ_oracle_next_def, dft_next_inf_def,
          dft_fill_def, dft_fill_control_def, dft_fill_frame_def,
          dft_open_next_def, dft_open_return_def, dft_erase_def,
          dft_runtime_core_ready_def, dft_runtime_control_ready_def] >>
  rename1 `bind_outputs _ _ _ = SOME after` >>
  `(dft_occ_oracle_next w C c).dft_occ_core =
    DftOpen (DftAt fn 0 bb (after with vs_inst_idx := SUC caller.vs_inst_idx))
      (MAP (dft_fill_frame 0) (MAP (dft_fill_frame 1) stack)) n` by
    simp[dft_occ_oracle_next_def, dft_next_inf_def,
         dft_fill_def, dft_fill_control_def, dft_fill_frame_def,
         dft_open_next_def, dft_open_return_def, dft_open_deliver_def,
         dft_open_continue_def, is_terminator_def, dft_erase_def] >>
  drule_all dft_runtime_return >>
  simp[dft_runtime_ready_def, dft_runtime_core_ready_def,
       EVERY_MAP, combinTheory.o_DEF]
QED

Theorem dft_runtime_done[local]:
  EVERY dft_runtime_frame_ready stack /\
  c.dft_occ_core = DftOpen (DftDone result) stack n ==>
  dft_runtime_ready (dft_occ_oracle_next w C c)
Proof
  strip_tac >> Cases_on `result` >>
  simp[dft_runtime_ready_def, dft_occ_oracle_next_def, dft_next_inf_def,
       dft_fill_def, dft_fill_control_def, dft_open_next_def,
       dft_open_return_def, dft_erase_def, dft_runtime_core_ready_def,
       dft_runtime_control_ready_def] >>
  Cases_on `stack` >> simp[dft_fill_def, dft_fill_control_def,
    dft_runtime_core_ready_def, dft_runtime_control_ready_def] >>
  rename1 `c.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (frame::rest) n` >>
  Cases_on `frame` >> rename1 `DftCaller fn budget bb inst caller` >>
  gvs[dft_runtime_frame_ready_def, dft_runtime_control_ready_def] >>
  `dft_runtime_frame_ready (DftCaller fn 0 bb inst caller)` by
    simp[dft_runtime_frame_ready_def, dft_runtime_control_ready_def] >>
  drule_all dft_runtime_resume >>
  simp[dft_runtime_ready_def, dft_occ_oracle_next_def, dft_next_inf_def,
       dft_fill_def, dft_fill_control_def, dft_fill_frame_def, dft_open_next_def,
       dft_open_return_def, dft_erase_def]
QED

(* The invariant is frame-local: it does not assume that any callee returns. *)
Theorem dft_runtime_next:
  EVERY dft_runtime_fn_ok C.ctx_functions /\ dft_runtime_ready c ==>
  dft_runtime_ready (dft_occ_oracle_next w C c)
Proof
  strip_tac >> Cases_on `c.dft_occ_core` >>
  rename1 `c.dft_occ_core = DftOpen ctl stack n` >> Cases_on `ctl`
  >- (rename1 `DftEnter fn budget s` >>
      `budget = 0` by
        fs[dft_runtime_ready_def, dft_runtime_core_ready_def,
           dft_runtime_control_ready_def] >> gvs[] >>
      simp[dft_runtime_ready_def, dft_occ_oracle_next_def] >>
      irule dft_runtime_entry >>
      fs[dft_runtime_ready_def])
  >- (rename1 `DftAt fn budget bb s` >>
      `budget = 0 /\ dft_runtime_control_ready (DftAt fn budget bb s) /\
       EVERY dft_runtime_frame_ready stack` by
        fs[dft_runtime_ready_def, dft_runtime_core_ready_def,
           dft_runtime_control_ready_def] >> gvs[] >>
      irule dft_runtime_at >> simp[] >> goal_assum drule >> simp[]) >>
  irule dft_runtime_done >> simp[] >>
  fs[dft_runtime_ready_def, dft_runtime_core_ready_def]
QED

Theorem dft_runtime_iter:
  !k c. EVERY dft_runtime_fn_ok C.ctx_functions /\ dft_runtime_ready c ==>
    dft_runtime_ready (FUNPOW (dft_occ_oracle_next w C) k c)
Proof
  Induct >> simp[FUNPOW_SUC] >> metis_tac[dft_runtime_next]
QED

Theorem dft_runtime_at_projection:
  dft_runtime_ready c /\ c.dft_occ_core = DftOpen (DftAt fn b bb s) stack n ==>
  b = 0 /\ dft_runtime_fn_ok fn /\ MEM bb fn.fn_blocks /\
  fn_reachable fn s.vs_current_bb /\ dft_activation_cut fn bb s
Proof
  strip_tac >> fs[dft_runtime_ready_def, dft_runtime_core_ready_def,
       dft_runtime_control_ready_def]
QED

Theorem dft_runtime_frame_projection:
  dft_runtime_ready c /\ c.dft_occ_core = DftOpen ctl stack n /\
  MEM (DftCaller fn b bb inst s) stack ==>
  b = 0 /\ dft_runtime_fn_ok fn /\ MEM bb fn.fn_blocks /\
  fn_reachable fn s.vs_current_bb /\ dft_activation_cut fn bb s /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_opcode = INVOKE
Proof
  strip_tac >> fs[dft_runtime_ready_def, dft_runtime_core_ready_def, EVERY_MEM] >>
  first_x_assum drule >>
  simp[dft_runtime_frame_ready_def, dft_runtime_control_ready_def]
QED
