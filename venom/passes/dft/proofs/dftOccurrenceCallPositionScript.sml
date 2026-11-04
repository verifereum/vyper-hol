Theory dftOccurrenceCallPosition
Ancestors
  dftOccurrenceCallClosure dftOccurrenceCallCrossing dftOccurrenceCallStack
  dftOccurrenceSuspended dftOccurrenceGasEdit dftOccurrenceMachine dftOccurrenceReplay
  dftOpenMachine dftOpenErase venomExecSemantics venomInst venomState arithmetic list

Theorem dft_mixed_phi_bound:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\ gas.inst_opcode = GAS ==>
  phi_prefix_length bb0.bb_instructions <= LENGTH pre
Proof
  metis_tac[dft_gas_edit_phi_bound]
QED

Theorem dft_mixed_caller_not_first:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\ gas.inst_opcode = GAS /\
  dft_mixed_frame bb0 pre gas call post v w path visit
    (DftCaller fnL 0 bb0 inst s) (DftCaller fnR 0 bbR inst s) ==>
  s.vs_inst_idx <> LENGTH pre
Proof
  simp[dft_mixed_frame_def] >> rpt strip_tac >>
  gvs[get_instruction_def, EL_APPEND_EQN]
QED

Theorem dft_mixed_safe_enter:
  l.dft_occ_core = DftOpen (DftEnter fn b s) stack n ==>
  dft_mixed_safe_sync bb0 pre l
Proof
  simp[dft_mixed_safe_sync_def]
QED

Theorem dft_mixed_safe_done:
  l.dft_occ_core = DftOpen (DftDone result) stack n ==>
  dft_mixed_safe_sync bb0 pre l
Proof
  simp[dft_mixed_safe_sync_def]
QED

Theorem dft_mixed_safe_after_index:
  l.dft_occ_core = DftOpen (DftAt fn 0 bb (s with vs_inst_idx := SUC idx)) stack n /\
  (bb = bb0 ==> idx <> LENGTH pre) ==>
  dft_mixed_safe_sync bb0 pre l
Proof
  simp[dft_mixed_safe_sync_def] >> rpt strip_tac >> gvs[]
QED

Theorem dft_mixed_enter_position:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\ gas.inst_opcode = GAS /\
  l.dft_occ_core = DftOpen (DftEnter fn 0 s) stack n ==>
  dft_mixed_safe_sync bb0 pre (dft_occ_oracle_next w C l)
Proof
  strip_tac >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_erase_def, dft_fill_def, dft_fill_control_def, dft_open_next_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[dft_occ_update_def, dft_fill_def, dft_fill_control_def,
           dft_mixed_safe_sync_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  simp[dft_occ_update_def, dft_fill_def, dft_fill_control_def,
       dft_mixed_safe_sync_def] >>
  rpt strip_tac >> gvs[] >>
  drule_all dft_mixed_phi_bound >> simp[]
QED

Theorem dft_mixed_crossing_position:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\ ~MEM v call.inst_outputs /\
  (!nm ops. decode_invoke call = SOME (nm,ops) ==> ~MEM (Var v) ops) /\
  dft_mixed_sync bb0 pre gas call post v w l r /\
  l.dft_occ_core = DftOpen (DftAt fn 0 bb0 s) stack n /\
  s.vs_inst_idx = LENGTH pre ==>
  dft_mixed_safe_sync bb0 pre (dft_occ_oracle_next w C (dft_occ_oracle_next w C l))
Proof
  strip_tac >>
  Cases_on `?nm ops callee args cs.
    decode_invoke call = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs`
  >- (pop_assum strip_assume_tac >>
      `~MEM (Var v) ops` by metis_tac[] >>
      drule_all dft_mixed_crossing_entry >>
      simp_tac bool_ss [LET_THM] >> strip_tac >>
      irule dft_mixed_safe_enter >> simp[] >> metis_tac[]) >>
  drule_all dft_mixed_crossing_failure >>
  simp[dft_suspend_cleared_def] >> strip_tac >>
  irule dft_mixed_safe_done >> metis_tac[]
QED

Theorem dft_mixed_discharge_position:
  dft_mixed_discharge bb0 pre gas call post v w l r ==>
  dft_mixed_safe_sync bb0 pre l
Proof
  simp[dft_mixed_discharge_def] >> rpt strip_tac >>
  gvs[dft_mixed_frame_def] >>
  gvs[dft_suspend_resumed_def] >>
  simp[dft_mixed_safe_sync_def]
QED

Theorem dft_mixed_deliver_position:
  dft_fill 0 (dft_open_deliver fn budget bb inst s stack n result) =
    DftOpen (DftAt fn' 0 bb' s') stack' n' ==>
  bb' = bb /\ s'.vs_inst_idx = SUC s.vs_inst_idx
Proof
  Cases_on `result` >>
  simp[dft_open_deliver_def, dft_open_continue_def, dft_erase_def,
       dft_fill_def, dft_fill_control_def] >>
  Cases_on `is_terminator inst.inst_opcode` >>
  simp[dft_fill_control_def] >>
  Cases_on `v.vs_halted` >> simp[dft_fill_control_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem dft_mixed_at_position:
  l.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  (bb = bb0 ==> s.vs_inst_idx <> LENGTH pre) ==>
  dft_mixed_safe_sync bb0 pre (dft_occ_oracle_next w C l)
Proof
  strip_tac >> simp[dft_mixed_safe_sync_def, dft_occ_oracle_next_def,
    dft_next_inf_def, dft_fill_def, dft_fill_control_def, dft_open_next_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[dft_erase_def, dft_fill_def, dft_fill_control_def] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (simp[dft_open_invoke_def] >>
      Cases_on `decode_invoke inst` >>
      simp[dft_erase_def, dft_fill_def, dft_fill_control_def] >>
      PairCases_on `x` >> Cases_on `lookup_function x0 C.ctx_functions` >>
      simp[dft_fill_def, dft_fill_control_def] >>
      Cases_on `eval_operands x1 s` >>
      simp[dft_fill_def, dft_fill_control_def] >>
      rename1 `setup_callee callee args s` >> Cases_on `setup_callee callee args s` >>
      simp[dft_fill_def, dft_fill_control_def]) >>
  Cases_on `inst.inst_opcode = GAS`
  >- (Cases_on `inst.inst_outputs` >>
      simp[dft_erase_def, dft_fill_def, dft_fill_control_def] >>
      rename1 `_ = SOME inst` >>
      Cases_on `t` >> simp[dft_fill_def, dft_fill_control_def,
        dft_open_deliver_def, dft_open_continue_def, is_terminator_def] >>
      rpt strip_tac >> gvs[]) >>
  Cases_on `step_inst_base inst s` >>
  simp[dft_open_deliver_def, dft_open_continue_def, dft_erase_def,
       dft_fill_def, dft_fill_control_def] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[dft_fill_control_def] >>
  Cases_on `v.vs_halted` >> simp[dft_fill_control_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem dft_mixed_frame_not_first:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\ gas.inst_opcode = GAS /\
  dft_mixed_frame bb0 pre gas call post v w path visit
    (DftCaller fnL 0 bbL inst s) (DftCaller fnR 0 bbR inst t) ==>
  (bbL = bb0 ==> s.vs_inst_idx <> LENGTH pre)
Proof
  simp[dft_mixed_frame_def] >> rpt strip_tac >>
  gvs[get_instruction_def, EL_APPEND_EQN]
QED

Theorem dft_mixed_return_position:
  l.dft_occ_core = DftOpen (DftDone result) stack n /\
  (!fn bb inst s rest. stack = DftCaller fn 0 bb inst s :: rest ==>
    (bb = bb0 ==> s.vs_inst_idx <> LENGTH pre)) /\
  MAP (dft_fill_frame 0) stack = stack ==>
  dft_mixed_safe_sync bb0 pre (dft_occ_oracle_next w C l)
Proof
  strip_tac >> simp[dft_mixed_safe_sync_def, dft_occ_oracle_next_def,
    dft_next_inf_def, dft_fill_def, dft_fill_control_def, dft_open_next_def] >>
  Cases_on `result` >> Cases_on `stack` >>
  simp[dft_open_return_def, dft_erase_def, dft_fill_def, dft_fill_control_def] >>
  Cases_on `h` >>
  gvs[dft_fill_frame_def] >>
  rename1 `DftCaller fn budget bb inst s` >>
  Cases_on `bind_outputs inst.inst_outputs i.iret_values
    (adopt_return_fmp i (merge_callee_state s v))` >>
  simp[dft_fill_def, dft_fill_control_def, dft_open_deliver_def,
       dft_open_continue_def] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[dft_fill_control_def] >>
  Cases_on `x.vs_halted` >> simp[dft_fill_control_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem dft_mixed_done_position:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\ gas.inst_opcode = GAS /\
  dft_mixed_sync bb0 pre gas call post v w l r /\
  l.dft_occ_core = DftOpen (DftDone result) stack n ==>
  dft_mixed_safe_sync bb0 pre (dft_occ_oracle_next w C l)
Proof
  strip_tac >>
  qpat_x_assum `dft_mixed_sync _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [dft_mixed_sync_def]) >> gvs[] >>
  drule dft_mixed_stack_erase >> strip_tac >>
  irule dft_mixed_return_position >> simp[] >>
  rpt strip_tac >> gvs[] >>
  drule dft_mixed_stack_head >> strip_tac >>
  Cases_on `fR` >> drule dft_mixed_frame_shape >> strip_tac >> gvs[] >>
  metis_tac[dft_mixed_frame_not_first]
QED

Theorem dft_mixed_sync_done_safe:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\ gas.inst_opcode = GAS /\
  dft_mixed_sync bb0 pre gas call post v w l r /\
  l.dft_occ_core = DftOpen (DftDone result) stack n ==>
  (dft_mixed_sync bb0 pre gas call post v w
    (dft_occ_oracle_next w C l)
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r) /\
   dft_mixed_safe_sync bb0 pre (dft_occ_oracle_next w C l)) \/
  dft_mixed_discharge bb0 pre gas call post v w
    (dft_occ_oracle_next w C l)
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r) \/
  dft_suspend_cleared (dft_occ_oracle_next w C l)
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r)
Proof
  metis_tac[dft_mixed_sync_done, dft_mixed_done_position]
QED

Theorem dft_mixed_sync_enter_safe:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  gas.inst_opcode = GAS /\ call.inst_opcode = INVOKE /\
  dft_mixed_sync bb0 pre gas call post v w l r /\
  l.dft_occ_core = DftOpen (DftEnter fn 0 s) stack n ==>
  dft_mixed_sync bb0 pre gas call post v w
    (dft_occ_oracle_next w C l)
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r) /\
  dft_mixed_safe_sync bb0 pre (dft_occ_oracle_next w C l)
Proof
  strip_tac >> conj_tac
  >- (irule dft_mixed_sync_enter >> simp[]) >>
  metis_tac[dft_mixed_enter_position]
QED

Theorem dft_mixed_sync_at_safe:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  (bb = bb0 ==> s.vs_inst_idx <> LENGTH pre /\
                   s.vs_inst_idx <> SUC (LENGTH pre)) /\
  dft_mixed_sync bb0 pre gas call post v w l r /\
  l.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n ==>
  dft_mixed_sync bb0 pre gas call post v w
    (dft_occ_oracle_next w C l)
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r) /\
  dft_mixed_safe_sync bb0 pre (dft_occ_oracle_next w C l)
Proof
  strip_tac >> conj_tac
  >- (irule dft_mixed_sync_at >> simp[]) >>
  irule dft_mixed_at_position >> metis_tac[]
QED

Theorem dft_mixed_discharge_next_safe:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  dft_mixed_discharge bb0 pre gas call post v w l r ==>
  dft_mixed_sync bb0 pre gas call post v w l
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r) /\
  dft_mixed_safe_sync bb0 pre l
Proof
  metis_tac[dft_mixed_discharge_next, dft_mixed_discharge_position]
QED
