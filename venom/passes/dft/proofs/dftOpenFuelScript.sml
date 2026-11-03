(* Uniformly shifting active and saved fuel preserves active observations. *)
Theory dftOpenFuel
Ancestors
  dftOpenMachine arithmetic

Definition dft_shift_frame_def:
  dft_shift_frame delta (DftCaller fn b bb inst s) =
    DftCaller fn (b+delta) bb inst s
End

Definition dft_shift_control_def:
  (dft_shift_control delta (DftEnter fn b s) = DftEnter fn (b+delta) s) /\
  (dft_shift_control delta (DftAt fn b bb s) = DftAt fn (b+delta) bb s) /\
  (dft_shift_control delta (DftDone r) = DftDone r)
End

Definition dft_shift_config_def:
  dft_shift_config delta (DftOpen control stack n) =
    DftOpen (dft_shift_control delta control) (MAP (dft_shift_frame delta) stack) n
End

Definition dft_zero_entry_def:
  dft_zero_entry c <=> ?fn s stack n. c = DftOpen (DftEnter fn 0 s) stack n
End

Theorem dft_shift_continue[local]:
  dft_open_continue fn (b+delta) bb inst before after =
  dft_shift_control delta (dft_open_continue fn b bb inst before after)
Proof
  simp[dft_open_continue_def] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[dft_shift_control_def] >>
  Cases_on `after.vs_halted` >> simp[dft_shift_control_def]
QED

Theorem dft_shift_deliver[local]:
  dft_open_deliver fn (b+delta) bb inst before
    (MAP (dft_shift_frame delta) stack) n r =
  dft_shift_config delta (dft_open_deliver fn b bb inst before stack n r)
Proof
  Cases_on `r` >>
  simp[dft_open_deliver_def, dft_shift_config_def, dft_shift_control_def,
       dft_shift_continue]
QED

Theorem dft_shift_return[local]:
  dft_open_return r (MAP (dft_shift_frame delta) stack) n =
  dft_shift_config delta (dft_open_return r stack n)
Proof
  Cases_on `r` >> Cases_on `stack` >>
  simp[dft_open_return_def, dft_shift_config_def, dft_shift_control_def] >>
  Cases_on `h` >>
  simp[dft_shift_frame_def, dft_open_return_def] >>
  rename1 `bind_outputs call.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs))` >>
  Cases_on `bind_outputs call.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs))` >>
  simp[dft_shift_config_def, dft_shift_control_def] >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule dft_shift_deliver
QED

Theorem dft_shift_invoke[local]:
  dft_open_invoke ctx fn (b+delta) bb inst s
    (MAP (dft_shift_frame delta) stack) n =
  dft_shift_config delta (dft_open_invoke ctx fn b bb inst s stack n)
Proof
  simp[dft_open_invoke_def] >>
  Cases_on `decode_invoke inst` >>
  simp[dft_shift_config_def, dft_shift_control_def] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `lookup_function x0 ctx.ctx_functions` >>
  simp[dft_shift_config_def, dft_shift_control_def] >>
  Cases_on `eval_operands x1 s` >>
  simp[dft_shift_config_def, dft_shift_control_def] >>
  rename1 `setup_callee callee args s` >>
  Cases_on `setup_callee callee args s` >>
  simp[dft_shift_config_def, dft_shift_control_def, dft_shift_frame_def]
QED

Theorem dft_shift_next:
  ~dft_zero_entry c ==>
  dft_open_next a ctx (dft_shift_config delta c) =
  dft_shift_config delta (dft_open_next a ctx c)
Proof
  Cases_on `c` >> Cases_on `d` >>
  simp[dft_zero_entry_def, dft_shift_config_def, dft_shift_control_def,
       dft_open_next_def, dft_shift_return]
  >- (Cases_on `n'` >> simp[arithmeticTheory.ADD_CLAUSES] >>
      Cases_on `lookup_block v.vs_current_bb i.fn_blocks` >>
      simp[dft_shift_config_def, dft_shift_control_def] >>
      rename1 `eval_phis s bb.bb_instructions` >>
      Cases_on `eval_phis s bb.bb_instructions` >>
      simp[dft_shift_config_def, dft_shift_control_def]) >>
  Cases_on `get_instruction b v.vs_inst_idx` >>
  simp[dft_shift_config_def, dft_shift_control_def] >>
  rename1 `inst.inst_opcode = INVOKE` >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (asm_rewrite_tac[] >> once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
      irule dft_shift_invoke) >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  Cases_on `inst.inst_opcode = GAS` >>
  asm_rewrite_tac[dft_shift_deliver] >>
  Cases_on `inst.inst_outputs` >>
  simp[dft_shift_config_def, dft_shift_control_def] >>
  Cases_on `t` >> simp[dft_shift_deliver, dft_shift_config_def, dft_shift_control_def]
QED

Theorem dft_error_iterations[local]:
  FUNPOW (dft_open_next a ctx) j (DftOpen (DftDone (Error e)) [] n) =
  DftOpen (DftDone (Error e)) [] n
Proof
  Induct_on `j` >> simp[FUNPOW, dft_open_next_def, dft_open_return_def]
QED

Theorem dft_zero_entry_no_active[local]:
  dft_zero_entry c ==>
  FUNPOW (dft_open_next a ctx) j c <> DftOpen (DftAt fn b bb s) stack n
Proof
  Cases_on `j` >> simp[FUNPOW, dft_zero_entry_def] >>
  rpt strip_tac >> gvs[dft_open_next_def, dft_error_iterations]
QED

Theorem dft_shift_active:
  !j c fn b bb s stack n.
  FUNPOW (dft_open_next a ctx) j c = DftOpen (DftAt fn b bb s) stack n ==>
  FUNPOW (dft_open_next a ctx) j (dft_shift_config delta c) =
    DftOpen (DftAt fn (b+delta) bb s) (MAP (dft_shift_frame delta) stack) n
Proof
  Induct_on `j`
  >- (simp[dft_shift_config_def, dft_shift_control_def]) >>
  rpt gen_tac >> rewrite_tac[FUNPOW] >> strip_tac >>
  `~dft_zero_entry c` by metis_tac[dft_zero_entry_no_active, FUNPOW] >>
  asm_simp_tac bool_ss [dft_shift_next] >>
  first_x_assum irule >> simp[]
QED

Theorem dft_shift_observe:
  dft_open_observe fn inst s (FUNPOW (dft_open_next a ctx) j c) ==>
  dft_open_observe fn inst s
    (FUNPOW (dft_open_next a ctx) j (dft_shift_config delta c))
Proof
  simp[dft_open_observe_def] >> rpt strip_tac >>
  drule dft_shift_active >> strip_tac >>
  metis_tac[]
QED
