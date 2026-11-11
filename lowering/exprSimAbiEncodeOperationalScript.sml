Theory exprSimAbiEncodeOperational
Ancestors
  abiEncoderWindowPhase abiEncoderObserver instIdxIndep venomStepProps
  venomInstProps emitHelperProps list arithmetic venomExecSemantics
  compileEnv venomState exprLoweringProps abiEncoderWindowSequence
  fragExec rich_list venomInst

(* A straight-line sequence reaches its first end cut.  No claim about
   composition across different cuts is used here. *)
Theorem abi_encode_seq_prefix:
  !code s raw bb idx ctx fn.
    run_inst_seq code s = OK raw /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    (!k. k < LENGTH code ==> get_instruction bb (idx+k) = SOME (EL k code)) ==>
    local_prefix ctx fn (s.vs_current_bb,idx+LENGTH code)
      (s with vs_inst_idx := idx)
      (raw with vs_inst_idx := idx+LENGTH code)
Proof
  Induct_on `code`
  >- (simp[run_inst_seq_def] >> rpt strip_tac >>
      irule (cj 1 local_prefix_rules) >> simp[]) >>
  rpt gen_tac >> simp_tac bool_ss [run_inst_seq_def, EVERY_DEF, LENGTH] >>
  strip_tac >> Cases_on `step_inst_base h s` >>
  gvs[exec_result_case_def, exec_result_distinct, exec_result_11] >>
  rename1 `step_inst_base h s = OK middle` >>
  `middle.vs_halted = s.vs_halted` by metis_tac[step_inst_base_ok_halted] >>
  `middle.vs_current_bb = s.vs_current_bb` by
    (`step_inst 0 ctx h s = OK middle` by simp[step_inst_non_invoke] >>
     drule_all step_preserves_control_flow >> simp[]) >>
  `get_instruction bb idx = SOME h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `!k. k < LENGTH code ==>
    get_instruction bb (SUC idx+k) = SOME (EL k code)` by
    (rpt strip_tac >> first_x_assum (qspec_then `SUC k` mp_tac) >> simp[ADD_CLAUSES, ADD_COMM]) >>
  irule (cj 2 local_prefix_rules) >>
  qexists `middle with vs_inst_idx := SUC idx` >> conj_tac
  >- (simp[abi_observer_step_def, step_inst_non_invoke,
       step_inst_inst_idx_indep, exec_result_map_def]) >>
  first_x_assum (qspecl_then [`middle`, `raw`, `bb`, `SUC idx`, `ctx`, `fn`] mp_tac) >>
  simp[ADD_CLAUSES]
QED

Theorem abi_encode_window_seq_prefix:
  window_seq st en s raw /\ fn_has_code st en fn /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  local_prefix ctx fn (en.cs_current_bb,LENGTH en.cs_current_insts)
    s (raw with vs_inst_idx := LENGTH en.cs_current_insts)
Proof
  simp_tac bool_ss [window_seq_def, fn_has_code_def, inst_extends_def] >>
  strip_tac >>
  `?tail. en.cs_current_insts = st.cs_current_insts ++ tail` by
    metis_tac[] >>
  `emitted_insts st en = tail` by
    simp[emitted_insts_def, emitted_blocks_def, DROP_APPEND] >>
  `!k. k < LENGTH tail ==>
     get_instruction bb (LENGTH st.cs_current_insts+k) = SOME (EL k tail)` by
    (gvs[IS_PREFIX_APPEND] >> rpt strip_tac >>
     simp[get_instruction_def, EL_APPEND1, EL_APPEND2]) >>
  drule abi_encode_seq_prefix >>
  disch_then (qspecl_then [`bb`, `LENGTH st.cs_current_insts`, `ctx`, `fn`] mp_tac) >>
  `s with vs_inst_idx := LENGTH st.cs_current_insts = s` by
    simp[venom_state_component_equality] >>
  gvs[]
QED

Theorem abi_encode_window_seq_phase_prefix:
  window_seq st en s raw /\ fn_has_code st en fn /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_registered_effect ids outs s raw /\ window_alloca_growth s raw /\
  alloca_inv raw /\ alloca_room ctx fn raw /\
  raw.vs_halted = s.vs_halted /\ raw.vs_current_bb = s.vs_current_bb ==>
  window_phase ctx fn st en ids outs s
    (raw with vs_inst_idx := LENGTH en.cs_current_insts) /\
  local_prefix ctx fn (en.cs_current_bb,LENGTH en.cs_current_insts)
    s (raw with vs_inst_idx := LENGTH en.cs_current_insts)
Proof
  strip_tac >> conj_tac
  >- (irule window_seq_phase >> metis_tac[]) >>
  irule abi_encode_window_seq_prefix >> metis_tac[]
QED
