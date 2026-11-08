Theory entryReachBodyOperationalHeader
Ancestors
  entryReachBodyOperationalPath entryReachBodyOperationalLoop
  abiEncoderObserver abiDecoderExecution abiDecoderContract
  venomExecSemantics venomExecProofs venomInst venomState
  words list rich_list exprLoweringProps venomInstProps
  abiDecoderDynarrayPrefix abiDecoderArrayHeader abiDecoderIndexInit
  abiDecoderArrayLoopInit emitHelperProps
  allocaFrontierBound allocaBudgetProps abiAllocationHistory venomMemDefs
  abiEncoderRegisteredEffect entryReachBodyExactArrayLoop

Theorem entry_initializer_header_jump_path:
  ~prepared.vs_halted /\ prepared.vs_current_bb = loop_st.cs_current_bb /\
  lookup_block loop_st.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := loop_st.cs_current_bb; bb_instructions :=
      loop_st.cs_current_insts ++ [mk_inst loop_st.cs_next_id JMP [Label hdr] []]|> /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 ==>
  entry_decode_path ctx fn
    (prepared with vs_inst_idx := LENGTH loop_st.cs_current_insts)
    (jump_to hdr prepared)
Proof
  strip_tac >> irule entry_decode_path_step >>
  qexists_tac `(loop_st.cs_current_bb,SUC (LENGTH loop_st.cs_current_insts))` >>
  simp[abi_observer_step_def, jump_to_def] >>
  qexistsl_tac [`mk_inst loop_st.cs_next_id JMP [Label hdr] []`, `jump_to hdr prepared`] >>
  simp[mk_inst_def, get_instruction_def, EL_APPEND_EQN, is_terminator_def,
    step_inst_non_invoke, step_inst_base_opcode_eqs, jump_to_def] >>
  once_rewrite_tac[GSYM eval_phis_prefix] >> simp[eval_phis_def]
QED

Theorem initializer_header_ready[local]:
  ~prepared.vs_halted /\ eval_operand ip prepared = SOME (n2w p) /\
  eval_operand src prepared = SOME srcaddr /\ mload p prepared = 0w /\
  abi_decode_load CALLDATALOAD srcaddr prepared = n2w n /\ p < dimword (:256) ==>
  abi_decode_loop_ready hdr ip src CALLDATALOAD (n2w p) srcaddr n 0
    (jump_to hdr prepared)
Proof
  simp[abi_decode_loop_ready_def, jump_to_def, eval_operand_def, lookup_var_def,
    abi_decode_load_def, abi_decode_source_def, mload_def]
QED

Theorem header_jump_resources[local]:
  entry_operational_loop_resources ctx fn site cid p oid d cap prepared ==>
  entry_operational_loop_resources ctx fn site cid p oid d cap (jump_to hdr prepared)
Proof
  strip_tac >>
  `remaining_alloca_budget (fn_insts fn) (jump_to hdr prepared) =
   remaining_alloca_budget (fn_insts fn) prepared` by
    (irule remaining_alloca_budget_domain_cong >> simp[jump_to_def]) >>
  fs[entry_operational_loop_resources_def, alloca_frontier_inv_def,
    abi_alloca_history_def, alloca_inv_def, allocas_non_overlapping_def,
    alloca_next_valid_def, jump_to_def] >> metis_tac[]
QED

Theorem entry_initializer_ready_header_boundary:
  ~prepared.vs_halted /\ prepared.vs_current_bb = loop_st.cs_current_bb /\
  lookup_block loop_st.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := loop_st.cs_current_bb; bb_instructions :=
      loop_st.cs_current_insts ++ [mk_inst loop_st.cs_next_id JMP [Label hdr] []]|> /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  entry_decode_path ctx fn initial
    (prepared with vs_inst_idx := LENGTH loop_st.cs_current_insts) /\
  entry_loop_fields initial prepared /\
  entry_operational_loop_resources ctx fn site cid p oid d cap prepared /\
  abi_encoder_registered_effect ids [(d,32+LENGTH xs*type_memory_size tv)] initial prepared /\
  eval_operand ip prepared = SOME (n2w p) /\ eval_operand src prepared = SOME srcaddr /\
  mload p prepared = 0w /\ abi_decode_load CALLDATALOAD srcaddr prepared = n2w (LENGTH xs) /\
  p < dimword (:256) ==>
  entry_operational_loop_inv ctx fn site hdr ip src (n2w p) srcaddr tv xs d cap cid oid 0
    (jump_to hdr prepared) /\
  entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)] initial (jump_to hdr prepared)
Proof
  strip_tac >> conj_tac
  >- (simp_tac bool_ss [entry_operational_loop_inv_def] >> rpt conj_tac
      >- (irule initializer_header_ready >> simp[])
      >- (simp[] >> irule header_jump_resources >> simp[]) >>
      simp[entry_loop_prefix_def]) >>
  simp_tac bool_ss [entry_loop_trace_def] >> conj_tac
  >- fs[entry_loop_fields_def, jump_to_def] >> conj_tac
  >- (irule entry_decode_path_trans >>
      qexists_tac `prepared with vs_inst_idx := LENGTH loop_st.cs_current_insts` >>
      asm_rewrite_tac[] >> irule entry_initializer_header_jump_path >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  gvs[abi_encoder_registered_effect_def, jump_to_def] >> metis_tac[]
QED

Theorem entry_sequence_input_fields:
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
  run_inst_seq code s = OK t ==>
  t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_data_section = s.vs_data_section /\
  t.vs_current_bb = s.vs_current_bb
Proof
  strip_tac >> rpt conj_tac >>
  irule run_inst_seq_preserves_field >> goal_assum (drule_at Any) >>
  rpt strip_tac >> fs[EVERY_MEM] >>
  metis_tac[step_inst_non_invoke, step_preserves_call_ctx,
    step_preserves_data_section, step_preserves_control_flow]
QED

Theorem entry_initializer_input_fields:
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st = ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  run_inst_seq (emitted_insts st loop_st) s = OK t ==>
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
  t.vs_current_bb = s.vs_current_bb /\ loop_st.cs_current_bb = st.cs_current_bb
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `inst_extends st header_st` by metis_tac[inst_extends_trans] >>
  `emitted_insts st loop_st = emitted_insts st header_st ++
      emitted_insts header_st loop_st` by
    metis_tac[emitted_insts_append, inst_extends_def] >>
  `emitted_insts st header_st = emitted_insts st guard_st ++
      emitted_insts guard_st header_st` by
    metis_tac[emitted_insts_append, inst_extends_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st loop_st)` by (fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all entry_sequence_input_fields >> simp[]
QED

Theorem entry_array_initializer_header_path:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st = ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  eval_operand src initial = SOME srcword /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  maxn < dimword (:256) /\ d < dimword (:256) /\
  32 <= sz /\ d+sz <= initial.vs_alloca_next /\
  alloca_frontier_inv ctx fn site initial /\ unit_alloca_budget ctx < dimword (:256) /\
  (!i. MEM i (emitted_insts st loop_st) ==> MEM i (fn_insts fn)) /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
   (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
  (d+sz <= p \/ p+32 <= d) /\ alloca_inv initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  abi_decode_load CALLDATALOAD srcword initial = n2w (LENGTH xs) /\ LENGTH xs <= maxn /\
  abi_alloca_history (fn_insts fn) initial /\ fn_has_code st loop_st fn /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  FLOOKUP initial.vs_allocas oid = SOME (d,cap) /\ header_st.cs_next_id IN ids /\
  lookup_block loop_st.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := loop_st.cs_current_bb; bb_instructions :=
      loop_st.cs_current_insts ++ [mk_inst loop_st.cs_next_id JMP [Label hdr] []]|> /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 ==>
  ?prepared.
    run_inst_seq (emitted_insts st loop_st) initial = OK prepared /\
    entry_operational_loop_inv ctx fn site hdr ip src (n2w p) srcword tv xs d cap
      header_st.cs_next_id oid 0 (jump_to hdr prepared) /\
    entry_loop_trace ctx fn ids [(d,32+LENGTH xs*type_memory_size tv)]
      initial (jump_to hdr prepared)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all entry_array_init_operational >> strip_tac >>
  drule_all entry_initializer_input_fields >> strip_tac >>
  `entry_loop_fields initial t` by simp[entry_loop_fields_def] >>
  `p < dimword (:256)` by
    (`initial.vs_alloca_next < dimword (:256)` by
       metis_tac[alloca_frontier_inv_bound] >>
     qpat_x_assum `(_ /\ p = _) \/ _` strip_assume_tac >> simp[]) >>
  `abi_decode_load CALLDATALOAD srcword t = n2w (LENGTH xs)` by
    (qpat_x_assum `abi_decode_load CALLDATALOAD srcword initial = _` mp_tac >>
     simp[abi_decode_load_def, abi_decode_source_def]) >>
  drule_all entry_operational_loop_initializer_resources >>
  disch_then (qspecl_then [`xs`, `tv`, `t.vs_inst_idx`] mp_tac) >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  qexists_tac `t` >> conj_tac >- first_assum ACCEPT_TAC >>
  irule entry_initializer_ready_header_boundary >>
  goal_assum (drule_at Any) >> simp[] >> qexists_tac `loop_st` >> simp[]
QED
