(* Canonical bytes-array execution inside an independently based owner. *)
Theory entryReachBodyOwnedBytesArray
Ancestors
  entryReachBodyOwnedBytesChild entryReachBodyOwnedLoop
  entryReachBodyOwnedRegion entryReachBodyOperationalPath
  entryReachBodySequenceObservations entryReachBodyArrayInit entryReachBodyExactArrayLoop
  abiAllocationHistory allocaFrontierBound allocaBudgetProps
  abiEncoderRegisteredEffect abiDecoderArrayInit abiDecoderLoopSetup
  abiDecoderContract abiDecodeRanges fragExec venomExecProofs venomInstProps exprLoweringProps
  venomExecSemantics venomMemDefs venomState finite_map words pred_set list arithmetic instIdxIndep

(* The initializer's actual endpoint retains the enclosing allocation, even
   when the array count is stored strictly inside it. *)
Theorem owned_array_initializer[local]:
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
  alloca_inv initial /\ ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  abi_decode_load CALLDATALOAD srcword initial = n2w ncount /\ ncount <= maxn /\
  abi_alloca_history (fn_insts fn) initial /\ fn_has_code st loop_st fn /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  entry_owned_region oid root extent d sz initial /\ oid <> header_st.cs_next_id ==>
  ?t. entry_decode_path ctx fn initial t /\
    entry_owned_loop_resources ctx fn site header_st.cs_next_id p oid root extent d sz t /\
    abi_encoder_registered_effect {header_st.cs_next_id} [(d,32)] initial t /\
    eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
    eval_operand cnt t = SOME (n2w ncount) /\ mem_word_at d t.vs_memory = n2w ncount /\
    entry_loop_fields initial t /\ ~t.vs_halted /\
    t.vs_current_bb = loop_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op t = eval_operand op initial)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  SUBGOAL_THEN ``d+sz <= p \/ p+32 <= d`` assume_tac
  >- (drule entry_owned_region_counter_separation >>
      disch_then (qspecl_then [`p`,`header_st.cs_next_id`] mp_tac) >> simp[] >> metis_tac[]) >>
  drule_all entry_array_init_operational >>
  disch_then (qx_choose_then `prepared` strip_assume_tac) >>
  `entry_owned_region oid root extent d sz prepared` by
    (irule entry_owned_region_preserved >>
     goal_assum (drule_at Any) >> simp[]) >>
  `prepared.vs_current_bb = loop_st.cs_current_bb /\
   prepared.vs_call_ctx = initial.vs_call_ctx /\
   prepared.vs_data_section = initial.vs_data_section` by
    suspend "control" >>
  `remaining_alloca_budget (fn_insts fn)
      (prepared with vs_inst_idx := LENGTH loop_st.cs_current_insts) =
    remaining_alloca_budget (fn_insts fn) prepared` by
    (irule remaining_alloca_budget_domain_cong >> simp[]) >>
  `entry_owned_loop_resources ctx fn site header_st.cs_next_id p oid root extent d sz prepared` by
    simp[entry_owned_loop_resources_def] >>
  qexists_tac `prepared with vs_inst_idx := LENGTH loop_st.cs_current_insts` >>
  suspend "pc_frame"
QED

Resume owned_array_initializer[control]:
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  `prepared.vs_current_bb = initial.vs_current_bb` by
    (irule run_inst_seq_preserves_field >>
     qexists_tac `emitted_insts st loop_st` >> asm_rewrite_tac[] >>
     rpt strip_tac >> fs[EVERY_MEM] >>
     metis_tac[step_preserves_control_flow, step_inst_non_invoke]) >>
  simp[] >> conj_tac >> irule run_inst_seq_preserves_field >>
  qexists_tac `emitted_insts st loop_st` >> asm_rewrite_tac[] >>
  rpt strip_tac >> fs[EVERY_MEM] >>
  metis_tac[step_preserves_call_ctx, step_preserves_data_section, step_inst_non_invoke]
QED
Resume owned_array_initializer[pc_frame]:
  map_every (fn q => qpat_x_assum q kall_tac)
    [`abi_decode_array_loop_init _ _ _ _ _ _ _ = _`,
     `abi_decode_dynarray_prefix _ _ _ _ _ _ = _`,
     `abi_decode_array_header _ _ _ _ = _`, `abi_decode_index_init _ = _`,
     `eval_operand src initial = _`, `eval_operand dst initial = _`,
     `!i. MEM i (emitted_insts _ _) ==> _`,
     `FLOOKUP initial.vs_allocas _ = NONE /\ _ \/ _`,
     `alloca_inv initial`, `alloca_frontier_inv _ _ _ initial`,
     `abi_alloca_history _ initial`, `fn_has_code _ _ _`,
     `run_inst_seq _ initial = _`, `entry_owned_region _ _ _ _ _ initial`,
     `d+sz <= p \/ p+32 <= d`,
     `!id. id <> _ ==> _`, `if _ then _ else _`,
     `abi_decode_footprint_frame _ _ _`] >>
  fs[entry_owned_loop_resources_def, entry_owned_region_def,
     abi_encoder_registered_effect_def, entry_loop_fields_def,
     alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
     abi_alloca_history_def, alloca_frontier_inv_def, eval_op_inst_idx, mload_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise owned_array_initializer
