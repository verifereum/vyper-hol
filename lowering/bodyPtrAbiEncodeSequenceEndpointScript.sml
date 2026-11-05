(* Check transport for capped straight-line execution. *)
Theory bodyPtrAbiEncodeSequenceEndpoint
Ancestors
  ptrSafeRun ptrDiscipline contextCodegenRel venomExecSemantics venomState
  venomInst venomExecProofs venomInstProofs fragGasPathPtr fragGasSeqPtr
  fragExec gasCount exprLoweringProps instIdxIndep list rich_list arithmetic

Theorem ptr_safe_step_no_exemption_transport:
  inst.inst_opcode <> INVOKE /\ ~in_revert_forward fn0 s /\
  ~about_to_revert fn0 inst s /\
  ptr_safe_step D lo fuel ctx fn0 PG G tn inst s ==>
  ptr_safe_step D lo fuel ctx fn PG G tn inst s
Proof
  simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def] >>
  metis_tac[]
QED

Theorem block_no_revert_instruction:
  EVERY (\inst. inst.inst_opcode <> REVERT) bb.bb_instructions /\
  get_instruction bb k = SOME inst ==> inst.inst_opcode <> REVERT
Proof
  simp[get_instruction_def, EVERY_MEM] >> strip_tac >>
  Cases_on `k < LENGTH bb.bb_instructions` >> gvs[] >>
  metis_tac[MEM_EL]
QED

Theorem block_no_revert_forward:
  EVERY (\inst. inst.inst_opcode <> REVERT) bb.bb_instructions ==>
  ~revert_forward_at bb k
Proof
  simp[revert_forward_at_def, revert_forward_pair_def] >>
  metis_tac[block_no_revert_instruction]
QED

Theorem function_block_no_revert_exemptions:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  EVERY (\b. EVERY (\i. i.inst_opcode <> REVERT) b.bb_instructions) fn.fn_blocks /\
  inst.inst_opcode <> REVERT ==>
  ~in_revert_forward fn s /\ ~about_to_revert fn inst s
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_def, FIND_MEM] >>
  `EVERY (\i. i.inst_opcode <> REVERT) bb.bb_instructions` by
    (qpat_x_assum `EVERY _ fn.fn_blocks` mp_tac >>
     simp_tac bool_ss [EVERY_MEM] >> disch_then (qspec_then `bb` mp_tac) >> simp[]) >>
  conj_tac
  >- (simp[in_revert_forward_def] >> metis_tac[block_no_revert_forward]) >>
  simp[about_to_revert_def, active_inst_def] >>
  fs[EVERY_MEM] >> metis_tac[MEM_EL]
QED

Theorem nonterminating_code_no_revert:
  EVERY (\i. ~is_terminator i.inst_opcode) xs ==>
  EVERY (\i. i.inst_opcode <> REVERT) xs
Proof
  simp_tac bool_ss [EVERY_MEM] >> rpt strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[is_terminator_def]
QED

Theorem padded_singleton_no_revert_exemptions:
  fn.fn_blocks = [bb] /\ bb.bb_label = s.vs_current_bb /\
  bb.bb_instructions = REPLICATE start pad ++ xs /\
  pad.inst_opcode <> REVERT /\
  EVERY (\i. ~is_terminator i.inst_opcode) xs /\
  inst.inst_opcode <> REVERT ==>
  ~in_revert_forward fn s /\ ~about_to_revert fn inst s
Proof
  strip_tac >> irule function_block_no_revert_exemptions >>
  simp[lookup_block_def, FIND_thm, EVERY_REPLICATE] >>
  metis_tac[nonterminating_code_no_revert]
QED

Theorem gas_ptr_normal_edge_sequence:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  gas_path_ptr_edge D lo ctx fn PG G tn s n H un (OK t) ==>
  ?u. step_inst_base i s = OK u /\
    t = u with vs_inst_idx := SUC s.vs_inst_idx /\
    H = step_prov PG G i u /\ un = step_taint i s u tn /\
    ptr_inst_ok D lo 0 ctx fn G tn i s /\
    n = (if i.inst_opcode = GAS then 1 else 0)
Proof
  simp_tac bool_ss [gas_path_ptr_edge_def] >> rpt strip_tac >>
  gvs[exit_result_def, step_inst_non_invoke, ghost_step_non_invoke,
    gas_count_step_def, ptr_safe_step_def, ptr_inst_ok_def]
  >- (qpat_x_assum `(H,un) = _` mp_tac >>
      simp[ghost_step_def, step_inst_non_invoke]) >>
  qpat_x_assum `OK _ = step_inst_base _ _` (assume_tac o SYM) >>
  gvs[exit_result_def]
QED

Theorem capped_sequence_endpoint:
  !xs s fn bb D lo ctx PG G tn n H un t u.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    DROP s.vs_inst_idx bb.bb_instructions = xs /\
    LENGTH bb.bb_instructions = s.vs_inst_idx + LENGTH xs /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) xs /\
    gas_path_ptr D lo ctx fn PG G tn s n H un (OK t) /\
    t.vs_inst_idx = s.vs_inst_idx + LENGTH xs /\
    run_inst_seq xs s = OK u ==>
    t = u with vs_inst_idx := s.vs_inst_idx + LENGTH xs
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[Once gas_path_ptr_cases, exit_result_def] >> strip_tac >>
      gvs[run_inst_seq_def, gas_path_ptr_edge_def, get_instruction_def]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[Once gas_path_ptr_cases, exit_result_def] >> strip_tac
  >- gvs[] >>
  `get_instruction bb s.vs_inst_idx = SOME h` by
    (gvs[get_instruction_def] >>
     qpat_x_assum `DROP _ _ = _` mp_tac >>
     simp[DROP_EL_CONS]) >>
  fs[EVERY_DEF] >>
  drule_all gas_ptr_normal_edge_sequence >> strip_tac >>
  gvs[run_inst_seq_def] >>
  `u'.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow, step_inst_non_invoke] >>
  `DROP (SUC s.vs_inst_idx) bb.bb_instructions = xs` by
    (qpat_x_assum `DROP _ _ = h::xs` (mp_tac o AP_TERM ``DROP 1 : instruction list -> instruction list``) >>
     simp[DROP_DROP, ADD1]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) xs` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `!s fn bb D lo ctx PG G tn n H un t u. _` mp_tac >>
  disch_then (qspec_then `u' with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[run_inst_seq_inst_idx, exec_result_map_def, ADD_CLAUSES] >>
  disch_then drule >> simp[] >>
  disch_then drule >> simp[] >>
  disch_then drule >> simp[]
QED

Theorem normal_edge_function_transport:
  lookup_block s.vs_current_bb fn0.fn_blocks = SOME bb0 /\
  get_instruction bb0 s.vs_inst_idx = SOME i /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  ~in_revert_forward fn0 s /\ ~about_to_revert fn0 i s /\
  gas_path_ptr_edge D lo ctx fn0 PG G tn s n H un (OK t) ==>
  gas_path_ptr_edge D lo ctx fn PG G tn s n H un (OK t)
Proof
  simp_tac bool_ss [gas_path_ptr_edge_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[ptr_safe_step_no_exemption_transport]
QED

Theorem capped_sequence_transport:
  !xs s fn0 bb0 fn bb D lo ctx PG G tn n H un t.
    lookup_block s.vs_current_bb fn0.fn_blocks = SOME bb0 /\
    DROP s.vs_inst_idx bb0.bb_instructions = xs /\
    LENGTH bb0.bb_instructions = s.vs_inst_idx + LENGTH xs /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) xs /\
    EVERY (\b. EVERY (\i. i.inst_opcode <> REVERT) b.bb_instructions) fn0.fn_blocks /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX xs (DROP s.vs_inst_idx bb.bb_instructions) /\
    gas_path_ptr D lo ctx fn0 PG G tn s n H un (OK t) ==>
    gas_path_ptr D lo ctx fn PG G tn s n H un (OK t)
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`
        (strip_assume_tac o ONCE_REWRITE_RULE [gas_path_ptr_cases])
      >- (gvs[] >> irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
      gvs[gas_path_ptr_edge_def, get_instruction_def]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_path_ptr_cases])
  >- (gvs[] >> irule (cj 1 gas_path_ptr_rules) >> simp[])
  >~ [`exit_result (OK _)`] >- gvs[exit_result_def] >>
  fs[EVERY_DEF] >>
  `get_instruction bb0 s.vs_inst_idx = SOME h` by
    (gvs[get_instruction_def] >>
     qpat_x_assum `DROP _ _ = _` mp_tac >> simp[DROP_EL_CONS]) >>
  `?rest. DROP s.vs_inst_idx bb.bb_instructions = h::rest /\
          isPREFIX xs rest` by
    (Cases_on `DROP s.vs_inst_idx bb.bb_instructions` >> gvs[]) >>
  `get_instruction bb s.vs_inst_idx = SOME h` by
    (qpat_x_assum `DROP _ bb.bb_instructions = _` mp_tac >>
     Cases_on `s.vs_inst_idx < LENGTH bb.bb_instructions` >>
     simp[get_instruction_def, DROP_EL_CONS, DROP_LENGTH_TOO_LONG]) >>
  `h.inst_opcode <> REVERT` by
    (strip_tac >> gvs[is_terminator_def]) >>
  drule_all function_block_no_revert_exemptions >> strip_tac >>
  `gas_path_ptr_edge D lo ctx fn PG G tn s n' G1 tn1 (OK t')` by
    (irule normal_edge_function_transport >> metis_tac[]) >>
  drule_all gas_ptr_normal_edge_sequence >> strip_tac >>
  `u.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow, step_inst_non_invoke] >>
  `DROP (SUC s.vs_inst_idx) bb0.bb_instructions = xs` by
    (qpat_x_assum `DROP _ bb0.bb_instructions = _`
      (mp_tac o AP_TERM ``DROP 1 : instruction list -> instruction list``) >>
     simp[DROP_DROP, ADD1]) >>
  `DROP (SUC s.vs_inst_idx) bb.bb_instructions = rest` by
    (qpat_x_assum `DROP _ bb.bb_instructions = _`
      (mp_tac o AP_TERM ``DROP 1 : instruction list -> instruction list``) >>
     fs[get_instruction_def, DROP_DROP, ADD1]) >>
  `gas_path_ptr D lo ctx fn PG G1 tn1 t' m H un (OK t)` by
    (first_x_assum irule >> simp[] >>
     qexistsl [`bb0`, `fn0`] >> gvs[ADD_CLAUSES]) >>
  metis_tac[cj 2 gas_path_ptr_rules, ADD_COMM]
QED
