Theory entryReachBodyOperationalPath
Ancestors
  valueEncodingDefs abiEncoderObserver abiAllocationHistory allocaFrontierBound
  entryReachBodyArrayInit abiEncoderRegisteredEffect abiDecoderFrame
  abiDecoderArrayLoopInit abiDecoderIndexInit abiDecoderContract compileEnv emitHelperProps
  abiDecoderLoop contextCodegenRel venomExecProofs venomInst venomInstProofs1 venomInstProofs venomExecSemantics emitHelper phiTransform fragExec exprLoweringProps instIdxIndep rich_list relation

Definition entry_decode_step_def:
  entry_decode_step ctx fn s t <=> ?cut. abi_observer_step ctx fn cut s t
End

Definition entry_decode_path_def:
  entry_decode_path ctx fn = RTC (entry_decode_step ctx fn)
End

Theorem entry_decode_path_refl:
  entry_decode_path ctx fn s s
Proof
  simp[entry_decode_path_def]
QED

Theorem entry_decode_path_trans:
  entry_decode_path ctx fn s t /\ entry_decode_path ctx fn t u ==>
  entry_decode_path ctx fn s u
Proof
  metis_tac[entry_decode_path_def, RTC_TRANSITIVE, transitive_def]
QED

Theorem entry_decode_path_sim:
  !s t. entry_decode_path ctx fn s t ==> abi_decode_sim ctx fn s t
Proof
  rewrite_tac[entry_decode_path_def] >> ho_match_mp_tac RTC_INDUCT >>
  rpt strip_tac >- simp[abi_decode_sim_refl] >>
  fs[entry_decode_step_def] >> drule abi_observer_step_sim >>
  strip_tac >> drule_all abi_decode_sim_trans >> simp[]
QED

Theorem observer_step_history[local]:
  abi_observer_step ctx fn cut s t /\
  abi_alloca_history (fn_insts fn) s ==>
  abi_alloca_history (fn_insts fn) t
Proof
  rw[abi_observer_step_def] >>
  `MEM inst (fn_insts fn)` by
    (irule abi_alloca_history_fn_member >> qexists_tac `bb` >>
     fs[get_instruction_def] >>
     metis_tac[lookup_block_MEM, listTheory.EL_MEM]) >>
  drule_all abi_alloca_history_step_inst >> strip_tac
  >- (irule abi_alloca_history_frame >> simp[] >> metis_tac[]) >>
  drule eval_phis_preserves_alloca_fields >> strip_tac >>
  irule abi_alloca_history_frame >> simp[] >> metis_tac[]
QED

Theorem entry_decode_path_history:
  !s t. entry_decode_path ctx fn s t ==>
    abi_alloca_history (fn_insts fn) s ==>
    abi_alloca_history (fn_insts fn) t
Proof
  rewrite_tac[entry_decode_path_def] >> ho_match_mp_tac RTC_INDUCT >>
  rpt strip_tac >> fs[entry_decode_step_def] >>
  drule_all observer_step_history >> strip_tac >>
  first_x_assum irule >> simp[]
QED

Theorem observer_step_frontier[local]:
  ctx_inst_ids_distinct ctx /\ abi_observer_step ctx fn cut s t /\
  alloca_frontier_inv ctx fn site s ==>
  alloca_frontier_inv ctx fn site' t
Proof
  rw[abi_observer_step_def] >>
  `MEM inst (fn_insts fn)` by
    (irule abi_alloca_history_fn_member >> qexists_tac `bb` >>
     fs[get_instruction_def] >> metis_tac[lookup_block_MEM, listTheory.EL_MEM]) >>
  `MEM fn ctx.ctx_functions` by
    metis_tac[alloca_frontier_inv_def, lookup_function_MEM] >>
  drule_all ctx_inst_ids_distinct_fn >> strip_tac >>
  drule_all step_inst_alloca_budget >> strip_tac
  >- (fs[alloca_frontier_inv_def] >>
      `remaining_alloca_budget (fn_insts fn)
         (middle with vs_inst_idx := SUC s.vs_inst_idx) =
       remaining_alloca_budget (fn_insts fn) middle` by
        (irule allocaBudgetPropsTheory.remaining_alloca_budget_domain_cong >> simp[]) >>
      simp[]) >>
  drule eval_phis_preserves_alloca_fields >> strip_tac >>
  `remaining_alloca_budget (fn_insts fn)
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions) =
   remaining_alloca_budget (fn_insts fn) middle` by
    (irule allocaBudgetPropsTheory.remaining_alloca_budget_domain_cong >> simp[]) >>
  `remaining_alloca_budget (fn_insts fn) entered =
   remaining_alloca_budget (fn_insts fn) middle` by
    (irule allocaBudgetPropsTheory.remaining_alloca_budget_domain_cong >> simp[]) >>
  fs[alloca_frontier_inv_def] >> decide_tac
QED

Theorem entry_decode_path_frontier:
  !s t. entry_decode_path ctx fn s t ==>
    !site site'. ctx_inst_ids_distinct ctx /\ alloca_frontier_inv ctx fn site s ==>
    alloca_frontier_inv ctx fn site' t
Proof
  rewrite_tac[entry_decode_path_def] >> ho_match_mp_tac RTC_INDUCT >>
  rpt strip_tac
  >- fs[alloca_frontier_inv_def] >>
  fs[entry_decode_step_def] >>
  drule_all observer_step_frontier >> strip_tac >>
  first_x_assum irule >> metis_tac[]
QED

Theorem entry_decode_path_step:
  abi_observer_step ctx fn cut s t ==> entry_decode_path ctx fn s t
Proof
  strip_tac >> rewrite_tac[entry_decode_path_def] >> irule RTC_SINGLE >>
  simp[entry_decode_step_def] >> metis_tac[]
QED

Theorem entry_decode_sequence_path:
  !insts s t bb.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX insts (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) insts /\
    ~s.vs_halted /\ run_inst_seq insts s = OK t ==>
    entry_decode_path ctx fn s
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH insts)
Proof
  Induct >> rpt gen_tac
  >- (simp[run_inst_seq_def] >> strip_tac >>
      gvs[] >> simp[entry_decode_path_refl]) >>
  strip_tac >> fs[run_inst_seq_def] >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  rename1 `step_inst_base h s = OK middle` >>
  `middle.vs_current_bb = s.vs_current_bb /\
   middle.vs_inst_idx = s.vs_inst_idx /\ ~middle.vs_halted` by
    metis_tac[step_preserves_control_flow, step_preserves_halted,
              step_inst_non_invoke] >>
  `?rest. DROP s.vs_inst_idx bb.bb_instructions = h :: rest /\
          isPREFIX insts rest` by
    (Cases_on `DROP s.vs_inst_idx bb.bb_instructions` >> gvs[]) >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   EL s.vs_inst_idx bb.bb_instructions = h /\
   DROP (SUC s.vs_inst_idx) bb.bb_instructions = rest` by
    ( `s.vs_inst_idx < LENGTH bb.bb_instructions` by
        (qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >> simp[]) >>
      metis_tac[rich_listTheory.DROP_CONS_EL, listTheory.CONS_11]) >>
  `entry_decode_path ctx fn s (middle with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule entry_decode_path_step >>
     qexists_tac `(s.vs_current_bb,SUC s.vs_inst_idx)` >>
     simp[abi_observer_step_def] >>
     qexistsl_tac [`h`, `middle`] >>
     simp[get_instruction_def, step_inst_non_invoke]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) insts` by fs[listTheory.EVERY_MEM] >>
  first_x_assum (qspecl_then
    [`middle with vs_inst_idx := SUC s.vs_inst_idx`,
     `t with vs_inst_idx := SUC s.vs_inst_idx`, `bb`] mp_tac) >>
  simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  strip_tac >> irule entry_decode_path_trans >>
  qexists_tac `middle with vs_inst_idx := SUC s.vs_inst_idx` >>
  fs[arithmeticTheory.ADD_CLAUSES]
QED

Theorem entry_decode_emitted_path:
  st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  fn_has_code st st' fn /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st') /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  entry_decode_path ctx fn s (t with vs_inst_idx := LENGTH st'.cs_current_insts)
Proof
  strip_tac >>
  `?bb. lookup_block st.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX st'.cs_current_insts bb.bb_instructions` by
    metis_tac[fn_has_code_def] >>
  `?xs. st'.cs_current_insts = st.cs_current_insts ++ xs /\
        emitted_insts st st' = xs` by
    (qpat_x_assum `isPREFIX st.cs_current_insts _` mp_tac >>
     simp[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
     simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND]) >>
  `isPREFIX xs (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX st'.cs_current_insts _` mp_tac >>
     simp[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
     simp[rich_listTheory.IS_PREFIX_APPEND] >>
     rewrite_tac[GSYM listTheory.APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     metis_tac[]) >>
  gvs[] >> metis_tac[entry_decode_sequence_path]
QED

Theorem initializer_registered_effect[local]:
  abi_decode_footprint_frame [(d,32);(p,32)] s t /\
  FLOOKUP t.vs_allocas id = SOME (p,32) /\
  (!i. i <> id ==> FLOOKUP t.vs_allocas i = FLOOKUP s.vs_allocas i) /\
  (FLOOKUP s.vs_allocas id = NONE \/ FLOOKUP s.vs_allocas id = SOME (p,32)) /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests /\
  t.vs_pending_deletions = s.vs_pending_deletions ==>
  abi_encoder_registered_effect {id} [(d,32)] s t
Proof
  simp_tac bool_ss [abi_encoder_registered_effect_def,
    abi_decode_footprint_frame_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> simp[]
  >- (Cases_on `i = id` >> gvs[]) 
  >- (gvs[])
  >> qpat_x_assum `!p n. abi_footprint_disjoint p n _ ==> _`
       (qspecl_then [`a`, `1`] mp_tac) >>
  impl_tac >- (
    `a < p \/ p+32 <= a` by
      (qpat_x_assum `!i b sz. _`
        (qspecl_then [`id`, `p`, `32`] mp_tac) >> simp[]) >>
    fs[abi_footprint_disjoint_def] >> rpt strip_tac >> gvs[] >> decide_tac) >>
  simp[]
QED

Theorem initializer_path_shape[local]:
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st = ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) ==>
  loop_st.cs_current_bb = st.cs_current_bb /\ inst_extends st loop_st /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st loop_st)
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `inst_extends st header_st` by metis_tac[inst_extends_trans] >>
  `emitted_insts st loop_st = emitted_insts st header_st ++
      emitted_insts header_st loop_st` by metis_tac[emitted_insts_append, inst_extends_def] >>
  `emitted_insts st header_st = emitted_insts st guard_st ++
      emitted_insts guard_st header_st` by metis_tac[emitted_insts_append, inst_extends_def] >>
  simp[] >> conj_tac >- metis_tac[inst_extends_trans] >>
  fs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem entry_array_init_operational:
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
  abi_decode_load CALLDATALOAD srcword initial = n2w ncount /\ ncount <= maxn /\
  abi_alloca_history (fn_insts fn) initial /\ fn_has_code st loop_st fn /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. run_inst_seq (emitted_insts st loop_st) initial = OK t /\
    entry_decode_path ctx fn initial (t with vs_inst_idx := LENGTH loop_st.cs_current_insts) /\
    abi_alloca_history (fn_insts fn) t /\
    abi_encoder_registered_effect {header_st.cs_next_id} [(d,32)] initial t /\
    eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
    eval_operand cnt t = SOME (n2w ncount) /\ mem_word_at d t.vs_memory = n2w ncount /\
    FLOOKUP t.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    (!id. id <> header_st.cs_next_id ==> FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (if FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE then
       t.vs_alloca_next = initial.vs_alloca_next+32 else t.vs_alloca_next = initial.vs_alloca_next) /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    abi_decode_footprint_frame [(d,32);(p,32)] initial t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op t = eval_operand op initial) /\
    t.vs_halted = initial.vs_halted /\
    t.vs_accounts = initial.vs_accounts /\ t.vs_transient = initial.vs_transient /\
    t.vs_logs = initial.vs_logs /\ t.vs_tx_ctx = initial.vs_tx_ctx /\
    t.vs_block_ctx = initial.vs_block_ctx /\ t.vs_outcomes = initial.vs_outcomes /\
    t.vs_requests = initial.vs_requests /\ t.vs_pending_deletions = initial.vs_pending_deletions /\
    t.vs_gas_readings = initial.vs_gas_readings /\ t.vs_fmp = initial.vs_fmp
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all initializer_path_shape >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  `!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts fn)` by
    (rpt strip_tac >> first_x_assum irule >>
     `inst_extends st header_st` by
       (drule_all abi_decode_dynarray_prefix_shape >>
        simp[abi_decode_source_opcode_def] >> strip_tac >>
        drule_all abi_decode_array_header_shape >>
        simp[abi_decode_source_opcode_def] >> strip_tac >>
        metis_tac[inst_extends_trans]) >>
     `inst_extends header_st loop_st` by metis_tac[abi_decode_index_init_shape] >>
     metis_tac[emitted_insts_append, inst_extends_def, listTheory.MEM_APPEND]) >>
  drule_all entry_array_init_accepted_live >> strip_tac >>
  `abi_alloca_history (fn_insts fn) t` by
    (irule abi_alloca_history_sequence >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_encoder_registered_effect {header_st.cs_next_id} [(d,32)] initial t` by
    (irule initializer_registered_effect >> simp[] >> metis_tac[]) >>
  `entry_decode_path ctx fn initial
      (t with vs_inst_idx := LENGTH loop_st.cs_current_insts)` by
    (irule entry_decode_emitted_path >> simp[] >> qexists_tac `st` >> simp[] >>
     fs[inst_extends_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  qexists_tac `t` >> simp[]
QED
