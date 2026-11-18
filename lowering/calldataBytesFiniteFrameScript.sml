(* Finite bytes decoder writes preserve the ambient frontier and old ghosts. *)
Theory calldataBytesFiniteFrame
Ancestors
  entryReachBodySequenceObservations entryReachBodyExactArrayLoop
  calldataBytesLeaf abiDecoderReservation abiDecoderContract abiEncoder
  fragGasSeqPtr decoderGhostFramePtr ptrDiscipline
  emitHelper exprLoweringProps compileEnv loweringStateRelDefs venomExecSemantics venomState venomInst
  finite_map pred_set list rich_list arithmetic

Theorem calldata_bytes_sequence_frame:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecBytestring n) st = ((),last) /\
  run_inst_seq (emitted_insts st last) initial = OK actual /\
  last.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit initial ==>
  fresh_vars_wrt limit actual /\
  actual.vs_allocas = initial.vs_allocas /\
  actual.vs_alloca_next = initial.vs_alloca_next /\
  actual.vs_accounts = initial.vs_accounts /\
  actual.vs_transient = initial.vs_transient /\
  actual.vs_logs = initial.vs_logs /\
  actual.vs_tx_ctx = initial.vs_tx_ctx /\
  actual.vs_block_ctx = initial.vs_block_ctx /\
  actual.vs_immutables = initial.vs_immutables /\
  actual.vs_outcomes = initial.vs_outcomes /\
  actual.vs_requests = initial.vs_requests /\
  actual.vs_pending_deletions = initial.vs_pending_deletions /\
  actual.vs_gas_readings = initial.vs_gas_readings /\
  actual.vs_fmp = initial.vs_fmp /\
  actual.vs_call_ctx = initial.vs_call_ctx /\
  actual.vs_data_section = initial.vs_data_section /\
  actual.vs_code = initial.vs_code
Proof
  strip_tac >>
  `actual.vs_allocas = initial.vs_allocas /\
   actual.vs_alloca_next = initial.vs_alloca_next` by
    (irule abi_decode_sequence_allocation_frame >>
     goal_assum (drule_at Any) >>
     drule calldataBytesLeafTheory.calldata_bytes_allocation_shape >>
     simp[EVERY_MEM] >> metis_tac[]) >>
  `entry_loop_fields initial actual /\ fresh_vars_wrt limit actual` by
    (irule entry_sequence_observations >> simp[] >>
     qexists `emitted_insts st last` >> simp[] >>
     qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def,
       compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >>
     rpt strip_tac >> gvs[emitted_insts_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
     simp[DROP_LENGTH_APPEND, mk_inst_def] >> metis_tac[LESS_ADD]) >>
  fs[entry_loop_fields_def]
QED

(* Unlike op_taint, exact map entries distinguish NONE from SOME {}. *)
Theorem bytes_step_old_tvar[local]:
  ~MEM x i.inst_outputs ==>
  FLOOKUP (step_taint i s t tn).t_var x = FLOOKUP tn.t_var x
Proof
  simp[step_taint_def, set_var_taint_def] >>
  Cases_on `i.inst_outputs` >> simp[FLOOKUP_DRESTRICT] >>
  rename1 `i.inst_outputs = h::outs` >>
  Cases_on `outs` >> simp[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem bytes_sequence_old_ghosts[local]:
  !code D lower ctx fn PG G tn initial H u name.
  inst_seq_ptr D lower ctx fn PG G tn code initial H u /\
  EVERY (\i. ~MEM name i.inst_outputs) code ==>
  FLOOKUP H name = FLOOKUP G name /\
  FLOOKUP u.t_var name = FLOOKUP tn.t_var name
Proof
  Induct >> simp[inst_seq_ptr_def] >> rpt gen_tac >>
  Cases_on `step_inst_base h initial` >> simp[] >> strip_tac >>
  gvs[] >> first_x_assum drule >>
  simp[step_prov_other_output, bytes_step_old_tvar]
QED

Theorem calldata_bytes_sequence_ghost_frame:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecBytestring n) st = ((),last) /\
  run_inst_seq (emitted_insts st last) initial = OK actual /\
  inst_seq_ptr D lower ctx fn PG G tn (emitted_insts st last) initial H u ==>
  !name. not_fresh_at st name ==>
    FLOOKUP H name = FLOOKUP G name /\
    FLOOKUP u.t_var name = FLOOKUP tn.t_var name
Proof
  strip_tac >> gen_tac >> disch_tac >> irule bytes_sequence_old_ghosts >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def,
    compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
    fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def] >>
  fs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum drule >> simp[]
QED
