Theory groupedDefaultState
Ancestors
  selectedAcceptedFold defaultConcreteRegistrationDefs defaultRegistrationState
  externalEntryBound loweringPosts entryStateRel abiAllocationHistory e2eDefs exprLoweringProps
  loweringStateRelDefs bodyPtrDefs vyperInterpreter vyperState venomInst
  venomState ptrDiscipline words bodySim bodyInvSplit bodyInvIntCallPinsProps supportedProgram
  entryArgPtrs vyperTypeBindArguments venomMemDefs list finite_map
  compileEnv decoderOriginAllocationFrame fragGasPathFrameMem fragGasOriginPtr
  fragGasOrigin fragGasMode fragGasPathMem fragGasPath

Theorem grouped_empty_registration_state:
  initial_venom_state_rel tops am tx vs /\ cx.txn = tx /\
  send_call_value mut cx
    (initial_state am [FEMPTY] with
      <|outcomes := SOME vs.vs_outcomes; requests := []|>) = (INL (),es) /\
  selected_registration_frame vs entry_taint s tn /\
  default_registration_resources ctx fn site 0 st s (tn with t_mem := {}) /\
  fn_inst_ids_distinct fn /\ ce.ce_vars = FEMPTY /\
  ce.ce_modules = [(NONE,tops)] /\ ce.ce_module = NONE /\ ~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\
  ce.ce_return_pc = NONE /\ ce.ce_return_buf = NONE /\
  storage_vars_rel ce cx /\ transient_vars_rel ce cx /\
  immutable_section_layout ce tops ==>
  alloca_history fn s /\ return_buf_frame NONE ce st s /\
  !H:(bool # bytes32 # type_value) list # num list.
    stmt_state_rel H ctx fn ce cx es s /\ ghost_inv_at D 0 NONE ce cx es G tn s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `es.scopes = [FEMPTY]` by
    (drule send_call_value_with_scopes >> simp[initial_state_def]) >>
  `local_ptrs_rel fn ce [FEMPTY] s` by simp[local_ptrs_rel_def, local_region_def] >>
  fs[selected_registration_frame_def, default_registration_resources_def] >>
  simp[return_buf_frame_def] >> gen_tac >> conj_tac
  >- (simp[stmt_state_rel_def, immutable_alloca_sep_def, immutable_decl_sep_def,
        immutable_base_zero_def] >>
      conj_tac
      >- (mp_tac (Q.SPECL [`H:(bool # bytes32 # type_value) list # num list`,
            `tops`,`fn`,`ce`,`cx`,`am`,`tx`,`vs`,`s`,`mut`,`FEMPTY`,`es`]
            body_entry_state_rel_runtime) >>
          asm_rewrite_tac[]) >>
      rpt gen_tac >> strip_tac >>
      drule_all abi_alloca_history_function_size >> simp[]) >>
  fs[ghost_inv_at_def, return_buf_ptr_def, stor_taint_ok_at_def, allocas_from_def,
    entry_taint_def]
QED

Theorem grouped_body_registration_layout:
  body_inv tops ctx ce (initial_evaluation_context am.sources am.layouts tx NONE) /\
  source_deployment_rel tops am tx ==>
  ce.ce_module = NONE /\
  storage_vars_rel ce (initial_evaluation_context am.sources am.layouts tx NONE) /\
  transient_vars_rel ce (initial_evaluation_context am.sources am.layouts tx NONE) /\
  immutable_section_layout ce tops
Proof
  strip_tac >>
  drule body_inv_immutable_section_layout >> strip_tac >>
  drule body_inv_contract >> strip_tac >>
  drule body_inv_module >> strip_tac >>
  drule_then strip_assume_tac intcall_args_body_inv_pins >>
  drule_all contract_inv_module_distinct_keys >> strip_tac >>
  drule_all contract_inv_module_gate >> strip_tac >>
  qpat_assum `cenv_module_pins _ _`
    (strip_assume_tac o REWRITE_RULE [cenv_module_pins_def]) >>
  `supported_declaration_headers tops` by fs[supported_program_def] >>
  simp[] >>
  mp_tac (Q.SPECL [`tops`,`am`,`tx`,`ce`,
    `initial_evaluation_context am.sources am.layouts tx NONE`]
    entry_storage_vars_rel_immutable) >>
  simp[initial_evaluation_context_def, supported_program_def]
QED

Theorem grouped_registered_owners_ghost:
  bind_arguments tenv args vals = SOME envb /\
  ALL_DISTINCT (MAP FST args) /\
  LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) (MAP SND args) tvs /\
  selected_registration_owners fn (MAP FST args) tvs vals (LENGTH args) ce st s G tn /\
  alloca_inv s /\ s.vs_alloca_next < dimword (:256) /\
  tn.t_stor = {} /\ tn.t_trans = {} /\ tn.t_imm = {} /\
  es.scopes = [envb] /\ ce.ce_return_pc = NONE ==>
  ghost_inv_at D 0 NONE ce cx es G tn s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[ghost_inv_at_def, return_buf_ptr_def, stor_taint_ok_at_def, allocas_from_def] >>
  rpt gen_tac >> strip_tac >>
  `FLOOKUP envb name = SOME entry` by
    fs[lookup_scopes_def, AllCaseEqs()] >>
  drule_all bind_arguments_scope_lookup >> strip_tac >>
  `?j. j < LENGTH args /\ EL j args = (name,typ)` by
    metis_tac[MEM_EL] >>
  pop_assum strip_assume_tac >>
  `evaluate_type tenv (SND (EL j args)) = SOME (EL j tvs)` by
    (qpat_assum `LIST_REL _ _ tvs`
       (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     simp[EL_MAP]) >>
  drule_all bind_arguments_lookup_index >> strip_tac >>
  qpat_assum `j < LENGTH args` (fn bound =>
    qpat_assum `selected_registration_owners _ _ _ _ _ _ _ _ _ _`
      (qx_choosel_then [`owner_id`,`owner_var`,`owner_base`,`owner_width`]
         (map_every assume_tac o CONJUNCTS)
       o (fn th => MATCH_MP th bound)
       o Q.SPEC `j` o REWRITE_RULE [selected_registration_owners_def])) >>
  `owner_base+owner_width <= s.vs_alloca_next` by
    metis_tac[alloca_inv_def, alloca_next_valid_def] >>
  `owner_base < dimword (:256)` by decide_tac >>
  `EL j (MAP FST args) = name` by fs[EL_MAP] >>
  `owner_var = p /\ owner_width = sz` by fs[] >>
  gvs[wordsTheory.w2n_n2w] >>
  rpt strip_tac >>
  `w = n2w owner_base` by fs[] >>
  gvs[wordsTheory.w2n_n2w]
QED

Theorem grouped_positional_state_frame:
  stmt_state_rel H ctx fn (ce with ce_vars := FEMPTY) cx es s /\
  ~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\
  selected_registration_frame s tn t tz /\
  selected_registration_resources ctx fn site lo st t /\
  local_ptrs_rel fn ce [envb] t /\ fn_inst_ids_distinct fn /\
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,J,tz) ==>
  stmt_state_rel H ctx fn ce cx (es with scopes := [envb]) t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all decoder_origin_path_allocation_frame >> strip_tac >>
  drule gas_origin_ptr_path_projections >> strip_tac >>
  drule gas_origin_path_erase >> simp[gas_marked_path_def] >> strip_tac >>
  drule gas_path_mem_memory_length >> strip_tac >>
  fs[stmt_state_rel_def, selected_registration_resources_def,
    selected_registration_frame_def, immutable_alloca_sep_def,
    immutable_decl_sep_def, immutable_base_zero_def] >>
  rpt conj_tac
  >- (fs[state_rel_def, storage_rel_def, transient_rel_def, accounts_rel_def,
        immutables_rel_def, logs_rel_def, LIST_REL_EL_EQN, log_entry_equiv_def,
        storage_vars_rel_def, transient_vars_rel_def, contract_storage_def,
        contract_transient_def] >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- fs[alloca_room_def]
  >- (fs[fmp_room_def] >> strip_tac >> res_tac >> decide_tac)
  >> first_assum ACCEPT_TAC
QED

Theorem grouped_empty_scope_decoder_frame:
  es.scopes = [FEMPTY] /\ ~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\
  ce.ce_return_pc = NONE /\ tn.t_imm = {} /\
  stmt_state_rel H ctx fn (ce with ce_vars := FEMPTY) cx es s /\
  ghost_inv_at D 0 NONE (ce with ce_vars := FEMPTY) cx es G tn s /\
  selected_registration_frame s tn t tz /\
  selected_registration_resources ctx fn site 0 st t /\ fn_inst_ids_distinct fn /\
  gas_origin_ptr_path (D,0,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,J,tz) ==>
  stmt_state_rel H ctx fn (ce with ce_vars := FEMPTY) cx es t /\
  ghost_inv_at D 0 NONE (ce with ce_vars := FEMPTY) cx es J tz t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac
  >- (`local_ptrs_rel fn (ce with ce_vars := FEMPTY) [FEMPTY] t` by
        simp[local_ptrs_rel_def, local_region_def] >>
      `es with scopes := [FEMPTY] = es` by
        simp[evaluation_state_component_equality] >>
      mp_tac (Q.INST [`ce` |-> `ce with ce_vars := FEMPTY`,`envb` |-> `FEMPTY`,
        `lo` |-> `0`] (SPEC_ALL grouped_positional_state_frame)) >>
      asm_rewrite_tac[compile_env_accfupds] >> simp[]) >>
  fs[ghost_inv_at_def, return_buf_ptr_def, stor_taint_ok_at_def,
     selected_registration_frame_def, allocas_from_def]
QED
