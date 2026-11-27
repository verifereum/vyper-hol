Theory groupedDefaultGuardedStart
Ancestors
  groupedDefaultState vyperExternalEntryStorageFrame vyperStorageFootprint
  vyperInterpreter vyperLoweringCorrect selectedAcceptedFold
  defaultConcreteRegistrationDefs bodyPtrDefs loweringStateRelDefs
  bodySim compileEnv vyperContext vyperState words finite_map pair

Theorem grouped_default_guarded_start:
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
  immutable_section_layout ce tops /\
  valid_horizon cx (initial_state am [])
    (H:(bool # bytes32 # type_value) list # num list) es.storage_trace ==>
  stmt_state_rel H ctx fn ce cx es s /\
  storage_well_formed_on cx es (FST H) /\
  ghost_inv_at (cx_dead H cx) 0 NONE ce cx es G tn s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `storage_well_formed_on cx es (FST H)` by
    (drule_at (Pat `send_call_value _ _ _ = _`)
       (INST_TYPE [alpha |-> ``:256``] send_call_value_preserves_storage_well_formed_on) >>
     disch_then irule >>
     `storage_well_formed_on cx
       (initial_state am [FEMPTY] with <|outcomes := SOME vs.vs_outcomes; requests := []|>) (FST H) <=>
      storage_well_formed_on cx (initial_state am []) (FST H)` by
       (irule storage_well_formed_on_backends >> simp[initial_state_def]) >>
     qpat_assum `valid_horizon _ _ _ _` (assume_tac o cj 3 o REWRITE_RULE [valid_horizon_def]) >>
     asm_rewrite_tac[]) >>
  drule_all grouped_empty_registration_state >>
  simp[FORALL_AND_THM]
QED
