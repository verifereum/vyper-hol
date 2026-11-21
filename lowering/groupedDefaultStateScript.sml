Theory groupedDefaultState
Ancestors
  selectedAcceptedFold defaultConcreteRegistrationDefs defaultRegistrationState
  externalEntryBound loweringPosts entryStateRel abiAllocationHistory e2eDefs exprLoweringProps
  loweringStateRelDefs bodyPtrDefs vyperInterpreter vyperState venomInst
  venomState ptrDiscipline words

Theorem grouped_registration_state:
  initial_venom_state_rel tops am tx vs /\ cx.txn = tx /\
  send_call_value mut cx
    (initial_state am [env] with
      <|outcomes := SOME vs.vs_outcomes; requests := []|>) = (INL (),es) /\
  selected_registration_frame vs entry_taint s tn /\
  default_registration_resources ctx fn site 0 st s tn /\
  fn_inst_ids_distinct fn /\
  local_ptrs_rel fn ce [env] s /\
  (!name entry. lookup_scopes name [env] = SOME entry ==>
    value_has_type entry.type entry.value) /\
  (!name entry p sz. lookup_scopes name [env] = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    ptr_covers G tn p s sz) /\
  ce.ce_module = NONE /\ ~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\
  ce.ce_return_pc = NONE /\ ce.ce_return_buf = NONE /\
  storage_vars_rel ce cx /\ transient_vars_rel ce cx /\
  immutable_section_layout ce tops ==>
  alloca_history fn s /\ return_buf_frame NONE ce st s /\
  !H:(bool # bytes32 # type_value) list # num list. stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at (cx_dead H cx) 0 NONE ce cx es G tn s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `es.scopes = [env]` by
    (drule send_call_value_with_scopes >> simp[initial_state_def]) >>
  fs[selected_registration_frame_def, default_registration_resources_def] >>
  simp[return_buf_frame_def] >> gen_tac >> conj_tac
  >- (simp[stmt_state_rel_def, immutable_alloca_sep_def, immutable_decl_sep_def,
        immutable_base_zero_def] >>
      conj_tac
      >- (mp_tac (Q.SPECL [`H:(bool # bytes32 # type_value) list # num list`,`tops`,`fn`,`ce`,`cx`,`am`,`tx`,
            `vs`,`s`,`mut`,`env`,`es`] body_entry_state_rel_runtime) >>
          asm_rewrite_tac[]) >>
      rpt gen_tac >> strip_tac >>
      drule_all abi_alloca_history_function_size >> simp[]) >>
  irule default_registration_clean_ghost >>
  rpt conj_tac
  >~ [`?f. local_ptrs_rel f _ _ _`] >- (qexists_tac `fn` >> asm_rewrite_tac[]) >>
  asm_rewrite_tac[] >> first_assum ACCEPT_TAC
QED

Theorem grouped_empty_vars_local_ptrs:
  local_ptrs_rel fn (ce with ce_vars := FEMPTY) [FEMPTY] s
Proof
  simp[local_ptrs_rel_def, local_region_def]
QED
