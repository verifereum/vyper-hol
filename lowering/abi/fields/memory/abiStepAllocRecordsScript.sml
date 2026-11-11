(* TOP-LEVEL: successful native instructions preserve every existing
   allocation record. ALLOCA reuses an existing id; INVOKE restores the
   caller's allocation map when it returns. *)
Theory abiStepAllocRecords
Ancestors
  venomMemProps venomExecProps venomExecSemantics venomState venomInst
  finite_map list pair words arithmetic

Theorem update_var_allocation_fields:
  !name value ss.
    (update_var name value ss).vs_allocas = ss.vs_allocas /\
    (update_var name value ss).vs_alloca_next = ss.vs_alloca_next
Proof
  simp[update_var_def]
QED

Theorem foldl_update_var_allocation_fields:
  !bindings ss.
    (FOLDL (\state (name,value). update_var name value state) ss bindings).vs_allocas = ss.vs_allocas /\
    (FOLDL (\state (name,value). update_var name value state) ss bindings).vs_alloca_next = ss.vs_alloca_next
Proof
  Induct_on `bindings` >- simp[] >> qx_gen_tac `binding` >> Cases_on `binding` >>
  simp[FOLDL, UNCURRY_DEF, update_var_allocation_fields]
QED

Theorem bind_outputs_allocation_fields:
  !outputs values ss out.
    bind_outputs outputs values ss = SOME out ==>
    out.vs_allocas = ss.vs_allocas /\ out.vs_alloca_next = ss.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >> gvs[bind_outputs_def, AllCaseEqs()] >>
  simp[foldl_update_var_allocation_fields]
QED

Theorem exec_alloca_lookup_old:
  !inst ss alloc_size out id offset recorded_size.
    exec_alloca inst ss alloc_size = OK out /\ FLOOKUP ss.vs_allocas id = SOME (offset,recorded_size) ==>
    FLOOKUP out.vs_allocas id = SOME (offset,recorded_size)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[exec_alloca_def, AllCaseEqs(), LET_THM, update_var_def, FLOOKUP_UPDATE] >>
  rw[] >> gvs[]
QED

Theorem step_inst_base_alloca_lookup_old:
  !inst ss out id offset recorded_size.
    inst.inst_opcode = ALLOCA /\ step_inst_base inst ss = OK out /\
    FLOOKUP ss.vs_allocas id = SOME (offset,recorded_size) ==>
    FLOOKUP out.vs_allocas id = SOME (offset,recorded_size)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` (mp_tac o ONCE_REWRITE_RULE [step_inst_base_def]) >>
  asm_simp_tac bool_ss [] >> strip_tac >> gvs[AllCaseEqs()] >>
  drule_all exec_alloca_lookup_old >> simp[]
QED

Theorem step_inst_base_lookup_old:
  !inst ss out id offset recorded_size.
    step_inst_base inst ss = OK out /\ FLOOKUP ss.vs_allocas id = SOME (offset,recorded_size) ==>
    FLOOKUP out.vs_allocas id = SOME (offset,recorded_size)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `inst.inst_opcode = ALLOCA`
  >- (drule_all step_inst_base_alloca_lookup_old >> simp[]) >>
  drule step_inst_base_OK_not_INVOKE >> DISCH_TAC >>
  mp_tac (Q.SPECL [`inst`, `ss`, `out`] step_inst_base_preserves_allocas) >>
  impl_tac >- simp[] >> simp[]
QED

Theorem step_inst_invoke_allocas:
  !fuel ctx inst ss out.
    inst.inst_opcode = INVOKE /\ step_inst fuel ctx inst ss = OK out ==>
    out.vs_allocas = ss.vs_allocas
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` (mp_tac o ONCE_REWRITE_RULE [step_inst_def]) >>
  asm_simp_tac bool_ss [] >> strip_tac >> gvs[AllCaseEqs()] >>
  drule bind_outputs_allocation_fields >>
  simp[merge_callee_state_def]
QED

Theorem step_inst_lookup_old:
  !fuel ctx inst ss out id offset recorded_size.
    step_inst fuel ctx inst ss = OK out /\ FLOOKUP ss.vs_allocas id = SOME (offset,recorded_size) ==>
    FLOOKUP out.vs_allocas id = SOME (offset,recorded_size)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- (drule_all step_inst_invoke_allocas >> simp[]) >>
  `step_inst_base inst ss = OK out` by fs[step_inst_non_invoke] >>
  drule_all step_inst_base_lookup_old >> simp[]
QED

Theorem step_inst_allocas_extend:
  !fuel ctx inst ss out.
    step_inst fuel ctx inst ss = OK out ==> ss.vs_allocas SUBMAP out.vs_allocas
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [SUBMAP_FLOOKUP_EQN] >>
  MAP_EVERY qx_gen_tac [`id`, `recorded_region`] >> DISCH_TAC >>
  PairCases_on `recorded_region` >> drule_all step_inst_lookup_old >> simp[]
QED
