Theory concretizePtrOwnershipErasure
Ancestors
  concretizePtrPrefixLedger ptrDiscipline finite_map list

Definition ptr_owner_project_def:
  ptr_owner_project (births : (num # num,num # num) fmap) p =
    case p of NONE => NONE | SOME owner => FLOOKUP births owner
End

Definition ptr_params_erases_def:
  ptr_params_erases births tagged numerical <=>
    numerical = MAP (ptr_owner_project births) tagged /\
    EVERY (\p. case p of NONE => T | SOME owner => owner IN FDOM births) tagged
End

Theorem ptr_owner_op_projection:
  ptr_ledger_erases births tagged numerical ==>
  op_prov numerical op = ptr_owner_project births (op_prov tagged op) /\
  (!owner. op_prov tagged op = SOME owner ==> owner IN FDOM births)
Proof
  Cases_on `op` >> simp[op_prov_def, ptr_owner_project_def] >>
  simp[ptr_ledger_erases_def] >> metis_tac[]
QED

Theorem ptr_owner_first_projection:
  !ops. ptr_ledger_erases births tagged numerical ==>
  first_prov numerical ops = ptr_owner_project births (first_prov tagged ops) /\
  (!owner. first_prov tagged ops = SOME owner ==> owner IN FDOM births)
Proof
  Induct >> simp[first_prov_def, ptr_owner_project_def] >> rpt gen_tac >> strip_tac >>
  drule ptr_owner_op_projection >> disch_then (qspec_then `h` strip_assume_tac) >>
  Cases_on `op_prov tagged h` >> gvs[first_prov_def, ptr_owner_project_def] >>
  `?site. FLOOKUP births x = SOME site` by metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME] >>
  simp[]
QED

Theorem ptr_owner_set_projection:
  ptr_ledger_erases births tagged numerical /\
  (!owner. p = SOME owner ==> owner IN FDOM births) ==>
  ptr_ledger_erases births (set_prov tagged outs p)
    (set_prov numerical outs (ptr_owner_project births p))
Proof
  strip_tac >> Cases_on `p`
  >- (Cases_on `outs` >>
      gvs[ptr_owner_project_def, set_prov_def, ptr_ledger_erases_def,
          FLOOKUP_DRESTRICT] >> rpt strip_tac >>
      gvs[AllCaseEqs()] >> metis_tac[]) >>
  `?site. FLOOKUP births x = SOME site` by metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME] >>
  Cases_on `outs` >> gvs[set_prov_def, ptr_owner_project_def]
  >- (gvs[ptr_ledger_erases_def, FLOOKUP_DRESTRICT] >> metis_tac[]) >>
  Cases_on `t` >> gvs[set_prov_def, ptr_ledger_erases_def,
      FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem ptr_owner_call_params:
  ptr_ledger_erases births tagged numerical ==>
  ptr_params_erases births (MAP (op_prov tagged) ops) (MAP (op_prov numerical) ops)
Proof
  strip_tac >> simp[ptr_params_erases_def, EVERY_MAP, EVERY_MEM, MAP_MAP_o, MAP_EQ_f] >>
  conj_tac
  >- (rpt strip_tac >> metis_tac[ptr_owner_op_projection]) >>
  rpt strip_tac >> drule ptr_owner_op_projection >>
  disch_then (qspec_then `x` strip_assume_tac) >>
  Cases_on `op_prov tagged x` >> gvs[]
QED

Theorem ptr_owner_phi_projection[local]:
  ptr_ledger_erases births tagged numerical ==>
  phi_prov prev numerical inst = ptr_owner_project births (phi_prov prev tagged inst) /\
  (!owner. phi_prov prev tagged inst = SOME owner ==> owner IN FDOM births)
Proof
  strip_tac >> Cases_on `prev` >> simp[phi_prov_def, ptr_owner_project_def] >>
  Cases_on `resolve_phi x inst.inst_operands` >>
  simp[ptr_owner_project_def] >> drule ptr_owner_op_projection >>
  disch_then (qspec_then `x'` mp_tac) >> simp[ptr_owner_project_def]
QED

Theorem ptr_owner_phis_projection[local]:
  !insts. ptr_ledger_erases births tagged numerical ==>
    ptr_ledger_erases births (phis_prov prev tagged insts) (phis_prov prev numerical insts)
Proof
  Induct >> simp[phis_prov_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  drule ptr_owner_phi_projection >>
  disch_then (qspecl_then [`prev`,`h`] strip_assume_tac) >>
  asm_rewrite_tac[] >> irule ptr_owner_set_projection >> metis_tac[]
QED

Theorem ptr_owner_entry_projection:
  ptr_ledger_erases births tagged numerical ==>
    ptr_ledger_erases births (entry_prov fn s tagged) (entry_prov fn s numerical)
Proof
  strip_tac >> simp[entry_prov_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  metis_tac[ptr_owner_phis_projection]
QED

Theorem ptr_owner_param_projection[local]:
  ptr_params_erases births tagged numerical /\ n < LENGTH tagged ==>
  EL n numerical = ptr_owner_project births (EL n tagged) /\
  (!owner. EL n tagged = SOME owner ==> owner IN FDOM births)
Proof
  simp[ptr_params_erases_def, EVERY_EL] >> rpt strip_tac
  >- simp[EL_MAP] >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[]
QED

Theorem ptr_owner_out_projection[local]:
  ptr_ledger_erases births tagged numerical /\ ptr_params_erases births PT PG /\
  inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> DALLOCA ==>
  out_prov PG numerical inst s' = ptr_owner_project births (out_prov PT tagged inst s') /\
  (!owner. out_prov PT tagged inst s' = SOME owner ==> owner IN FDOM births)
Proof
  strip_tac >> Cases_on `inst.inst_opcode = PARAM`
  >- (simp[out_prov_def] >>
      Cases_on `inst.inst_operands` >> simp[ptr_owner_project_def] >>
      Cases_on `t` >> simp[ptr_owner_project_def] >>
      Cases_on `h` >> simp[ptr_owner_project_def] >>
      `LENGTH PG = LENGTH PT` by gvs[ptr_params_erases_def] >>
      Cases_on `w2n c < LENGTH PT` >> simp[ptr_owner_project_def] >>
      drule_all ptr_owner_param_projection >> simp[ptr_owner_project_def]) >>
  simp[out_prov_def] >>
  Cases_on `inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/ inst.inst_opcode = ASSIGN` >>
  simp[ptr_owner_project_def] >>
  drule ptr_owner_first_projection >> disch_then (qspec_then `inst.inst_operands` mp_tac) >>
  simp[ptr_owner_project_def]
QED

Theorem ptr_owner_step_projection:
  ptr_ledger_erases births tagged numerical /\ ptr_params_erases births PT PG /\
  inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> DALLOCA ==>
  ptr_ledger_erases births (step_prov PT tagged inst s') (step_prov PG numerical inst s')
Proof
  strip_tac >> drule_all ptr_owner_out_projection >>
  disch_then (qspec_then `s'` strip_assume_tac) >>
  simp[step_prov_def] >> irule ptr_owner_set_projection >> simp[]
QED

Theorem ptr_ledger_erases_extend:
  ptr_ledger_erases births tagged numerical /\
  (!owner site. FLOOKUP births owner = SOME site ==> FLOOKUP births' owner = SOME site) ==>
  ptr_ledger_erases births' tagged numerical
Proof
  simp[ptr_ledger_erases_def] >> strip_tac >> conj_tac
  >- (gen_tac >> Cases_on `FLOOKUP tagged v` >> simp[] >>
      `?site. FLOOKUP births x = SOME site` by
        metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME] >> metis_tac[]) >>
  rpt strip_tac >>
  `?site. FLOOKUP births owner = SOME site` by
    metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME] >>
  metis_tac[FLOOKUP_DEF, optionTheory.NOT_SOME_NONE]
QED

Theorem ptr_params_erases_extend:
  ptr_params_erases births PT PG /\
  (!owner site. FLOOKUP births owner = SOME site ==> FLOOKUP births' owner = SOME site) ==>
  ptr_params_erases births' PT PG
Proof
  simp[ptr_params_erases_def, EVERY_MEM] >> strip_tac >> conj_tac
  >- (simp[MAP_EQ_f] >> rpt strip_tac >>
      Cases_on `e` >> simp[ptr_owner_project_def] >>
      `x IN FDOM births` by
        (qpat_x_assum `!p. MEM p PT ==> _` (qspec_then `SOME x` mp_tac) >> simp[]) >>
      `?site. FLOOKUP births x = SOME site` by
        metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME] >> metis_tac[]) >>
  rpt strip_tac >> Cases_on `p` >> simp[] >>
  `x IN FDOM births` by
        (qpat_x_assum `!p. MEM p PT ==> _` (qspec_then `SOME x` mp_tac) >> simp[]) >>
  `?site. FLOOKUP births x = SOME site` by
    metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME] >>
  metis_tac[FLOOKUP_DEF, optionTheory.NOT_SOME_NONE]
QED

Theorem ptr_owner_alloca_insert:
  ptr_ledger_erases births tagged numerical /\
  owner NOTIN FDOM births /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s'.vs_allocas inst.inst_id = SOME site ==>
  ptr_ledger_erases (births |+ (owner,site))
    (set_prov tagged inst.inst_outputs (SOME owner))
    (step_prov PG numerical inst s')
Proof
  strip_tac >>
  `ptr_ledger_erases (births |+ (owner,site)) tagged numerical` by
    (irule ptr_ledger_erases_extend >> qexists `births` >> simp[] >>
     rpt strip_tac >> `owner' <> owner` by (strip_tac >> gvs[FLOOKUP_DEF]) >>
     simp[FLOOKUP_UPDATE]) >>
  simp[step_prov_def, out_prov_def] >>
  `SOME site = ptr_owner_project (births |+ (owner,site)) (SOME owner)` by
    simp[ptr_owner_project_def, FLOOKUP_UPDATE] >>
  pop_assum SUBST1_TAC >> irule ptr_owner_set_projection >> simp[]
QED
