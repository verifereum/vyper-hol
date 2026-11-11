Theory bodyPtrIntCallAllocation
Ancestors bodyPtrIntCallConfinement ptrDiscipline venomExecSemantics
  venomState finite_map pred_set list arithmetic venomExecProofs
  venomExecProps venomInstProofs1 venomMemProps venomInst allocaFrontierBound

Definition intcall_alloc_outside_def:
  intcall_alloc_outside P s <=>
  (!id b n. FLOOKUP s.vs_allocas id = SOME (b,n) ==>
     intcall_site_outside P (b,n)) /\
  (!a. s.vs_alloca_next <= a ==> a NOTIN P)
End

Theorem intcall_alloc_setup:
  setup_callee fn args s = SOME cs /\
  (!a. s.vs_alloca_next <= a ==> a NOTIN P) ==>
  intcall_alloc_outside P cs
Proof
  simp[setup_callee_def, AllCaseEqs(), intcall_alloc_outside_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem intcall_alloc_merge:
  intcall_alloc_outside P s ==>
  intcall_alloc_outside P (merge_callee_state s cs)
Proof
  simp[intcall_alloc_outside_def, merge_callee_state_def] >> metis_tac[]
QED

Theorem intcall_alloc_exec_alloca:
  intcall_alloc_outside P s /\ exec_alloca inst s sz = OK t ==>
  intcall_alloc_outside P t
Proof
  simp[exec_alloca_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[update_var_def, intcall_alloc_outside_def, FLOOKUP_UPDATE,
      AllCaseEqs()] >>
  rpt strip_tac >> gvs[intcall_site_outside_def, DISJOINT_DEF, EXTENSION] >>
  metis_tac[LESS_EQ_TRANS, LESS_EQ_ADD]
QED

Theorem intcall_alloc_new_site_bytes:
  intcall_alloc_outside P s /\ exec_alloca inst s sz = OK t ==>
  new_site_bytes s t SUBSET COMPL P
Proof
  strip_tac >>
  `intcall_alloc_outside P t` by metis_tac[intcall_alloc_exec_alloca] >>
  fs[exec_alloca_def, AllCaseEqs()] >>
  gvs[update_var_def, new_site_bytes_def, SUBSET_DEF, FLOOKUP_UPDATE,
      intcall_alloc_outside_def, intcall_site_outside_def,
      DISJOINT_DEF, EXTENSION] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[FLOOKUP_DEF, optionTheory.NOT_SOME_NONE]
QED

Theorem intcall_op_prov_outside[local]:
  intcall_prov_outside P PG G /\ op_prov G op = SOME site ==>
  intcall_site_outside P site
Proof
  Cases_on `op` >> simp[op_prov_def, intcall_prov_outside_def] >> metis_tac[]
QED

Theorem intcall_first_prov_outside[local]:
  !ops. intcall_prov_outside P PG G /\ first_prov G ops = SOME site ==>
  intcall_site_outside P site
Proof
  Induct >- simp[first_prov_def] >> strip_tac >>
  Cases_on `op_prov G h` >> gvs[first_prov_def] >>
  metis_tac[intcall_op_prov_outside]
QED

Theorem intcall_set_prov_outside[local]:
  intcall_prov_outside P PG G /\
  (!site. p = SOME site ==> intcall_site_outside P site) ==>
  intcall_prov_outside P PG (set_prov G outs p)
Proof
  strip_tac >>
  Cases_on `outs` >> simp[set_prov_def, intcall_prov_outside_def,
                             FLOOKUP_DRESTRICT]
  >- (fs[intcall_prov_outside_def] >> metis_tac[]) >>
  Cases_on `t` >> Cases_on `p` >>
  simp[set_prov_def, intcall_prov_outside_def, FLOOKUP_DRESTRICT,
       FLOOKUP_UPDATE] >> rpt strip_tac >> gvs[AllCaseEqs()] >>
  fs[intcall_prov_outside_def] >> metis_tac[]
QED

Theorem intcall_out_prov_outside[local]:
  intcall_prov_outside P PG G /\ intcall_alloc_outside P t /\
  inst.inst_opcode <> DALLOCA /\ out_prov PG G inst t = SOME site ==>
  intcall_site_outside P site
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (fs[out_prov_def, intcall_alloc_outside_def] >>
      PairCases_on `site` >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (fs[out_prov_def, AllCaseEqs()] >>
      fs[intcall_prov_outside_def] >> metis_tac[MEM_EL]) >>
  fs[out_prov_def, AllCaseEqs()] >> metis_tac[intcall_first_prov_outside]
QED

Theorem intcall_step_prov_outside:
  intcall_prov_outside P PG G /\ intcall_alloc_outside P t /\
  inst.inst_opcode <> DALLOCA ==>
  intcall_prov_outside P PG (step_prov PG G inst t)
Proof
  strip_tac >> simp[step_prov_def] >>
  irule intcall_set_prov_outside >> simp[] >>
  metis_tac[intcall_out_prov_outside]
QED

Theorem intcall_phi_prov_outside[local]:
  intcall_prov_outside P PG G /\ phi_prov prev G inst = SOME site ==>
  intcall_site_outside P site
Proof
  strip_tac >> Cases_on `prev` >> gvs[phi_prov_def] >>
  Cases_on `resolve_phi x inst.inst_operands` >> gvs[] >>
  metis_tac[intcall_op_prov_outside]
QED

Theorem intcall_phis_prov_outside[local]:
  !insts. intcall_prov_outside P PG G ==>
  intcall_prov_outside P PG (phis_prov prev G insts)
Proof
  Induct >- simp[phis_prov_def] >> strip_tac >>
  simp[phis_prov_def] >> IF_CASES_TAC >- simp[] >> strip_tac >>
  irule intcall_set_prov_outside >>
  conj_tac >- metis_tac[intcall_phi_prov_outside] >> metis_tac[]
QED

Theorem intcall_entry_prov_outside:
  intcall_prov_outside P PG G ==>
  intcall_prov_outside P PG (entry_prov fn s G)
Proof
  strip_tac >> simp[entry_prov_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  simp[intcall_phis_prov_outside]
QED

Theorem intcall_step_alloc_outside:
  step_inst fuel ctx inst s = OK t /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> DALLOCA /\ inst.inst_opcode <> SETFMP /\
  intcall_alloc_outside P s ==> intcall_alloc_outside P t
Proof
  strip_tac >>
  `step_inst_base inst s = OK t` by fs[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (fs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
      metis_tac[intcall_alloc_exec_alloca]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    metis_tac[step_inst_base_preserves_allocas,
              step_inst_base_preserves_alloca_next] >>
  fs[intcall_alloc_outside_def] >> metis_tac[]
QED

Theorem intcall_ordinary_fmp[local]:
  step_inst_base inst s = OK t /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> DALLOCA /\
  inst.inst_opcode <> SETFMP ==> w2n t.vs_fmp <= w2n s.vs_fmp
Proof
  strip_tac >> Cases_on `is_terminator inst.inst_opcode`
  >- (Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
      qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
      asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
      simp[AllCaseEqs()] >> strip_tac >> gvs[jump_to_def] >>
      pairarg_tac >> gvs[]) >>
  `~is_alloca_op inst.inst_opcode` by
    (Cases_on `inst.inst_opcode` >> fs[is_alloca_op_def]) >>
  drule step_inst_base_preserves_all >> simp[] >> strip_tac >> simp[]
QED

Theorem intcall_step_new_site_outside:
  step_inst fuel ctx inst s = OK t /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> DALLOCA /\ inst.inst_opcode <> SETFMP /\
  intcall_alloc_outside P s ==> new_site_bytes s t SUBSET COMPL P
Proof
  strip_tac >>
  `step_inst_base inst s = OK t` by fs[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (fs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
      metis_tac[intcall_alloc_new_site_bytes]) >>
  `t.vs_allocas = s.vs_allocas` by metis_tac[step_inst_base_preserves_allocas] >>
  `w2n t.vs_fmp <= w2n s.vs_fmp` by metis_tac[intcall_ordinary_fmp] >>
  fs[new_site_bytes_def, SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem intcall_alloc_phis_entry:
  eval_phis s insts = OK t /\ intcall_alloc_outside P s ==>
  intcall_alloc_outside P (t with vs_inst_idx := k)
Proof
  strip_tac >> drule eval_phis_preserves_alloca_fields >> strip_tac >>
  fs[intcall_alloc_outside_def] >> metis_tac[]
QED

Theorem intcall_invoke_alloc_outside:
  inst.inst_opcode = INVOKE /\ step_inst fuel ctx inst s = OK t /\
  intcall_alloc_outside P s ==>
  intcall_alloc_outside P (t with vs_inst_idx := k)
Proof
  strip_tac >> drule_all step_inst_invoke_alloca_fields >>
  strip_tac >> gvs[intcall_alloc_outside_def] >> metis_tac[]
QED
