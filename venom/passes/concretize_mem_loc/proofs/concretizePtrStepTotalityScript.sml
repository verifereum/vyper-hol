Theory concretizePtrStepTotality
Ancestors
  concretizePtrLocalOrigin concretizePtrPhiTotality concretizePtrAllocationOrigins
  concretizeAnalysisRoots allocaRemapSSA ptrDiscipline pointerClosure
  pointerConfinedDefs venomWf venomExecSemantics venomState venomInst
  basePtrProofs finite_map pred_set list

Theorem local_output_origin:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ MEM out inst.inst_outputs /\
  out IN pointer_derived_vars fn (alloca_roots fn) ==>
  inst.inst_opcode = ALLOCA \/
  (is_pointer_preserving_op inst.inst_opcode /\
   ?u. MEM (Var u) inst.inst_operands /\
       u IN pointer_derived_vars fn (alloca_roots fn))
Proof
  rpt strip_tac >>
  `FINITE (alloca_roots fn)` by
    (irule SUBSET_FINITE >> qexists_tac `ptr_roots (K {}) fn` >>
     simp[ptr_roots_finite, ptr_roots_def, SUBSET_DEF]) >>
  gvs[pointer_derived_vars_def] >>
  drule pointer_use_vars_mem_char >> strip_tac
  >- (`out IN alloca_roots fn` by gvs[MEM_SET_TO_LIST] >>
      gvs[alloca_roots_def, inst_output_def, AllCaseEqs()] >>
      `inst = inst'` by (irule ssa_unique_output >> simp[] >> metis_tac[]) >> gvs[is_alloca_op_def]) >>
  `MEM inst' (fn_insts fn)` by metis_tac[mem_fn_insts_intro] >>
  `inst = inst'` by (irule ssa_unique_output >> metis_tac[]) >>
  gvs[] >> metis_tac[]
QED

Theorem first_prov_present[local]:
  !ops. MEM (Var u) ops /\ FLOOKUP G u = SOME site ==>
    ?site'. first_prov G ops = SOME site'
Proof
  Induct >> simp[first_prov_def] >> rpt strip_tac >>
  Cases_on `op_prov G h` >> gvs[op_prov_def] >> metis_tac[]
QED

Theorem affine_step_inputs[local]:
  step_inst fuel ctx inst s = OK s' /\
  (inst.inst_opcode = ASSIGN \/ inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) ==>
  (?out. inst.inst_outputs = [out]) /\
  (!op. MEM op inst.inst_operands ==> ?w. eval_operand op s = SOME w)
Proof
  rpt strip_tac >>
  `step_inst_base inst s = OK s'` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >> simp[step_inst_non_invoke]) >>
  qpat_x_assum `step_inst _ _ _ _ = _` kall_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[] >> simp[exec_pure2_def] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem alloca_step_provenance[local]:
  step_inst fuel ctx inst s = OK s' /\ inst.inst_opcode = ALLOCA ==>
  (?out. inst.inst_outputs = [out]) /\
  ?site. FLOOKUP s'.vs_allocas inst.inst_id = SOME site
Proof
  rpt strip_tac >>
  `step_inst_base inst s = OK s'` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >> simp[step_inst_non_invoke]) >>
  qpat_x_assum `step_inst _ _ _ _ = _` kall_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >>
  simp[AllCaseEqs()] >> rpt strip_tac
  >- gvs[exec_alloca_def, AllCaseEqs()] >>
  metis_tac[exec_alloca_id_present]
QED

Theorem ptr_pure_local_step_totality:
  fn_ptr_ok P fn /\ ssa_form fn /\ fn_inst_wf fn /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode <> PHI /\ inst.inst_opcode <> INVOKE /\
  L = pointer_derived_vars fn (alloca_roots fn) /\
  X = pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn) /\
  step_inst fuel ctx inst s = OK s' /\
  (!v w. v IN L DIFF X /\ lookup_var v s = SOME w ==> ?site. FLOOKUP G v = SOME site) ==>
  !v w. v IN L DIFF X /\ lookup_var v s' = SOME w ==>
    ?site. FLOOKUP (step_prov PG G inst s') v = SOME site
Proof
  rpt strip_tac >> Cases_on `MEM v inst.inst_outputs`
  >- (gvs[IN_DIFF] >> drule_all local_output_origin >> strip_tac
      >- (drule_all alloca_step_provenance >> strip_tac >>
          gvs[step_prov_def, set_prov_def, out_prov_def, FLOOKUP_UPDATE]) >>
      `inst.inst_opcode = ASSIGN \/ inst.inst_opcode = ADD \/ inst.inst_opcode = SUB` by
        (Cases_on `inst.inst_opcode` >> gvs[is_pointer_preserving_op_def]) >>
      drule affine_step_inputs >> simp[] >> strip_tac >>
      `u NOTIN pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn)` by
        (strip_tac >>
         `v IN pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn)` by
           (irule pointer_derived_vars_closed >> simp[FINITE_DIFF, ptr_roots_finite] >>
            qexistsl_tac [`inst`, `u`] >> metis_tac[]) >> gvs[IN_DIFF]) >>
      `?w. lookup_var u s = SOME w` by metis_tac[eval_operand_def] >>
      `?site. FLOOKUP G u = SOME site` by metis_tac[IN_DIFF] >>
      `?site. first_prov G inst.inst_operands = SOME site` by metis_tac[first_prov_present] >>
      gvs[step_prov_def, set_prov_def, out_prov_def, FLOOKUP_UPDATE]) >>
  `lookup_var v s' = lookup_var v s` by metis_tac[step_inst_preserves_lookup] >>
  `?site. FLOOKUP G v = SOME site` by metis_tac[] >>
  simp[step_prov_def, set_prov_def] >>
  Cases_on `inst.inst_outputs` >> simp[FLOOKUP_DRESTRICT] >>
  Cases_on `t` >> simp[FLOOKUP_DRESTRICT] >>
  Cases_on `out_prov PG G inst s'` >> gvs[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED
