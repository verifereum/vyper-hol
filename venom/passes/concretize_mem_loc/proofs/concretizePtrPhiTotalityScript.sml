Theory concretizePtrPhiTotality
Ancestors
  concretizePtrLocalOrigin concretizePtrClosure execEquivParamBase phiWellFormed
  ptrDiscipline pointerConfinedDefs venomWf venomExecSemantics venomState
  venomInst finite_map pred_set list

Theorem pure_phi_evaluation_provenance[local]:
  eval_one_phi s i = SOME (out,w) /\ out IN D /\
  phi_well_formed i.inst_operands /\
  (!u. MEM (Var u) i.inst_operands ==> u IN D) /\
  (!v x. v IN D /\ lookup_var v s = SOME x ==> ?site. FLOOKUP G v = SOME site) ==>
  ?site. phi_prov s.vs_prev_bb G i = SOME site
Proof
  simp[eval_one_phi_def, AllCaseEqs()] >> rpt strip_tac >>
  `?u. val_op = Var u` by metis_tac[resolve_phi_well_formed] >>
  `MEM val_op i.inst_operands` by metis_tac[resolve_phi_MEM] >>
  gvs[eval_operand_def, phi_prov_def, op_prov_def] >> metis_tac[]
QED

Theorem pure_phis_totality[local]:
  !insts s'.
  (!i out u. MEM i insts /\ i.inst_opcode = PHI /\
    MEM out i.inst_outputs /\ out IN D /\ MEM (Var u) i.inst_operands ==> u IN D) /\
  (!i. MEM i insts /\ i.inst_opcode = PHI ==> phi_well_formed i.inst_operands) /\
  eval_phis s insts = OK s' /\
  (!v w. v IN D /\ lookup_var v s = SOME w ==> ?site. FLOOKUP G v = SOME site) ==>
  !v w. v IN D /\ lookup_var v s' = SOME w ==>
    ?site. FLOOKUP (phis_prov s.vs_prev_bb G insts) v = SOME site
Proof
  Induct >> simp[eval_phis_def, phis_prov_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> gvs[] >>
  gvs[AllCaseEqs()] >> rpt strip_tac >>
  `h.inst_outputs = [out]` by gvs[eval_one_phi_def, AllCaseEqs()] >>
  Cases_on `v' = out`
  >- (`?site. phi_prov s.vs_prev_bb G h = SOME site` by
        (irule pure_phi_evaluation_provenance >>
         conj_tac >- metis_tac[] >>
         qexistsl_tac [`D`, `out`, `v`] >> simp[] >>
         reverse conj_tac >- metis_tac[] >>
         qpat_x_assum `!i out u. _` (qspecl_then [`h`, `out`] mp_tac) >> simp[] >> metis_tac[]) >>
      gvs[set_prov_def, FLOOKUP_UPDATE]) >>
  gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE, set_prov_def,
      FLOOKUP_DRESTRICT, AllCaseEqs()] >>
  Cases_on `phi_prov s.vs_prev_bb G h` >>
  simp[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  first_x_assum irule >> metis_tac[]
QED

Theorem ptr_pure_local_phis_totality:
  fn_ptr_ok P fn /\ ssa_form fn /\ fn_inst_wf fn /\
  L = pointer_derived_vars fn (alloca_roots fn) /\
  X = pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn) /\
  MEM bb fn.fn_blocks /\ eval_phis s bb.bb_instructions = OK s' /\
  (!v w. v IN L DIFF X /\ lookup_var v s = SOME w ==>
    ?site. FLOOKUP G v = SOME site) ==>
  !v w. v IN L DIFF X /\ lookup_var v s' = SOME w ==>
    ?site. FLOOKUP (phis_prov s.vs_prev_bb G bb.bb_instructions) v = SOME site
Proof
  rpt strip_tac >> irule pure_phis_totality >>
  conj_tac
  >- (rpt strip_tac >>
      `inst_wf i` by metis_tac[fn_inst_wf_def] >> gvs[inst_wf_def]) >>
  conj_tac >- metis_tac[] >>
  qexists_tac `L DIFF X` >> conj_tac
  >- (rpt strip_tac >> irule ptr_pure_local_phi_input >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[IN_DIFF]) >>
  metis_tac[]
QED
