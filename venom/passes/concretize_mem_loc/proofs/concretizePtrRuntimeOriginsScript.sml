Theory concretizePtrRuntimeOrigins
Ancestors
  ptrDiscipline pointerConfinedDefs venomInst finite_map pred_set list
  execEquivParamBase removeUnusedSsaProofs runtimeProvenanceSources

Definition ptr_site_supported_def:
  ptr_site_supported X G site <=>
    !v. FLOOKUP G v = SOME site ==> v IN X
End

Theorem ptr_site_set[local]:
  ptr_site_supported X G site /\
  (p = SOME site ==> !out. MEM out outs ==> out IN X) ==>
  ptr_site_supported X (set_prov G outs p) site
Proof
  Cases_on `outs` >> Cases_on `p` >>
  simp[set_prov_def, ptr_site_supported_def, FLOOKUP_DRESTRICT,
       FLOOKUP_UPDATE] >> rpt strip_tac >>
  Cases_on `t` >> gvs[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem ptr_site_step:
  ptr_site_supported X G site /\ MEM inst (fn_insts fn) /\
  (!i v out. MEM i (fn_insts fn) /\
    is_pointer_preserving_op i.inst_opcode /\ MEM (Var v) i.inst_operands /\
    v IN X /\ MEM out i.inst_outputs ==> out IN X) /\
  ((inst.inst_opcode = ALLOCA \/ inst.inst_opcode = DALLOCA \/
    inst.inst_opcode = PARAM) /\ out_prov PG G inst s' = SOME site ==>
    !out. MEM out inst.inst_outputs ==> out IN X) ==>
  ptr_site_supported X (step_prov PG G inst s') site
Proof
  strip_tac >> simp[step_prov_def] >> irule ptr_site_set >> simp[] >>
  strip_tac >>
  Cases_on `inst.inst_opcode = ALLOCA \/ inst.inst_opcode = DALLOCA \/
            inst.inst_opcode = PARAM`
  >- metis_tac[]
  >> `first_prov G inst.inst_operands = SOME site /\
      is_pointer_preserving_op inst.inst_opcode` by
    (gvs[out_prov_def, AllCaseEqs()] >>
     simp[is_pointer_preserving_op_def]) >>
  drule first_prov_source >> strip_tac >>
  gvs[ptr_site_supported_def] >> metis_tac[]
QED

Theorem ptr_site_phi[local]:
  ptr_site_supported X G site /\ phi_prov prev G inst = SOME site ==>
  ?v. MEM (Var v) inst.inst_operands /\ v IN X
Proof
  simp[phi_prov_def, AllCaseEqs()] >> rpt strip_tac >>
  Cases_on `op` >> gvs[op_prov_def, ptr_site_supported_def] >>
  metis_tac[resolve_phi_MEM]
QED

Theorem ptr_site_phis:
  ptr_site_supported X G0 site /\
  (!i v out. MEM i (fn_insts fn) /\
    is_pointer_preserving_op i.inst_opcode /\ MEM (Var v) i.inst_operands /\
    v IN X /\ MEM out i.inst_outputs ==> out IN X) /\
  EVERY (\i. MEM i (fn_insts fn)) insts ==>
  ptr_site_supported X (phis_prov prev G0 insts) site
Proof
  Induct_on `insts` >> simp[phis_prov_def] >> strip_tac >>
  IF_CASES_TAC >> simp[] >> strip_tac >> irule ptr_site_set >>
  reverse conj_tac >- metis_tac[] >>
  strip_tac >> drule_all ptr_site_phi >> strip_tac >>
  metis_tac[is_pointer_preserving_op_def]
QED

Theorem ptr_site_entry:
  ptr_site_supported X G site /\
  (!i v out. MEM i (fn_insts fn) /\
    is_pointer_preserving_op i.inst_opcode /\ MEM (Var v) i.inst_operands /\
    v IN X /\ MEM out i.inst_outputs ==> out IN X) ==>
  ptr_site_supported X (entry_prov fn s G) site
Proof
  strip_tac >> simp[entry_prov_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  irule ptr_site_phis >> simp[] >> qexists `fn` >> simp[] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  `MEM x fn.fn_blocks` by
    (gvs[lookup_block_def] >> metis_tac[FIND_MEM]) >>
  simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
  metis_tac[]
QED
