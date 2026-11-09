(* Syntax origin and identity exclusion at occurrence constructors. *)
Theory occurrenceOrigin
Ancestors
  o1LowerDloadOccurrence o1LowerDloadClosure o1FrameLockstep
  ptrDiscipline o1LowerDloadGhost finite_map list pred_set

Theorem occurrence_out_identity_cases:
  occurrence_out a HP H inst s = SOME id ==>
  (inst.inst_opcode = ALLOCA /\ id = (a,inst.inst_id)) \/
  MEM (SOME id) HP \/ ?v. FLOOKUP H v = SOME id
Proof
  simp[occurrence_out_def, out_prov_def] >>
  IF_CASES_TAC
  >- (Cases_on `FLOOKUP s.vs_allocas inst.inst_id` >> simp[]) >>
  IF_CASES_TAC >- simp[] >>
  IF_CASES_TAC
  >- (Cases_on `inst.inst_operands` >> simp[] >>
      Cases_on `h` >> simp[] >> Cases_on `t` >> simp[] >>
      metis_tac[MEM_EL]) >>
  IF_CASES_TAC >> simp[] >> metis_tac[first_prov_origin]
QED

Theorem occurrence_step_identity_absent:
  (!v. FLOOKUP H v <> SOME id) /\ ~MEM (SOME id) HP /\
  (inst.inst_opcode = ALLOCA ==> id <> (a,inst.inst_id)) ==>
  !v. FLOOKUP (occurrence_step a HP H inst s) v <> SOME id
Proof
  strip_tac >> simp[occurrence_step_def, FLOOKUP_set_prov] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  metis_tac[occurrence_out_identity_cases]
QED

Theorem phi_prov_identity_origin:
  phi_prov prev H inst = SOME id ==> ?v. FLOOKUP H v = SOME id
Proof
  Cases_on `prev` >> simp[phi_prov_def] >>
  Cases_on `resolve_phi x inst.inst_operands` >> simp[] >>
  Cases_on `x'` >> simp[op_prov_def] >> metis_tac[]
QED

Theorem phis_prov_identity_absent:
  !insts. (!v. FLOOKUP H v <> SOME id) ==>
  !v. FLOOKUP (phis_prov prev H insts) v <> SOME id
Proof
  Induct >> simp[phis_prov_def] >> strip_tac >>
  IF_CASES_TAC >> simp[] >>
  simp[FLOOKUP_set_prov] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[phi_prov_identity_origin]
QED

Theorem entry_prov_identity_absent:
  (!v. FLOOKUP H v <> SOME id) ==>
  !v. FLOOKUP (entry_prov fn s H) v <> SOME id
Proof
  simp[entry_prov_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  simp[phis_prov_identity_absent]
QED

Theorem occurrence_call_identity_absent:
  (!v. FLOOKUP H v <> SOME id) ==>
  ~MEM (SOME id) (MAP (op_prov H) ops)
Proof
  simp[MEM_MAP] >> rpt strip_tac >>
  Cases_on `y` >> gvs[op_prov_def] >> metis_tac[]
QED

Theorem occurrence_return_identity_absent:
  (!v. FLOOKUP H v <> SOME id) ==>
  !v. FLOOKUP (DRESTRICT H (COMPL (set outs))) v <> SOME id
Proof
  simp[FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Definition occurrence_syntax_origin_def:
  occurrence_syntax_origin fn a H <=>
    !v aid. FLOOKUP H v = SOME (a,aid) ==>
      ?ai r. MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\
        ai.inst_id = aid /\ MEM r ai.inst_outputs /\
        v IN pointer_derived_vars fn {r}
End

Theorem occurrence_out_own_source:
  occurrence_out a HP H inst s = SOME (a,aid) /\
  ~MEM (SOME (a,aid)) HP ==>
  (inst.inst_opcode = ALLOCA /\ aid = inst.inst_id) \/
  (is_pointer_preserving_op inst.inst_opcode /\
   ?v. MEM (Var v) inst.inst_operands /\ FLOOKUP H v = SOME (a,aid))
Proof
  simp[occurrence_out_def, out_prov_def] >>
  IF_CASES_TAC
  >- (Cases_on `FLOOKUP s.vs_allocas inst.inst_id` >> simp[]) >>
  IF_CASES_TAC >- simp[] >>
  IF_CASES_TAC
  >- (Cases_on `inst.inst_operands` >> simp[] >>
      Cases_on `h` >> simp[] >> Cases_on `t` >> simp[] >>
      metis_tac[MEM_EL]) >>
  IF_CASES_TAC >> simp[] >> strip_tac >>
  drule first_prov_origin >> strip_tac >>
  gvs[pointerConfinedDefsTheory.is_pointer_preserving_op_def] >> metis_tac[]
QED

Theorem occurrence_step_syntax_origin:
  occurrence_syntax_origin fn a H /\ MEM inst (fn_insts fn) /\
  (!aid. ~MEM (SOME (a,aid)) HP) ==>
  occurrence_syntax_origin fn a (occurrence_step a HP H inst s)
Proof
  simp[occurrence_syntax_origin_def] >> strip_tac >>
  simp[occurrence_step_def, FLOOKUP_set_prov] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[]
  >- (strip_tac >>
      drule occurrence_out_own_source >> simp[] >> strip_tac
      >- (qexistsl_tac [`inst`,`v`] >>
          simp[mem2varBlockSimHelpersTheory.roots_in_pointer_derived_vars] >> gvs[]) >>
      first_x_assum drule >> strip_tac >>
      qexistsl_tac [`ai`,`r`] >> simp[] >>
      irule pointer_derived_vars_forward >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem phi_prov_syntax_origin:
  occurrence_syntax_origin fn a H /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = PHI /\ MEM v inst.inst_outputs /\
  phi_prov prev H inst = SOME (a,aid) ==>
  ?ai r. MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\
    ai.inst_id = aid /\ MEM r ai.inst_outputs /\
    v IN pointer_derived_vars fn {r}
Proof
  simp[occurrence_syntax_origin_def, phi_prov_def] >>
  Cases_on `prev` >> simp[] >>
  Cases_on `resolve_phi x inst.inst_operands` >> simp[] >>
  Cases_on `x'` >> simp[op_prov_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexistsl_tac [`ai`,`r`] >> simp[] >>
  irule pointer_derived_vars_forward >>
  simp[pointerConfinedDefsTheory.is_pointer_preserving_op_def] >>
  qexistsl_tac [`inst`,`s`] >>
  simp[pointerConfinedDefsTheory.is_pointer_preserving_op_def] >>
  metis_tac[execEquivParamBaseTheory.resolve_phi_MEM]
QED

Theorem phis_prov_syntax_origin:
  !insts. occurrence_syntax_origin fn a H /\
  EVERY (\i. MEM i (fn_insts fn)) insts ==>
  occurrence_syntax_origin fn a (phis_prov prev H insts)
Proof
  Induct >- simp[phis_prov_def] >>
  gen_tac >> strip_tac >> fs[] >>
  simp[Once phis_prov_def] >> IF_CASES_TAC >> simp[] >>
  fs[occurrence_syntax_origin_def] >>
  simp[FLOOKUP_set_prov] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[]
  >- (strip_tac >> irule phi_prov_syntax_origin >>
      simp[occurrence_syntax_origin_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem entry_prov_syntax_origin:
  occurrence_syntax_origin fn a H ==>
  occurrence_syntax_origin fn a (entry_prov fn s H)
Proof
  strip_tac >> simp[entry_prov_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  irule phis_prov_syntax_origin >> simp[EVERY_MEM] >>
  rpt strip_tac >>
  metis_tac[livenessTransferProofsTheory.lookup_block_mem,
            venomInstTheory.fn_insts_def,
            o1PassContractTheory.fn_insts_blocks_MEM]
QED

Theorem occurrence_return_syntax_origin:
  occurrence_syntax_origin fn a H ==>
  occurrence_syntax_origin fn a (DRESTRICT H (COMPL (set outs)))
Proof
  simp[occurrence_syntax_origin_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem occurrence_syntax_origin_empty:
  occurrence_syntax_origin fn a FEMPTY
Proof
  simp[occurrence_syntax_origin_def]
QED
