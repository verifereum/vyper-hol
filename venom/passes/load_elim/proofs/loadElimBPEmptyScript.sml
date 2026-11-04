Theory loadElimBPEmpty
Ancestors
  finite_map pred_set list basePtrDefs venomInst

Definition le_bp_empty_writes_def:
  le_bp_empty_writes inst =
    {out | inst.inst_opcode = ASSIGN /\ inst_output inst = SOME out /\
           ?src. inst.inst_operands = [Var src]}
End

Theorem le_bp_empty_lookup:
  (!v. bp_get_ptrs r v = []) <=>
  (!v ps. FLOOKUP r v = SOME ps ==> ps = [])
Proof
  simp[bp_get_ptrs_def] >> eq_tac >> rpt strip_tac
  >- (first_x_assum (qspec_then `v` mp_tac) >> simp[])
  >> Cases_on `FLOOKUP r v` >> simp[] >> metis_tac[]
QED

Theorem le_bp_empty_phi:
  (!v. bp_get_ptrs r v = []) ==>
  bp_normalize (FLAT (MAP (bp_get_ptrs r) vs)) = []
Proof
  strip_tac >> simp[bp_normalize_def, MAP_EQ_f, FLAT_EQ_NIL, EVERY_MAP,
                    EVERY_MEM]
QED

Theorem le_bp_empty_transfer_form:
  (!v. bp_get_ptrs r v = []) /\ inst.inst_opcode <> ALLOCA ==>
  SND (bp_handle_inst r inst) =
    case inst_output inst of
      NONE => r
    | SOME out => if inst.inst_opcode = ASSIGN /\
                      (?src. inst.inst_operands = [Var src])
                  then r |+ (out, []) else r
Proof
  strip_tac >> Cases_on `inst_output inst` >> simp[bp_handle_inst_def]
  >> Cases_on `inst.inst_opcode`
  >> gvs[bp_handle_inst_def, le_bp_empty_phi]
  >> namedCases_on `inst.inst_operands` ["", "a rest"] >> gvs[]
  >> Cases_on `a` >> gvs[]
  >> namedCases_on `rest` ["", "b tail"] >> gvs[]
  >> Cases_on `b` >> gvs[]
  >> Cases_on `tail` >> gvs[]
QED

Theorem le_bp_empty_transfer:
  (!v. bp_get_ptrs r v = []) /\ inst.inst_opcode <> ALLOCA ==>
  (!v. bp_get_ptrs (SND (bp_handle_inst r inst)) v = [])
Proof
  strip_tac >> drule_all le_bp_empty_transfer_form >> disch_then SUBST1_TAC
  >> Cases_on `inst_output inst` >> simp[]
  >> IF_CASES_TAC >> simp[]
  >> gen_tac >> Cases_on `x = v`
  >> gvs[bp_get_ptrs_def, FLOOKUP_UPDATE]
QED

Theorem le_bp_empty_transfer_domain:
  (!v. bp_get_ptrs r v = []) /\ inst.inst_opcode <> ALLOCA ==>
  FDOM (SND (bp_handle_inst r inst)) =
    FDOM r UNION le_bp_empty_writes inst
Proof
  strip_tac >> drule_all le_bp_empty_transfer_form >> disch_then SUBST1_TAC
  >> Cases_on `inst_output inst` >> simp[le_bp_empty_writes_def]
  >> IF_CASES_TAC >> gvs[EXTENSION] >> metis_tac[]
QED

Theorem le_bp_empty_ext:
  (!v. bp_get_ptrs r v = []) /\
  (!v. bp_get_ptrs r' v = []) /\ FDOM r = FDOM r' ==>
  r = r'
Proof
  simp[le_bp_empty_lookup, fmap_eq_flookup] >> rpt strip_tac
  >> Cases_on `FLOOKUP r x` >> Cases_on `FLOOKUP r' x`
  >> gvs[FLOOKUP_DEF, AllCaseEqs()] >> metis_tac[]
QED
