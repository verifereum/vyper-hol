(* FMP lowering's well-formedness, shape and retained-opcode facts, lifted
   from instructions to blocks.  Supply and id facts are
   fmpStepRewriteSupply's, origin and PHI facts fmpStepRewriteOrigin's. *)
Theory fmpStepRewrite
Ancestors
  fmpLowerDefs fmpLowerProps fmpLowerInvokeProps fmpStepSupply fmpStepReclaim
  fmpStepChunk fmpStepList fmpLowerIndexedProps
  unitShapeDefs venomWf venomInst list dretDesugarProofs

Theorem fmp_lower_inst_wf:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') /\ inst_wf inst ==>
  EVERY inst_wf out
Proof
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (rpt strip_tac >> gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs(),
         venomInstTheory.mk_inst_def, inst_wf_def] >> gvs[inst_wf_def]) >>
  Cases_on `inst.inst_opcode = DRET`
  >- (rpt strip_tac >> gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def]) >>
  Cases_on `inst.inst_opcode = GETFMP`
  >- (rpt strip_tac >> gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs(), inst_wf_def] >> gvs[inst_wf_def]) >>
  Cases_on `inst.inst_opcode = SETFMP`
  >- (rpt strip_tac >> gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs(), inst_wf_def] >> gvs[inst_wf_def]) >>
  Cases_on `inst.inst_opcode = RETFMP`
  >- (rpt strip_tac >> gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs(), inst_wf_def] >> gvs[inst_wf_def]) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (rpt strip_tac >> gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs(), inst_wf_def] >> gvs[inst_wf_def]) >>
  simp[fmp_lower_inst_ordinary, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem fmp_lower_inst_shape_ok:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') /\ inst_shape_ok inst ==>
  EVERY inst_shape_ok out
Proof
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (rpt strip_tac >>
      gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs(),
          venomInstTheory.mk_inst_def] >>
      gvs[inst_shape_ok_def, is_read0_opcode_def, label_positions_ok_def,
          stackPlanTypesTheory.is_label_operand_def, AllCaseEqs()] >>
      Cases_on `size_op` >> gvs[stackPlanTypesTheory.is_label_operand_def]) >>
  Cases_on `inst.inst_opcode = DRET`
  >- (rpt strip_tac >> gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def]) >>
  Cases_on `inst.inst_opcode = GETFMP`
  >- (rpt strip_tac >>
      gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs()] >>
      gvs[inst_shape_ok_def, is_read0_opcode_def, label_positions_ok_def,
          stackPlanTypesTheory.is_label_operand_def]) >>
  Cases_on `inst.inst_opcode = SETFMP`
  >- (rpt strip_tac >>
      gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs()] >>
      gvs[inst_shape_ok_def, is_read0_opcode_def, label_positions_ok_def,
          stackPlanTypesTheory.is_label_operand_def, AllCaseEqs()]) >>
  Cases_on `inst.inst_opcode = RETFMP`
  >- (rpt strip_tac >>
      gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs()] >>
      gvs[inst_shape_ok_def, is_read0_opcode_def, label_positions_ok_def,
          stackPlanTypesTheory.is_label_operand_def] >>
      `EVERY (\op. ~is_label_operand op)
         (FRONT inst.inst_operands ++ [LAST inst.inst_operands])` by
        metis_tac[APPEND_FRONT_LAST] >> gvs[EVERY_APPEND]) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (rpt strip_tac >>
      gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs()] >>
      drule fmp_resolve_invoke_some >> strip_tac >>
      gvs[inst_shape_ok_def, is_read0_opcode_def, label_positions_ok_def] >>
      IF_CASES_TAC >>
      simp[stackPlanTypesTheory.is_label_operand_def]) >>
  simp[fmp_lower_inst_ordinary, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem fmp_emit_restores_every:
  (!id base. MEM base bases ==> P (mk_inst id ASSIGN [Var base] [runner])) ==>
  fmp_emit_restores runner s bases = (out,s') ==> EVERY P out
Proof
  map_every qid_spec_tac [`s'`, `out`, `s`] >> Induct_on `bases`
  >- simp[fmp_emit_restores_def] >>
  simp[fmp_emit_restores_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem fmp_lower_indexed_every:
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,s') ==>
  (!s i head s1. MEM i insts /\
      fmp_lower_inst infos ctx runner s i = SOME (head,s1) ==> EVERY P head) ==>
  (!s bases prefix s1.
      fmp_emit_restores runner s bases = (prefix,s1) ==> EVERY P prefix) ==>
  EVERY P out
Proof
  map_every qid_spec_tac [`s'`, `leftover`, `out`, `restores`, `s`, `k`] >>
  Induct_on `insts` >- simp[fmp_lower_indexed_def] >>
  rpt gen_tac >> Cases_on `fmp_select_point_restores (label,k) restores` >>
  simp[fmp_lower_indexed_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[EVERY_APPEND] >>
  `EVERY P prefix` by (qpat_x_assum `!s bases prefix s1. _` drule >> simp[]) >>
  `EVERY P head` by (qpat_x_assum `!s i head s1. _ /\ fmp_lower_inst _ _ _ _ _ = _ ==> _`
      (drule_at Any) >> simp[]) >>
  simp[] >> qpat_x_assum `!k s restores out leftover s'. _`
    (drule_at Any) >> simp[] >> disch_then irule >> metis_tac[]
QED

Theorem fmp_lower_blocks_every:
  fmp_lower_blocks infos ctx runner s restores bbs =
    SOME (FmpBlocksResult out leftover s') ==>
  (!s bb i head s1. MEM bb bbs /\ MEM i bb.bb_instructions /\
      fmp_lower_inst infos ctx runner s i = SOME (head,s1) ==> EVERY P head) ==>
  (!s bases prefix s1.
      fmp_emit_restores runner s bases = (prefix,s1) ==> EVERY P prefix) ==>
  EVERY (\bb. EVERY P bb.bb_instructions) out
Proof
  map_every qid_spec_tac [`s'`, `leftover`, `out`, `restores`, `s`] >>
  Induct_on `bbs` >- simp[fmp_lower_blocks_def] >>
  simp[fmp_lower_blocks_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >> conj_tac
  >- (drule fmp_lower_indexed_every >>
      disch_then (qspec_then `P` mp_tac) >>
      (impl_tac >- (rpt strip_tac >>
        qpat_x_assum `!s bb i head s1. _` (drule_at Any) >>
        strip_tac >> qpat_x_assum `!s restores out leftover s'. _` kall_tac >>
        metis_tac[])) >> simp[]) >>
  qpat_x_assum `!s restores out leftover s'. _` (drule_at Any) >>
  simp[] >> disch_then irule >> metis_tac[]
QED

Theorem fmp_emit_restores_wf:
  fmp_emit_restores runner s bases = (out,s') ==> EVERY inst_wf out
Proof
  strip_tac >> irule fmp_emit_restores_every >>
  qexistsl [`bases`, `runner`, `s`, `s'`] >>
  simp[venomInstTheory.mk_inst_def, inst_wf_def]
QED

Theorem fmp_emit_restores_shape_ok:
  fmp_emit_restores runner s bases = (out,s') ==> EVERY inst_shape_ok out
Proof
  strip_tac >> irule fmp_emit_restores_every >>
  qexistsl [`bases`, `runner`, `s`, `s'`] >>
  simp[venomInstTheory.mk_inst_def, inst_shape_ok_def, is_read0_opcode_def,
       label_positions_ok_def, stackPlanTypesTheory.is_label_operand_def]
QED

Theorem fmp_lower_indexed_wf:
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,s') ==> EVERY inst_wf insts ==> EVERY inst_wf out
Proof
  strip_tac >> drule fmp_lower_indexed_every >>
  disch_then (qspec_then `inst_wf` mp_tac) >>
  strip_tac >> strip_tac >> first_x_assum irule >> conj_tac
  >- (rpt strip_tac >> `inst_wf i` by (gvs[EVERY_MEM] >> metis_tac[]) >>
      drule_all fmp_lower_inst_wf >> simp[]) >>
  metis_tac[fmp_emit_restores_wf]
QED

Theorem fmp_lower_indexed_shape_ok:
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,s') ==> EVERY inst_shape_ok insts ==> EVERY inst_shape_ok out
Proof
  strip_tac >> drule fmp_lower_indexed_every >>
  disch_then (qspec_then `inst_shape_ok` mp_tac) >>
  strip_tac >> strip_tac >> first_x_assum irule >> conj_tac
  >- (rpt strip_tac >> `inst_shape_ok i` by (gvs[EVERY_MEM] >> metis_tac[]) >>
      drule_all fmp_lower_inst_shape_ok >> simp[]) >>
  metis_tac[fmp_emit_restores_shape_ok]
QED

Theorem fmp_lower_blocks_wf:
  fmp_lower_blocks infos ctx runner s restores bbs =
    SOME (FmpBlocksResult out leftover s') ==>
  EVERY (\bb. EVERY inst_wf bb.bb_instructions) bbs ==>
  EVERY (\bb. EVERY inst_wf bb.bb_instructions) out
Proof
  strip_tac >> drule fmp_lower_blocks_every >>
  disch_then (qspec_then `inst_wf` mp_tac) >>
  strip_tac >> strip_tac >> first_x_assum irule >> conj_tac
  >- (rpt strip_tac >> `inst_wf i` by (gvs[EVERY_MEM] >> metis_tac[]) >>
      drule_all fmp_lower_inst_wf >> simp[]) >>
  metis_tac[fmp_emit_restores_wf]
QED

Theorem fmp_lower_blocks_shape_ok:
  fmp_lower_blocks infos ctx runner s restores bbs =
    SOME (FmpBlocksResult out leftover s') ==>
  EVERY (\bb. EVERY inst_shape_ok bb.bb_instructions) bbs ==>
  EVERY (\bb. EVERY inst_shape_ok bb.bb_instructions) out
Proof
  strip_tac >> drule fmp_lower_blocks_every >>
  disch_then (qspec_then `inst_shape_ok` mp_tac) >>
  strip_tac >> strip_tac >> first_x_assum irule >> conj_tac
  >- (rpt strip_tac >> `inst_shape_ok i` by (gvs[EVERY_MEM] >> metis_tac[]) >>
      drule_all fmp_lower_inst_shape_ok >> simp[]) >>
  metis_tac[fmp_emit_restores_shape_ok]
QED

(* The pass neither introduces nor edits seeds, PHIs, or parameters. *)
Theorem fmp_lower_inst_retained_opcodes:
  MEM op [GAS; PHI; PARAM; RETPC_PARAM; FMP_PARAM] /\
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') ==>
  FILTER (\i. i.inst_opcode = op) out =
    if inst.inst_opcode = op then [inst] else []
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs(),
          venomInstTheory.mk_inst_def] >> gvs[]) >>
  Cases_on `inst.inst_opcode = DRET`
  >- gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def] >>
  Cases_on `inst.inst_opcode = GETFMP`
  >- (gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs()] >> gvs[]) >>
  Cases_on `inst.inst_opcode = SETFMP`
  >- (gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs()] >> gvs[]) >>
  Cases_on `inst.inst_opcode = RETFMP`
  >- (gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs()] >> gvs[]) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs()] >> gvs[]) >>
  gvs[fmp_lower_inst_ordinary, AllCaseEqs()] >> simp[]
QED

Theorem fmp_emit_restores_retained_opcodes:
  MEM op [GAS; PHI; PARAM; RETPC_PARAM; FMP_PARAM] ==>
  fmp_emit_restores runner s bases = (out,s') ==>
  FILTER (\i. i.inst_opcode = op) out = []
Proof
  map_every qid_spec_tac [`s'`, `out`, `s`] >> Induct_on `bases`
  >- simp[fmp_emit_restores_def] >>
  simp[fmp_emit_restores_def, AllCaseEqs(), venomInstTheory.mk_inst_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem fmp_lower_indexed_retained_opcodes:
  MEM op [GAS; PHI; PARAM; RETPC_PARAM; FMP_PARAM] ==>
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,s') ==>
  FILTER (\i. i.inst_opcode = op) out = FILTER (\i. i.inst_opcode = op) insts
Proof
  map_every qid_spec_tac [`s'`, `leftover`, `out`, `restores`, `s`, `k`] >>
  Induct_on `insts` >- simp[fmp_lower_indexed_def] >>
  rpt gen_tac >> disch_tac >>
  Cases_on `fmp_select_point_restores (label,k) restores` >>
  simp[fmp_lower_indexed_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `_ = out` (SUBST1_TAC o SYM) >>
  qpat_x_assum `_ = (head,s1)` SUBST_ALL_TAC >>
  qpat_x_assum `_ = (tail,leftover,s')` SUBST_ALL_TAC >>
  pure_rewrite_tac[FILTER_APPEND_DISTRIB] >>
  drule_all fmp_emit_restores_retained_opcodes >> strip_tac >>
  drule_all fmp_lower_inst_retained_opcodes >> strip_tac >>
  gvs[] >> first_x_assum (drule_at Any) >> simp[] >>
  strip_tac >> gvs[] >> metis_tac[]
QED
