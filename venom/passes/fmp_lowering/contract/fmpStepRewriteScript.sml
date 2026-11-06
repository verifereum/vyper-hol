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
      rpt (CASE_TAC >> gvs[stackPlanTypesTheory.is_label_operand_def])) >>
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

Theorem fmp_lower_inst_supply:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') ==>
  ir_supply_inst_ok s ==>
  dret_supply_extends s s' /\ ir_supply_inst_ok s'
Proof
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (rpt strip_tac >>
      gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs()] >>
      rpt (dxrule_all fresh_var_extends_ok >> strip_tac) >>
      rpt (dxrule_all fresh_id_extends >> strip_tac) >>
      metis_tac[dret_supply_extends_trans]) >>
  simp[fmp_lower_inst_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[dret_supply_extends_refl]
QED

Theorem fmp_emit_restores_supply:
  fmp_emit_restores runner s bases = (out,s') ==>
  ir_supply_inst_ok s ==>
  dret_supply_extends s s' /\ ir_supply_inst_ok s'
Proof
  map_every qid_spec_tac [`s'`, `out`, `s`] >> Induct_on `bases`
  >- simp[fmp_emit_restores_def, dret_supply_extends_refl] >>
  simp[fmp_emit_restores_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule_all fresh_id_extends >> strip_tac >>
  first_x_assum drule >> disch_then drule >> strip_tac >>
  metis_tac[dret_supply_extends_trans]
QED

Theorem fmp_lower_indexed_supply:
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,s') ==>
  ir_supply_inst_ok s ==>
  dret_supply_extends s s' /\ ir_supply_inst_ok s'
Proof
  map_every qid_spec_tac [`s'`, `leftover`, `out`, `restores`, `s`, `k`] >>
  Induct_on `insts` >- simp[fmp_lower_indexed_def, dret_supply_extends_refl] >>
  rpt gen_tac >> Cases_on `fmp_select_point_restores (label,k) restores` >>
  simp[fmp_lower_indexed_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule_all fmp_emit_restores_supply >> strip_tac >>
  drule_all fmp_lower_inst_supply >> strip_tac >>
  first_x_assum drule >> disch_then drule >> strip_tac >>
  metis_tac[dret_supply_extends_trans]
QED

Theorem fmp_lower_blocks_supply:
  fmp_lower_blocks infos ctx runner s restores bbs =
    SOME (FmpBlocksResult out leftover s') ==>
  ir_supply_inst_ok s ==>
  dret_supply_extends s s' /\ ir_supply_inst_ok s'
Proof
  map_every qid_spec_tac [`s'`, `leftover`, `out`, `restores`, `s`] >>
  Induct_on `bbs` >- simp[fmp_lower_blocks_def, dret_supply_extends_refl] >>
  simp[fmp_lower_blocks_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule_all fmp_lower_indexed_supply >> strip_tac >>
  first_x_assum drule >> disch_then drule >> strip_tac >>
  metis_tac[dret_supply_extends_trans]
QED

Theorem fmp_lower_inst_terminal:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') ==>
  out <> [] /\
  (if is_terminator inst.inst_opcode then
     list_terminal (\i. is_terminator i.inst_opcode) out
   else EVERY (\i. ~is_terminator i.inst_opcode) out)
Proof
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (rpt strip_tac >>
      gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs(),
          venomInstTheory.mk_inst_def, is_terminator_def]) >>
  Cases_on `inst.inst_opcode = DRET`
  >- simp[fmp_lower_inst_def] >>
  Cases_on `inst.inst_opcode = GETFMP`
  >- (simp[fmp_lower_inst_def, AllCaseEqs()] >> rpt strip_tac >>
      gvs[is_terminator_def]) >>
  Cases_on `inst.inst_opcode = SETFMP`
  >- (simp[fmp_lower_inst_def, AllCaseEqs()] >> rpt strip_tac >>
      gvs[is_terminator_def]) >>
  Cases_on `inst.inst_opcode = RETFMP`
  >- (simp[fmp_lower_inst_def, AllCaseEqs()] >> rpt strip_tac >>
      gvs[is_terminator_def, list_terminal_def]) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (simp[fmp_lower_inst_def, AllCaseEqs()] >> rpt strip_tac >>
      gvs[is_terminator_def]) >>
  simp[fmp_lower_inst_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[list_terminal_def] >> IF_CASES_TAC >> simp[]
QED

Theorem fmp_lower_inst_successors:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') ==>
  FLAT (MAP get_successors out) = get_successors inst
Proof
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (rpt strip_tac >>
      gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs(),
          mk_inst_def, get_successors_def, is_terminator_def]) >>
  Cases_on `inst.inst_opcode = DRET`
  >- simp[fmp_lower_inst_def] >>
  Cases_on `inst.inst_opcode = GETFMP`
  >- (simp[fmp_lower_inst_def, AllCaseEqs()] >> rpt strip_tac >>
      gvs[get_successors_def, is_terminator_def]) >>
  Cases_on `inst.inst_opcode = SETFMP`
  >- (simp[fmp_lower_inst_def, AllCaseEqs()] >> rpt strip_tac >>
      gvs[get_successors_def, is_terminator_def]) >>
  Cases_on `inst.inst_opcode = RETFMP`
  >- (simp[fmp_lower_inst_def, AllCaseEqs()] >> rpt strip_tac >>
      gvs[get_successors_def, is_terminator_def, MAP_APPEND, FILTER_APPEND_DISTRIB,
          venomStateTheory.get_label_def] >>
      qspec_then `inst.inst_operands` mp_tac APPEND_FRONT_LAST >>
      simp[GSYM NULL_EQ] >> disch_then (fn th =>
        CONV_TAC (RHS_CONV (ONCE_DEPTH_CONV (REWR_CONV (GSYM th))))) >>
      simp[MAP_APPEND, FILTER_APPEND_DISTRIB]) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (simp[fmp_lower_inst_def, AllCaseEqs()] >> rpt strip_tac >>
      gvs[get_successors_def, is_terminator_def]) >>
  simp[fmp_lower_inst_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem fmp_emit_restores_successors:
  fmp_emit_restores runner s bases = (out,s') ==>
  FLAT (MAP get_successors out) = []
Proof
  map_every qid_spec_tac [`s'`, `out`, `s`] >> Induct_on `bases`
  >- simp[fmp_emit_restores_def] >>
  simp[fmp_emit_restores_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  simp[mk_inst_def, get_successors_def, is_terminator_def] >> metis_tac[]
QED

Theorem fmp_lower_indexed_successors:
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,s') ==>
  FLAT (MAP get_successors out) = FLAT (MAP get_successors insts)
Proof
  map_every qid_spec_tac [`s'`, `leftover`, `out`, `restores`, `s`, `k`] >>
  Induct_on `insts` >- simp[fmp_lower_indexed_def] >>
  rpt gen_tac >> Cases_on `fmp_select_point_restores (label,k) restores` >>
  simp[fmp_lower_indexed_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule fmp_emit_restores_successors >> strip_tac >>
  drule fmp_lower_inst_successors >> strip_tac >>
  simp[MAP_APPEND, FLAT_APPEND] >> metis_tac[]
QED

Theorem fmp_lower_blocks_successors:
  fmp_lower_blocks infos ctx runner s restores bbs =
    SOME (FmpBlocksResult out leftover s') ==>
  MAP (\bb. (bb.bb_label, FLAT (MAP get_successors bb.bb_instructions))) out =
  MAP (\bb. (bb.bb_label, FLAT (MAP get_successors bb.bb_instructions))) bbs
Proof
  map_every qid_spec_tac [`s'`, `leftover`, `out`, `restores`, `s`] >>
  Induct_on `bbs` >- simp[fmp_lower_blocks_def] >>
  simp[fmp_lower_blocks_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule fmp_lower_indexed_successors >> strip_tac >> simp[] >> metis_tac[]
QED

Theorem fmp_lower_inst_ids:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') ==>
  if inst.inst_opcode = DALLOCA then
    ir_id_interval s.irs_next_inst s'.irs_next_inst (MAP (\i. i.inst_id) out)
  else MAP (\i. i.inst_id) out = [inst.inst_id] /\
       s'.irs_next_inst = s.irs_next_inst
Proof
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (rpt strip_tac >>
      gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs()] >>
      rpt (dxrule (cj 4 irSupplyTheory.fresh_ir_var_contract) >> strip_tac) >>
      gvs[irSupplyTheory.fresh_inst_id_def, mk_inst_def,
          ir_id_interval_def]) >>
  simp[fmp_lower_inst_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem fmp_emit_restores_ids:
  fmp_emit_restores runner s bases = (out,s') ==>
  ir_id_interval s.irs_next_inst s'.irs_next_inst (MAP (\i. i.inst_id) out)
Proof
  map_every qid_spec_tac [`s'`, `out`, `s`] >> Induct_on `bases`
  >- simp[fmp_emit_restores_def, ir_id_interval_empty] >>
  simp[fmp_emit_restores_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule fresh_inst_id_interval >> strip_tac >>
  first_x_assum drule >> strip_tac >> simp[mk_inst_def] >>
  metis_tac[ir_id_interval_append, APPEND]
QED

Theorem fmp_lower_inst_next_mono:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') ==>
  s.irs_next_inst <= s'.irs_next_inst
Proof
  strip_tac >> drule fmp_lower_inst_ids >>
  IF_CASES_TAC >> simp[ir_id_interval_def]
QED

Theorem fmp_emit_restores_next_mono:
  fmp_emit_restores runner s bases = (out,s') ==>
  s.irs_next_inst <= s'.irs_next_inst
Proof
  strip_tac >> drule fmp_emit_restores_ids >> simp[ir_id_interval_def]
QED

Theorem fmp_lower_indexed_next_mono:
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,s') ==>
  s.irs_next_inst <= s'.irs_next_inst
Proof
  map_every qid_spec_tac [`s'`, `leftover`, `out`, `restores`, `s`, `k`] >>
  Induct_on `insts` >- simp[fmp_lower_indexed_def] >>
  rpt gen_tac >> Cases_on `fmp_select_point_restores (label,k) restores` >>
  simp[fmp_lower_indexed_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule fmp_emit_restores_next_mono >> strip_tac >>
  drule fmp_lower_inst_next_mono >> strip_tac >>
  first_x_assum drule >> decide_tac
QED

Theorem fmp_lower_blocks_next_mono:
  fmp_lower_blocks infos ctx runner s restores bbs =
    SOME (FmpBlocksResult out leftover s') ==>
  s.irs_next_inst <= s'.irs_next_inst
Proof
  map_every qid_spec_tac [`s'`, `leftover`, `out`, `restores`, `s`] >>
  Induct_on `bbs` >- simp[fmp_lower_blocks_def] >>
  simp[fmp_lower_blocks_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule fmp_lower_indexed_next_mono >> strip_tac >>
  first_x_assum drule >> decide_tac
QED

Theorem fmp_lower_inst_assign_origin:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') ==>
  MEM j out /\ j.inst_opcode = ASSIGN ==>
  (inst.inst_opcode = ASSIGN /\ j = inst) \/
  (inst.inst_opcode = GETFMP /\ j.inst_operands = [Var runner] /\
     j.inst_outputs = inst.inst_outputs) \/
  (inst.inst_opcode = SETFMP /\ j.inst_operands = inst.inst_operands /\
     j.inst_outputs = [runner])
Proof
  rpt strip_tac >>
  gvs[fmp_lower_inst_def, AllCaseEqs(), mk_inst_def]
QED

Theorem fmp_emit_restores_assign_origin:
  fmp_emit_restores runner s bases = (out,s') ==>
  MEM j out ==>
  ?id base. MEM base bases /\ j = mk_inst id ASSIGN [Var base] [runner]
Proof
  map_every qid_spec_tac [`s'`, `out`, `s`] >> Induct_on `bases`
  >- simp[fmp_emit_restores_def] >>
  simp[fmp_emit_restores_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem fmp_lower_blocks_retained_opcodes:
  fmp_lower_blocks infos ctx runner s restores bbs =
    SOME (FmpBlocksResult out leftover s') ==>
  MEM op [GAS; PHI; PARAM; RETPC_PARAM; FMP_PARAM] ==>
  MAP (\bb. (bb.bb_label, FILTER (\i. i.inst_opcode = op) bb.bb_instructions)) out =
  MAP (\bb. (bb.bb_label, FILTER (\i. i.inst_opcode = op) bb.bb_instructions)) bbs
Proof
  map_every qid_spec_tac [`s'`, `leftover`, `out`, `restores`, `s`] >>
  Induct_on `bbs` >- simp[fmp_lower_blocks_def] >>
  simp[fmp_lower_blocks_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  (conj_tac
   >- metis_tac[fmp_lower_indexed_retained_opcodes, MEM] >>
   first_x_assum drule >> simp[])
QED

Theorem fmp_lower_indexed_origin:
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,s') ==>
  MEM j out ==>
  (?i s0 chunk s1. MEM i insts /\
     fmp_lower_inst infos ctx runner s0 i = SOME (chunk,s1) /\ MEM j chunk) \/
  (?point base id. MEM (point,base) restores /\
     j = mk_inst id ASSIGN [Var base] [runner])
Proof
  map_every qid_spec_tac [`s'`, `leftover`, `out`, `restores`, `s`, `k`] >>
  Induct_on `insts` >- simp[fmp_lower_indexed_def] >>
  simp[fmp_lower_indexed_cons] >> rpt strip_tac >> gvs[MEM_APPEND]
  >- (drule_all fmp_emit_restores_assign_origin >> strip_tac >>
      drule fmp_select_point_restores_once >> strip_tac >> metis_tac[])
  >- metis_tac[] >>
  first_x_assum drule >> disch_then drule >> strip_tac
  >- metis_tac[] >>
  drule fmp_select_point_restores_once >> strip_tac >> metis_tac[]
QED

Theorem fmp_lower_blocks_origin:
  fmp_lower_blocks infos ctx runner s restores bbs =
    SOME (FmpBlocksResult out leftover s') ==>
  MEM bb out /\ MEM j bb.bb_instructions ==>
  (?src i s0 chunk s1. MEM src bbs /\ MEM i src.bb_instructions /\
     fmp_lower_inst infos ctx runner s0 i = SOME (chunk,s1) /\ MEM j chunk) \/
  (?point base id. MEM (point,base) restores /\
     j = mk_inst id ASSIGN [Var base] [runner])
Proof
  map_every qid_spec_tac [`s'`, `leftover`, `out`, `restores`, `s`] >>
  Induct_on `bbs` >- simp[fmp_lower_blocks_def] >>
  simp[fmp_lower_blocks_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
  >- (drule_all fmp_lower_indexed_origin >> strip_tac >> metis_tac[]) >>
  first_x_assum drule >> simp[] >> strip_tac
  >- metis_tac[] >>
  drule fmp_lower_indexed_leftover >> strip_tac >> metis_tac[]
QED

Theorem fmp_lower_inst_id_origin:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') ==>
  MEM j out ==>
  j.inst_id = inst.inst_id \/
  (s.irs_next_inst <= j.inst_id /\ j.inst_id < s'.irs_next_inst)
Proof
  strip_tac >> drule fmp_lower_inst_ids >>
  Cases_on `inst.inst_opcode = DALLOCA` >>
  simp[ir_id_interval_def, EVERY_MAP, EVERY_MEM] >>
  rpt strip_tac >> gvs[] >> metis_tac[MEM_MAP]
QED

Theorem fmp_lower_indexed_id_origin:
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,s') ==>
  MEM j out ==>
  MEM j.inst_id (MAP (\i. i.inst_id) insts) \/
  (s.irs_next_inst <= j.inst_id /\ j.inst_id < s'.irs_next_inst)
Proof
  map_every qid_spec_tac [`s'`, `leftover`, `out`, `restores`, `s`, `k`] >>
  Induct_on `insts` >- simp[fmp_lower_indexed_def] >>
  simp[fmp_lower_indexed_cons] >> rpt gen_tac >> strip_tac >>
  drule fmp_emit_restores_next_mono >> strip_tac >>
  drule fmp_lower_inst_next_mono >> strip_tac >>
  drule fmp_lower_indexed_next_mono >> strip_tac >>
  gvs[MEM_APPEND] >> strip_tac
  >- (drule fmp_emit_restores_ids >>
      simp[ir_id_interval_def, EVERY_MAP, EVERY_MEM] >> strip_tac >>
      first_x_assum drule >> decide_tac)
  >- (drule_all fmp_lower_inst_id_origin >> strip_tac >> simp[] >> decide_tac) >>
  first_x_assum drule >> disch_then drule >> strip_tac >> simp[] >> decide_tac
QED

Theorem fmp_lower_blocks_id_origin:
  fmp_lower_blocks infos ctx runner s restores bbs =
    SOME (FmpBlocksResult out leftover s') ==>
  MEM bb out /\ MEM j bb.bb_instructions ==>
  (?src i. MEM src bbs /\ MEM i src.bb_instructions /\ j.inst_id = i.inst_id) \/
  (s.irs_next_inst <= j.inst_id /\ j.inst_id < s'.irs_next_inst)
Proof
  map_every qid_spec_tac [`s'`, `leftover`, `out`, `restores`, `s`] >>
  Induct_on `bbs` >- simp[fmp_lower_blocks_def] >>
  simp[fmp_lower_blocks_def, AllCaseEqs()] >> rpt gen_tac >> strip_tac >> gvs[] >>
  drule fmp_lower_indexed_next_mono >> strip_tac >>
  drule fmp_lower_blocks_next_mono >> strip_tac >>
  gvs[] >> strip_tac >> gvs[]
  >- (drule_all fmp_lower_indexed_id_origin >> strip_tac
      >- (disj1_tac >> gvs[MEM_MAP] >> metis_tac[]) >>
      disj2_tac >> decide_tac) >>
  first_x_assum drule >> simp[] >> strip_tac
  >- metis_tac[] >>
  disj2_tac >> decide_tac
QED

Theorem fmp_lower_inst_label_origin:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') ==>
  MEM j out /\ MEM (Label l) j.inst_operands /\ j.inst_opcode <> INVOKE ==>
  inst.inst_opcode <> INVOKE /\ MEM (Label l) inst.inst_operands
Proof
  rpt strip_tac >>
  gvs[fmp_lower_inst_def, AllCaseEqs(), mk_inst_def, MEM_APPEND]
  >> metis_tac[APPEND_FRONT_LAST, MEM_APPEND, MEM, NULL_EQ]
QED

Theorem fmp_lower_inst_var_operand_origin:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') ==>
  MEM j out /\ MEM (Var v) j.inst_operands ==>
  MEM (Var v) inst.inst_operands \/ v = runner \/ ~MEM v s.irs_used_vars
Proof
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (rpt strip_tac >>
      gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs()] >>
      rpt (drule (cj 1 irSupplyTheory.fresh_ir_var_contract) >> strip_tac >>
           dxrule (cj 2 irSupplyTheory.fresh_ir_var_contract) >> strip_tac) >>
      gvs[mk_inst_def] >> metis_tac[MEM]) >>
  rpt strip_tac >>
  gvs[fmp_lower_inst_def, AllCaseEqs(), mk_inst_def, MEM_APPEND]
  >- metis_tac[APPEND_FRONT_LAST, MEM_APPEND, MEM, NULL_EQ]
  >- metis_tac[APPEND_FRONT_LAST, MEM_APPEND, MEM, NULL_EQ] >>
  drule fmp_resolve_invoke_some >> strip_tac >> gvs[MEM_APPEND] >>
  qpat_x_assum `MEM _ (if _ then _ else _)` mp_tac >>
  IF_CASES_TAC >> simp[]
QED

Theorem fmp_lower_inst_phi:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') ==>
  if inst.inst_opcode = PHI then out = [inst]
  else EVERY (\i. i.inst_opcode <> PHI) out
Proof
  rpt strip_tac >> gvs[fmp_lower_inst_def, AllCaseEqs(), mk_inst_def]
QED

Theorem fmp_emit_restores_nonterminal:
  fmp_emit_restores runner s bases = (out,s') ==>
  EVERY (\i. ~is_terminator i.inst_opcode) out
Proof
  strip_tac >> irule fmp_emit_restores_every >>
  qexistsl [`bases`, `runner`, `s`, `s'`] >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem fmp_lower_indexed_empty:
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,s') ==>
  (out = [] <=> insts = [])
Proof
  Cases_on `insts` >- simp[fmp_lower_indexed_def] >>
  simp[fmp_lower_indexed_cons] >> rpt strip_tac >> gvs[] >>
  drule fmp_lower_inst_terminal >> simp[]
QED

Theorem fmp_lower_indexed_terminal:
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,s') ==>
  list_terminal (\i. is_terminator i.inst_opcode) insts ==>
  list_terminal (\i. is_terminator i.inst_opcode) out
Proof
  map_every qid_spec_tac [`s'`, `leftover`, `out`, `restores`, `s`, `k`] >>
  Induct_on `insts` >- simp[fmp_lower_indexed_def, list_terminal_def] >>
  simp[fmp_lower_indexed_cons] >> rpt gen_tac >> strip_tac >>
  drule fmp_emit_restores_nonterminal >> strip_tac >>
  drule fmp_lower_inst_terminal >> strip_tac >>
  Cases_on `insts = []`
  >- (gvs[fmp_lower_indexed_def, list_terminal_def] >>
      strip_tac >> gvs[] >> simp[list_terminal_append]) >>
  drule fmp_lower_indexed_empty >> strip_tac >>
  simp[list_terminal_def] >> strip_tac >>
  first_x_assum drule >> disch_then drule >> strip_tac >>
  gvs[] >> simp[list_terminal_append]
QED

Theorem fmp_emit_restores_not_phi:
  fmp_emit_restores runner s bases = (out,s') ==>
  EVERY (\i. i.inst_opcode <> PHI) out
Proof
  strip_tac >> irule fmp_emit_restores_every >>
  qexistsl [`bases`, `runner`, `s`, `s'`] >> simp[mk_inst_def]
QED

Theorem fmp_lower_indexed_not_phi:
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,s') ==>
  EVERY (\i. i.inst_opcode <> PHI) insts ==>
  EVERY (\i. i.inst_opcode <> PHI) out
Proof
  rpt strip_tac >> drule fmp_lower_indexed_every >>
  disch_then (qspec_then `\i. i.inst_opcode <> PHI` mp_tac) >>
  disch_then irule >> conj_tac
  >- (rpt strip_tac >>
      `i.inst_opcode <> PHI` by gvs[EVERY_MEM] >>
      drule fmp_lower_inst_phi >> simp[]) >>
  rpt strip_tac >> drule fmp_emit_restores_not_phi >> simp[]
QED

Theorem fmp_lower_indexed_phi_prefix:
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,s') ==>
  list_prefix (\i. i.inst_opcode = PHI) insts ==>
  (!n base. n < LENGTH insts /\ MEM ((label,k+n),base) restores ==>
       (EL n insts).inst_opcode <> PHI) ==>
  list_prefix (\i. i.inst_opcode = PHI) out
Proof
  map_every qid_spec_tac [`s'`, `leftover`, `out`, `restores`, `s`, `k`] >>
  Induct_on `insts` >- simp[fmp_lower_indexed_def, list_prefix_def] >>
  simp[fmp_lower_indexed_cons] >> rpt gen_tac >> strip_tac >> gvs[] >>
  simp[Once list_prefix_def] >> strip_tac >> disch_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (`bases = []` by
        (drule fmp_select_point_restores_once >> strip_tac >>
         qpat_x_assum `!n base. _` (qspec_then `0` mp_tac) >>
         simp[] >> Cases_on `bases` >> gvs[] >> metis_tac[]) >>
      gvs[fmp_emit_restores_def] >>
      drule fmp_lower_inst_phi >> simp[] >> strip_tac >> gvs[] >>
      simp[list_prefix_def] >> first_x_assum drule >>
      simp[] >> disch_then irule >> rpt strip_tac >>
      drule fmp_select_point_restores_once >> strip_tac >>
      qpat_x_assum `!n base. _` (qspec_then `SUC n` mp_tac) >>
      gvs[arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> PHI) insts` by metis_tac[] >>
  drule_all fmp_lower_indexed_not_phi >> strip_tac >>
  drule fmp_lower_inst_phi >> simp[] >> strip_tac >>
  drule fmp_emit_restores_not_phi >> strip_tac >>
  irule list_prefix_none >> simp[EVERY_APPEND]
QED

Theorem fmp_lower_indexed_bb_well_formed:
  fmp_lower_indexed infos ctx runner bb.bb_label 0 s restores bb.bb_instructions =
    SOME (out,leftover,s') ==>
  bb_well_formed bb ==>
  (!n base. n < LENGTH bb.bb_instructions /\ MEM ((bb.bb_label,n),base) restores ==>
       (EL n bb.bb_instructions).inst_opcode <> PHI) ==>
  bb_well_formed (bb with bb_instructions := out)
Proof
  simp[bb_well_formed_list] >> rpt strip_tac
  >- (drule_all fmp_lower_indexed_terminal >> simp[]) >>
  drule fmp_lower_indexed_phi_prefix >> simp[] >> disch_then irule >>
  simp[] >> metis_tac[]
QED

Theorem fmp_lower_blocks_well_formed:
  fmp_lower_blocks infos ctx runner s restores bbs =
    SOME (FmpBlocksResult out leftover s') ==>
  EVERY bb_well_formed bbs ==>
  (!bb n base. MEM bb bbs /\ n < LENGTH bb.bb_instructions /\
       MEM ((bb.bb_label,n),base) restores ==>
       (EL n bb.bb_instructions).inst_opcode <> PHI) ==>
  EVERY bb_well_formed out
Proof
  map_every qid_spec_tac [`s'`, `leftover`, `out`, `restores`, `s`] >>
  Induct_on `bbs` >- simp[fmp_lower_blocks_def] >>
  simp[fmp_lower_blocks_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >> conj_tac
  >- (drule fmp_lower_indexed_bb_well_formed >> simp[] >>
      disch_then irule >> metis_tac[]) >>
  first_x_assum drule >> simp[] >> disch_then irule >> rpt strip_tac >>
  drule fmp_lower_indexed_leftover >> strip_tac >> metis_tac[]
QED
