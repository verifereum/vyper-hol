(* FMP lowering's supply, terminator, successor and id facts, and next-id
   monotonicity, lifted from instructions to blocks. *)
Theory fmpStepRewriteSupply
Ancestors
  fmpStepRewrite
  fmpLowerDefs fmpLowerProps fmpLowerInvokeProps fmpStepSupply fmpStepReclaim
  fmpStepChunk fmpStepList fmpLowerIndexedProps
  unitShapeDefs venomWf venomInst list dretDesugarProofs

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
