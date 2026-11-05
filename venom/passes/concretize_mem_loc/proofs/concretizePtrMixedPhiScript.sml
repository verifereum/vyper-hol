Theory concretizePtrMixedPhi
Ancestors
  concretizePtrOpaqueRetpc concretizePtrSharedFields concretizePtrValueSelection
  concretizePtrValueTransport ptrDiscipline unitShapeDefs
  venomExecSemantics venomState finite_map list
  concretizeStepStructure passSharedDefs venomWf passSimulationDefs rich_list venomInst unitLabelMapIdentity venomExecProofs
  contextCodegenRel passSimulationProps

Theorem ptr_mixed_phis_token[local]:
  !insts s s'. eval_phis s insts = OK s' ==>
    s'.vs_return_pc_token = s.vs_return_pc_token
Proof
  Induct >> simp[eval_phis_def] >> rpt gen_tac >>
  Cases_on `h.inst_opcode <> PHI` >> simp[] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[update_var_def] >>
  metis_tac[]
QED

Theorem ptr_mixed_eval_phis:
  !insts t'.
  ptr_mixed_vars births positions TG tn f g s t /\ ptr_core_shared s t /\
  s.vs_prev_bb = t.vs_prev_bb /\ retpc_shape_ok f /\
  EVERY (\i. MEM i (fn_insts f) /\ inst_wf i) insts /\
  eval_phis t insts = OK t' ==>
  ?s'. eval_phis s insts = OK s' /\
    ptr_mixed_vars births positions (phis_prov s.vs_prev_bb TG insts)
      (tn with t_var := phis_taint s.vs_prev_bb tn insts) f g s' t' /\
    ptr_core_shared s' t'
Proof
  Induct
  >- (simp[eval_phis_def, phis_prov_def, phis_taint_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `s` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode <> PHI`
  >- (gvs[eval_phis_def, phis_prov_def, phis_taint_def] >>
      qexists_tac `s` >> simp[]) >>
  `s.vs_prev_bb = t.vs_prev_bb /\ s.vs_labels = t.vs_labels` by
    fs[ptr_core_shared_def, ptr_shared_fields_def] >>
  `OPTREL (\(out,sv) (out',tv). out = out' /\
      if retpc_var f out then
        sv = s.vs_return_pc_token /\ tv = t.vs_return_pc_token
      else ptr_value_transport births positions (phi_prov s.vs_prev_bb TG h)
        (phi_taint s.vs_prev_bb tn h) sv tv)
    (eval_one_phi s h) (eval_one_phi t h)` by
    (irule ptr_mixed_eval_one_phi >> gvs[] >> metis_tac[]) >>
  gvs[eval_phis_def, AllCaseEqs()] >>
  gvs[optionTheory.OPTREL_def] >> PairCases_on `x0` >> gvs[] >>
  rename1 `eval_one_phi s h = SOME (out,sv)` >>
  `h.inst_outputs = [out]` by gvs[eval_one_phi_def, AllCaseEqs()] >>
  reverse conj_tac
  >- gvs[ptr_core_shared_def, ptr_shared_fields_def, update_var_def] >>
  simp[phis_prov_def, phis_taint_def] >>
  irule ptr_mixed_vars_update >>
  rpt (goal_assum (drule_at Any)) >>
  reverse (rpt conj_tac)
  >- metis_tac[]
  >- (Cases_on `retpc_var f out` >> gvs[] >>
      metis_tac[ptr_mixed_phis_token]) 
  >- (Cases_on `phi_prov t.vs_prev_bb TG h` >>
      gvs[set_prov_def, set_var_taint_def, FLOOKUP_UPDATE,
          FLOOKUP_DRESTRICT, op_taint_def] >>
      Cases_on `retpc_var f out` >> gvs[]) >>
  rpt strip_tac >>
  Cases_on `phi_prov t.vs_prev_bb TG h` >>
  simp[set_prov_def, set_var_taint_def, FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT, op_taint_def] >>
  qpat_x_assum `ptr_mixed_vars births positions TG tn f g s t` kall_tac >>
  drule_all ptr_mixed_vars_lookup >> simp[op_taint_def]
QED

Theorem ptr_positions_eval_phis_map[local]:
  !insts s. eval_phis s (MAP (concretize_inst_with_positions p) insts) =
    eval_phis s insts
Proof
  Induct >> simp[eval_phis_def] >> rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI` >>
  simp[concretize_positions_phi, eval_phis_def]
QED

(* Arbitrary deletions after the leading PHIs do not affect their parallel
   evaluation. Unlike NOP-specific clearing interfaces this also covers
   deleted non-PHI allocation instructions. *)
Theorem ptr_eval_phis_filter_prefix:
  !insts s P.
  (!i j. i < j /\ j < LENGTH insts /\ (EL j insts).inst_opcode = PHI ==>
    (EL i insts).inst_opcode = PHI) /\
  (!i. MEM i insts /\ i.inst_opcode = PHI ==> P i) ==>
  eval_phis s (FILTER P insts) = eval_phis s insts
Proof
  Induct >- simp[eval_phis_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (`P h` by metis_tac[MEM] >> simp[eval_phis_def] >>
      `eval_phis s (FILTER P insts) = eval_phis s insts` by
        (first_x_assum irule >> simp[MEM] >> rpt strip_tac
         >- (qpat_x_assum `!i j. _` (qspecl_then [`SUC i`, `SUC j`] mp_tac) >>
             simp[EL_CONS]) >> metis_tac[MEM]) >> simp[]) >>
  Cases_on `P h` >- simp[eval_phis_def] >>
  simp[eval_phis_def] >> irule eval_phis_no_phis >>
  simp[EVERY_FILTER, EVERY_EL] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[EL_CONS]
QED

Theorem ptr_positions_block_eval_phis:
  bb_well_formed bb ==>
  eval_phis s (clear_nops_block
    (block_map_transform (concretize_inst_with_positions p) bb)).bb_instructions =
  eval_phis s bb.bb_instructions
Proof
  strip_tac >>
  drule concretize_positions_map_block_wf >>
  disch_then (qspec_then `p` assume_tac) >>
  simp[clear_nops_block_def] >>
  irule EQ_TRANS >>
  qexists_tac `eval_phis s
    (block_map_transform (concretize_inst_with_positions p) bb).bb_instructions` >>
  conj_tac
  >- (irule ptr_eval_phis_filter_prefix >> fs[bb_well_formed_def] >>
      rpt strip_tac >> simp[] >> metis_tac[]) >>
  simp[block_map_transform_def, ptr_positions_eval_phis_map]
QED

Theorem ptr_mixed_eval_phis_production_block:
  MEM bb f.fn_blocks /\ bb_well_formed bb /\
  EVERY inst_wf bb.bb_instructions /\
  bbt = clear_nops_block
    (block_map_transform (concretize_inst_with_positions p) bb) /\
  ptr_mixed_vars births positions TG tn f g s t /\ ptr_core_shared s t /\
  s.vs_prev_bb = t.vs_prev_bb /\ retpc_shape_ok f /\
  eval_phis t bbt.bb_instructions = OK t' ==>
  ?s'. eval_phis s bb.bb_instructions = OK s' /\
    ptr_mixed_vars births positions (phis_prov s.vs_prev_bb TG bb.bb_instructions)
      (tn with t_var := phis_taint s.vs_prev_bb tn bb.bb_instructions)
      f g s' t' /\ ptr_core_shared s' t'
Proof
  rpt strip_tac >> gvs[] >>
  `eval_phis t bb.bb_instructions = OK t'` by
    metis_tac[ptr_positions_block_eval_phis] >>
  `EVERY (\i. MEM i (fn_insts f) /\ inst_wf i) bb.bb_instructions` by
    (fs[EVERY_MEM, fn_insts_MEM] >> metis_tac[]) >>
  drule_all ptr_mixed_eval_phis >> simp[]
QED

Theorem ptr_mixed_enters_production_block:
  g.fn_blocks = (concretize_function_with_positions p f).fn_blocks /\
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  MEM bb f.fn_blocks /\ bb_well_formed bb /\
  EVERY inst_wf bb.bb_instructions /\
  s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
  retpc_shape_ok f /\ ptr_mixed_vars births positions TG tn f g s t /\
  ptr_core_shared s t /\ enters_block g t t' ==>
  ?s'. enters_block f s s' /\
    ptr_mixed_vars births positions (phis_prov s.vs_prev_bb TG bb.bb_instructions)
      (tn with t_var := phis_taint s.vs_prev_bb tn bb.bb_instructions) f g s' t' /\
    ptr_core_shared s' t' /\ s'.vs_current_bb = t'.vs_current_bb /\
    s'.vs_prev_bb = t'.vs_prev_bb
Proof
  rpt strip_tac >>
  `lookup_block t.vs_current_bb g.fn_blocks = SOME
    (clear_nops_block (block_map_transform (concretize_inst_with_positions p) bb))` by
    (qpat_x_assum `g.fn_blocks = _` SUBST1_TAC >>
     simp[concretize_positions_blocks, lookup_block_map,
          concretize_positions_block_label] >> metis_tac[]) >>
  qpat_x_assum `enters_block g t t'` mp_tac >>
  simp[enters_block_def] >> strip_tac >> gvs[] >>
  `?u. eval_phis s bb.bb_instructions = OK u /\
    ptr_mixed_vars births positions (phis_prov s.vs_prev_bb TG bb.bb_instructions)
      (tn with t_var := phis_taint s.vs_prev_bb tn bb.bb_instructions) f g u s_phi /\
    ptr_core_shared u s_phi` by
    metis_tac[ptr_mixed_eval_phis_production_block] >>
  qexists_tac `u with vs_inst_idx := phi_prefix_length bb.bb_instructions` >>
  conj_tac
  >- (simp[enters_block_def] >> metis_tac[]) >>
  imp_res_tac eval_phis_only_updates_vs_vars >>
  gvs[ptr_mixed_vars_def, ptr_opaque_env_def, ptr_core_shared_def,
      ptr_shared_fields_def, lookup_var_def] >>
  conj_tac >- metis_tac[] >>
  qpat_x_assum `u = _` SUBST1_TAC >>
  qpat_x_assum `s_phi = _` SUBST1_TAC >> simp[]
QED
