(* Backward opaque-copy provenance and shape through PHI fixup. *)
Theory simplifyCfgFixupShape
Ancestors
  simplifyCfgShapeCore
  simplifyCfgFixupClosure simplifyCfgFixupStatic simplifyCfgRestriction
  simplifyCfgLabelProps unitLabelMapIdentity
  unitShapeDefs stackPlanTypes venomWf venomInst simplifyCfgDefs
  list rich_list
  simplifyCfgStruct
  simplifyCfgShape

Theorem scfg_fix_phi_operand_subset:
  MEM op (fix_phi_inst actual_preds inst).inst_operands ==> MEM op inst.inst_operands
Proof
  Cases_on `inst.inst_opcode = PHI` >> simp[fix_phi_inst_def] >>
  namedCases_on `filter_phi_ops actual_preds inst.inst_operands` ["", "o1 r1"] >>
  simp[] >> namedCases_on `r1` ["", "o2 r2"] >> simp[]
  >- metis_tac[MEM_filter_phi_ops, MEM] >>
  Cases_on `r2` >> simp[] >> metis_tac[MEM_filter_phi_ops, MEM]
QED

Theorem scfg_fix_phi_seed_identity:
  (fix_phi_inst actual_preds inst).inst_opcode <> PHI /\
  (fix_phi_inst actual_preds inst).inst_opcode <> ASSIGN /\
  (fix_phi_inst actual_preds inst).inst_opcode <> NOP ==>
  fix_phi_inst actual_preds inst = inst
Proof
  Cases_on `inst.inst_opcode = PHI` >> simp[fix_phi_inst_def] >>
  namedCases_on `filter_phi_ops actual_preds inst.inst_operands` ["", "o1 r1"] >>
  simp[] >> namedCases_on `r1` ["", "o2 r2"] >> simp[] >> Cases_on `r2` >> simp[]
QED

Theorem scfg_fix_all_phis_inst_mem:
  MEM inst' (fn_insts (fix_all_phis fn)) ==>
  ?inst actual_preds. MEM inst (fn_insts fn) /\ inst' = fix_phi_inst actual_preds inst
Proof
  simp[fn_insts_MEM, scfg_fix_all_phis_mem] >>
  rpt strip_tac >> gvs[simplifyCfgStructTheory.fix_phis_in_block_mem] >> metis_tac[]
QED

Theorem scfg_fixed_assign_copy[local]:
  MEM inst (fn_insts fn) /\
  (fix_phi_inst actual_preds inst).inst_opcode = ASSIGN /\
  (fix_phi_inst actual_preds inst).inst_operands = [Var y] /\
  MEM x (fix_phi_inst actual_preds inst).inst_outputs /\
  copy_phi_var origin fn y ==> copy_phi_var origin fn x
Proof
  strip_tac >>
  `MEM x inst.inst_outputs` by metis_tac[fix_phi_inst_outputs_subset] >>
  Cases_on `inst.inst_opcode = PHI`
  >- (`MEM (Var y) inst.inst_operands` by
        metis_tac[scfg_fix_phi_operand_subset, MEM] >>
      metis_tac[copy_phi_var_phi]) >>
  gvs[fix_phi_inst_def] >> metis_tac[copy_phi_var_assign]
QED

Theorem scfg_fixed_phi_copy[local]:
  MEM inst (fn_insts fn) /\
  (fix_phi_inst actual_preds inst).inst_opcode = PHI /\
  MEM (Var y) (fix_phi_inst actual_preds inst).inst_operands /\
  MEM x (fix_phi_inst actual_preds inst).inst_outputs /\
  copy_phi_var origin fn y ==> copy_phi_var origin fn x
Proof
  strip_tac >>
  `inst.inst_opcode = PHI` by metis_tac[scfg_fix_phi_retained_opcode] >>
  `MEM x inst.inst_outputs` by metis_tac[fix_phi_inst_outputs_subset] >>
  `MEM (Var y) inst.inst_operands` by metis_tac[scfg_fix_phi_operand_subset] >>
  metis_tac[copy_phi_var_phi]
QED

Theorem scfg_fix_all_phis_copy_phi_var:
  origin <> PHI /\ origin <> ASSIGN /\ origin <> NOP /\
  fn_inst_wf fn /\ copy_phi_var origin (fix_all_phis fn) x ==>
  copy_phi_var origin fn x
Proof
  `!origin f x. copy_phi_var origin f x ==>
    !fn. f = fix_all_phis fn /\ origin <> PHI /\ origin <> ASSIGN /\ origin <> NOP ==>
      copy_phi_var origin fn x` suffices_by metis_tac[] >>
  Induct_on `copy_phi_var` >> rpt strip_tac
  >- (gvs[] >> drule scfg_fix_all_phis_inst_mem >>
      disch_then (qx_choosel_then [`old`, `ps`] strip_assume_tac) >> gvs[] >>
      `fix_phi_inst ps old = old` by
        (irule scfg_fix_phi_seed_identity >> simp[]) >>
      gvs[] >> metis_tac[copy_phi_var_seed])
  >- (gvs[] >> drule scfg_fix_all_phis_inst_mem >> strip_tac >> gvs[] >>
      irule scfg_fixed_assign_copy >> metis_tac[]) >>
  gvs[] >> drule scfg_fix_all_phis_inst_mem >> strip_tac >> gvs[] >>
  irule scfg_fixed_phi_copy >> metis_tac[]
QED

Theorem scfg_fix_phi_inst_shape:
  inst_wf inst /\ scfg_inst_shape inst ==> scfg_inst_shape (fix_phi_inst actual_preds inst)
Proof
  strip_tac >> Cases_on `inst.inst_opcode = PHI`
  >- (`phi_well_formed inst.inst_operands` by
        (qpat_x_assum `inst_wf inst` mp_tac >> simp[inst_wf_def]) >>
      `phi_well_formed (filter_phi_ops actual_preds inst.inst_operands)` by
        metis_tac[simplifyCfgStructTheory.filter_phi_ops_well_formed] >>
      simp[fix_phi_inst_def] >>
      namedCases_on `filter_phi_ops actual_preds inst.inst_operands` ["", "o1 r1"] >>
      simp[scfg_inst_shape_def, is_read0_opcode_def, scfg_label_positions_def, label_positions_ok_def] >>
      namedCases_on `r1` ["", "o2 r2"] >> simp[scfg_inst_shape_def, is_read0_opcode_def, scfg_label_positions_def, label_positions_ok_def] >>
      Cases_on `r2` >> simp[scfg_inst_shape_def, is_read0_opcode_def, scfg_label_positions_def, label_positions_ok_def] >>
      Cases_on `o1` >> Cases_on `o2` >> gvs[phi_well_formed_def, is_label_operand_def]) >>
  simp[fix_phi_inst_def]
QED

Theorem scfg_fix_phi_opaque_use:
  MEM (Var x) (fix_phi_inst actual_preds inst).inst_operands ==>
  (gas_use_ok inst x ==> gas_use_ok (fix_phi_inst actual_preds inst) x) /\
  (retpc_use_ok inst x ==> retpc_use_ok (fix_phi_inst actual_preds inst) x)
Proof
  strip_tac >> Cases_on `inst.inst_opcode = PHI`
  >- (gvs[fix_phi_inst_def] >>
      namedCases_on `filter_phi_ops actual_preds inst.inst_operands` ["", "o1 r1"] >>
      gvs[] >> namedCases_on `r1` ["", "o2 r2"] >> gvs[gas_use_ok_def, retpc_use_ok_def] >>
      Cases_on `r2` >> gvs[gas_use_ok_def, retpc_use_ok_def]) >>
  simp[fix_phi_inst_def]
QED

Theorem scfg_fix_all_phis_opaque:
  fn_inst_wf fn /\ opaque_use_ok fn ==> opaque_use_ok (fix_all_phis fn)
Proof
  strip_tac >> rewrite_tac[opaque_use_ok_def] >> rpt strip_tac >>
  drule scfg_fix_all_phis_inst_mem >>
  disch_then (qx_choosel_then [`old`, `ps`] strip_assume_tac) >> gvs[] >>
  `MEM (Var x) old.inst_operands` by metis_tac[scfg_fix_phi_operand_subset] >>
  drule scfg_fix_phi_opaque_use >> strip_tac >>
  `!v. gas_var (fix_all_phis fn) v ==> gas_var fn v` by
    (simp[gas_var_def] >> rpt strip_tac >>
     irule scfg_fix_all_phis_copy_phi_var >> simp[] >> metis_tac[]) >>
  `!v. retpc_var (fix_all_phis fn) v ==> retpc_var fn v` by
    (simp[retpc_var_def] >> rpt strip_tac >>
     irule scfg_fix_all_phis_copy_phi_var >> simp[] >> metis_tac[]) >>
  fs[opaque_use_ok_def] >> metis_tac[]
QED

Theorem scfg_fix_all_phis_shape:
  fn_inst_wf fn /\ scfg_shape fn ==> scfg_shape (fix_all_phis fn)
Proof
  strip_tac >> rewrite_tac[scfg_shape_def] >> conj_tac
  >- fs[scfg_shape_def, fix_all_phis_entry, fix_all_phis_def] >>
  conj_tac
  >- (irule scfg_fix_all_phis_opaque >> fs[scfg_shape_def]) >>
  conj_tac
  >- (simp[EVERY_MEM, scfg_fix_all_phis_mem, bb_label_fix_phis_in_block] >>
      rpt strip_tac >> gvs[bb_label_fix_phis_in_block] >>
      fs[scfg_shape_def, EVERY_MEM] >> metis_tac[]) >>
  simp[EVERY_MEM] >> rpt strip_tac >> drule scfg_fix_all_phis_inst_mem >> strip_tac >> gvs[] >>
  irule scfg_fix_phi_inst_shape >> fs[scfg_shape_def, EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >>
  metis_tac[]
QED

Theorem scfg_restriction_fix_phis_shape:
  wf_function fn /\ fn_inst_wf fn /\ scfg_shape fn ==>
  scfg_shape (fix_all_phis (remove_unreachable_blocks fn))
Proof
  strip_tac >> irule scfg_fix_all_phis_shape >>
  simp[simplifyCfgDefsTheory.remove_unreachable_blocks_fn_inst_wf, scfg_restriction_shape]
QED
