Theory simplifyCfgPhiPreds
Ancestors
  list venomInst venomWf cfgTransform simplifyCfgDefs simplifyCfgLabelProps
  simplifyCfgStruct simplifyCfgPhiRepair simplifyCfgRepairDataflow

(* Containment is separate from incoming-edge coverage: an ignored extra
   pair may otherwise become live after a CFG contraction. *)
Definition scfg_phi_preds_def:
  scfg_phi_preds fn <=>
    !bb inst p v.
      MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
      inst.inst_opcode = PHI /\ MEM (p,v) (phi_pairs inst.inst_operands) ==>
      fn_cfg_edge fn p bb.bb_label
End

Theorem scfg_phi_preds_edge:
  scfg_phi_preds fn /\ MEM bb fn.fn_blocks /\
  MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
  MEM (p,v) (phi_pairs inst.inst_operands) ==>
  fn_cfg_edge fn p bb.bb_label
Proof
  simp[scfg_phi_preds_def] >> metis_tac[]
QED

Theorem fix_all_phis_phi_preds:
  wf_function fn /\ fn_inst_wf fn ==>
  scfg_phi_preds (fix_all_phis fn)
Proof
  strip_tac >>
  `!bb. MEM bb fn.fn_blocks ==> bb_well_formed bb` by
    fs[wf_function_def, EVERY_MEM] >>
  simp[scfg_phi_preds_def, fix_all_phis_def, MEM_MAP,
    PULL_EXISTS] >> rpt strip_tac >>
  drule_all fix_phis_in_block_phi_pair >> strip_tac >>
  simp[GSYM fix_all_phis_def, bb_label_fix_phis_in_block,
    fix_all_phis_edge]
QED
