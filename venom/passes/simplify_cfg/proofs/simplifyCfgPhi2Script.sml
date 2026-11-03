Theory simplifyCfgPhi2
Ancestors
  simplifyCfgStruct simplifyCfgDefs venomWf venomInst cfgTransform list

Theorem simplify_cfg_iter_phi_arity:
  !n fn.
    (!inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI ==>
      phi_well_formed inst.inst_operands) /\
    (n = 0 ==> !inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI ==>
      2 <= LENGTH (phi_pairs inst.inst_operands)) ==>
    !inst. MEM inst (fn_insts (FST (simplify_cfg_iter_with_labels n fn))) /\
      inst.inst_opcode = PHI ==>
      2 <= LENGTH (phi_pairs inst.inst_operands)
Proof
  Induct_on `n`
  >- simp[simplify_cfg_iter_with_labels_def] >>
  rpt gen_tac >> strip_tac >>
  `!inst. MEM inst (fn_insts (simplify_cfg_round fn)) /\
      inst.inst_opcode = PHI ==> phi_well_formed inst.inst_operands` by
    (metis_tac[simplify_cfg_round_phi_operands]) >>
  `!inst. MEM inst (fn_insts (simplify_cfg_round fn)) /\
      inst.inst_opcode = PHI ==> 2 <= LENGTH (phi_pairs inst.inst_operands)` by
    (metis_tac[simplify_cfg_round_phi_arity]) >>
  Cases_on `simplify_cfg_round_with_labels fn` >>
  gvs[simplify_cfg_round_def] >>
  simp[Once simplify_cfg_iter_with_labels_def] >>
  IF_CASES_TAC
  >- (gvs[fn_insts_def] >> metis_tac[]) >>
  Cases_on `simplify_cfg_iter_with_labels n q` >>
  gvs[] >> first_x_assum (qspec_then `q` mp_tac) >> simp[]
QED
