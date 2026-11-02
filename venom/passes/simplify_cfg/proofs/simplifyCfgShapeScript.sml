(* Structural interfaces for the SimplifyCFG step contract. *)
Theory simplifyCfgShape
Ancestors
  simplifyCfgDefs simplifyCfgLabelProps venomWf venomInst list rich_list

Theorem filter_phi_ops_empty_preds:
  !ops. phi_well_formed ops ==> filter_phi_ops [] ops = []
Proof
  ho_match_mp_tac phi_well_formed_ind >>
  simp[filter_phi_ops_def, phi_well_formed_def]
QED

Theorem fix_phi_inst_empty_preds:
  inst.inst_opcode = PHI /\ phi_well_formed inst.inst_operands ==>
  (fix_phi_inst [] inst).inst_opcode = NOP
Proof
  simp[fix_phi_inst_def, filter_phi_ops_empty_preds]
QED

Theorem fix_phi_inst_terminator:
  is_terminator inst.inst_opcode ==>
  fix_phi_inst actual_preds inst = inst /\ inst.inst_opcode <> PHI
Proof
  Cases_on `inst.inst_opcode` >> simp[is_terminator_def, fix_phi_inst_def]
QED

Theorem fix_phis_in_block_cfg:
  bb.bb_instructions = front ++ [term] /\
  is_terminator term.inst_opcode ==>
  (fix_phis_in_block actual_preds bb).bb_label = bb.bb_label /\
  bb_succs (fix_phis_in_block actual_preds bb) = bb_succs bb
Proof
  strip_tac >> drule fix_phi_inst_terminator >> strip_tac >>
  simp[fix_phis_in_block_def, bb_succs_def, MAP_APPEND, FILTER_APPEND,
       LAST_APPEND] >>
  qmatch_goalsub_abbrev_tac `xs ++ [term]` >>
  Cases_on `xs` >> Cases_on `front` >> simp[LAST_DEF, LAST_APPEND]
QED

Theorem can_bypass_jump_source_distinct:
  lookup_block a.bb_label func.fn_blocks = SOME a /\
  lookup_block b.bb_label func.fn_blocks = SOME b /\
  can_bypass_jump func a b ==>
  a.bb_label <> b.bb_label
Proof
  strip_tac >> strip_tac >>
  `a = b` by metis_tac[optionTheory.SOME_11] >>
  gvs[can_bypass_jump_def]
QED
