(* Supply-independent operand-label origin for SUE. *)
Theory singleUseExpansionSupplyLabels
Ancestors
  singleUseExpansionSupplyProofs singleUseExpansionDefs venomInst list

Theorem sue_operand_label_mem[local]:
  !ops l. MEM (SOME l) (MAP sue_operand_label ops) <=> MEM (Label l) ops
Proof
  Induct >> simp[sue_operand_label_def] >> Cases_on `h` >>
  simp[sue_operand_label_def]
QED

Theorem sue_expand_inst_supply_label_origin[local]:
  sue_expand_inst_supply dfg s inst = (out,s') /\
  MEM i out /\ MEM (Label l) i.inst_operands ==>
  MEM (Label l) inst.inst_operands
Proof
  Cases_on `sue_should_skip inst.inst_opcode`
  >- (rpt strip_tac >> gvs[sue_expand_inst_supply_def]) >>
  Cases_on `sue_expand_ops_supply dfg inst s inst.inst_operands 0` >>
  PairCases_on `r` >>
  drule sue_expand_ops_supply_operand_labels >>
  drule sue_expand_ops_supply_copies >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  gvs[sue_expand_inst_supply_def, MEM_APPEND]
  >- (first_x_assum drule >> strip_tac >> gvs[]) >>
  metis_tac[sue_operand_label_mem]
QED

Theorem sue_expand_insts_supply_label_origin[local]:
  !insts dfg s out s' i l.
    sue_expand_insts_supply dfg s insts = (out,s') /\
    MEM i out /\ MEM (Label l) i.inst_operands ==>
    ?j. MEM j insts /\ MEM (Label l) j.inst_operands
Proof
  Induct >> rpt gen_tac
  >- simp[sue_expand_insts_supply_def] >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  Cases_on `sue_expand_insts_supply dfg r insts` >>
  simp[sue_expand_insts_supply_def] >> rpt strip_tac >>
  gvs[MEM_APPEND] >> metis_tac[sue_expand_inst_supply_label_origin]
QED

Theorem sue_expand_block_supply_label_origin[local]:
  sue_expand_block_supply dfg s bb = (bb',s') /\
  MEM i bb'.bb_instructions /\ MEM (Label l) i.inst_operands ==>
  ?j. MEM j bb.bb_instructions /\ MEM (Label l) j.inst_operands
Proof
  Cases_on `sue_expand_insts_supply dfg s bb.bb_instructions` >>
  rpt strip_tac >> gvs[sue_expand_block_supply_def] >>
  metis_tac[sue_expand_insts_supply_label_origin]
QED

Theorem sue_expand_blocks_supply_label_origin[local]:
  !bbs dfg s out s' i l.
    sue_expand_blocks_supply dfg s bbs = (out,s') /\
    MEM i (fn_insts_blocks out) /\ MEM (Label l) i.inst_operands ==>
    ?j. MEM j (fn_insts_blocks bbs) /\ MEM (Label l) j.inst_operands
Proof
  Induct >> rpt gen_tac
  >- simp[sue_expand_blocks_supply_def, fn_insts_blocks_def] >>
  Cases_on `sue_expand_block_supply dfg s h` >>
  Cases_on `sue_expand_blocks_supply dfg r bbs` >>
  simp[sue_expand_blocks_supply_def] >> rpt strip_tac >>
  gvs[fn_insts_blocks_def, MEM_APPEND] >>
  metis_tac[sue_expand_block_supply_label_origin]
QED

Theorem sue_expand_function_supply_label_origin:
  sue_expand_function_supply s fn = (fn',s') /\
  MEM i (fn_insts fn') /\ MEM (Label l) i.inst_operands ==>
  ?j. MEM j (fn_insts fn) /\ MEM (Label l) j.inst_operands
Proof
  Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
  rpt strip_tac >> gvs[sue_expand_function_supply_def, fn_insts_def] >>
  metis_tac[sue_expand_blocks_supply_label_origin]
QED
