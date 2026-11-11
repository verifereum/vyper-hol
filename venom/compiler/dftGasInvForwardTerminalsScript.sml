Theory dftGasInvForwardTerminals
Ancestors
  dftGasInvAliasPaths dftGasInvForwardOrigins dftRunRel dftWf dftTopoSort
  contextCodegenRel venomWf dftDefs list rich_list venomInst option

Theorem inv_forward_block_alias_hypotheses[local]:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks ==>
  EVERY inst_wf bb.bb_instructions /\
  ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions)) /\
  np_defs_before_uses bb.bb_instructions
Proof
  strip_tac >>
  `EVERY inst_wf bb.bb_instructions` by
    (gvs[dft_fn_rel_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `wf_ssa fn /\ wf_function fn` by gvs[dft_fn_rel_def] >>
  `np_defs_before_uses bb.bb_instructions` by
    metis_tac[wf_ssa_defs_before_uses] >> simp[] >>
  qpat_x_assum `wf_ssa fn` mp_tac >>
  simp[wf_ssa_def, ssa_form_def, fn_insts_def] >> strip_tac >>
  qpat_x_assum `MEM bb fn.fn_blocks` mp_tac >>
  qpat_x_assum `ALL_DISTINCT _` mp_tac >>
  qspec_tac (`fn.fn_blocks`, `bbs`) >>
  Induct >> simp[fn_insts_blocks_def, MAP_APPEND, FLAT_APPEND,
                ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem inv_forward_terminal_producer_use[local]:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  get_instruction bb k = SOME inst /\ ~is_pseudo inst.inst_opcode /\
  MEM a inst.inst_operands ==>
  (inv_terminal_producer bb.bb_instructions a prod <=>
   operand_producer bb.bb_instructions
     (resolve_block_assigns (REVERSE (TAKE k bb.bb_instructions)) a) =
       SOME prod /\ prod.inst_opcode <> ASSIGN)
Proof
  strip_tac >> irule inv_terminal_producer_use >>
  drule_all inv_forward_block_alias_hypotheses >>
  gvs[get_instruction_def, AllCaseEqs()]
QED

Theorem inv_forward_terminal_producers:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  revert_forward_pair bb i j /\
  get_instruction bb i = SOME copy /\ copy.inst_operands = [p;src;n] /\
  get_instruction bb j = SOME rev /\ rev.inst_operands = [q;m] ==>
  (!prod. inv_terminal_producer bb.bb_instructions p prod <=>
          inv_terminal_producer bb.bb_instructions q prod) /\
  (!prod. inv_terminal_producer bb.bb_instructions n prod <=>
          inv_terminal_producer bb.bb_instructions m prod) /\
  !prod. ~inv_terminal_producer bb.bb_instructions src prod
Proof
  strip_tac >>
  drule_all inv_forward_source_origins >> strip_tac >>
  `copy.inst_opcode = RETURNDATACOPY /\ rev.inst_opcode = REVERT` by
    gvs[revert_forward_pair_def] >>
  `!a prod. MEM a copy.inst_operands ==>
    (inv_terminal_producer bb.bb_instructions a prod <=>
     operand_producer bb.bb_instructions
       (resolve_block_assigns (REVERSE (TAKE i bb.bb_instructions)) a) =
         SOME prod /\ prod.inst_opcode <> ASSIGN)` by
    (rpt strip_tac >> irule inv_forward_terminal_producer_use >>
     simp[is_pseudo_def] >> metis_tac[]) >>
  `!a prod. MEM a rev.inst_operands ==>
    (inv_terminal_producer bb.bb_instructions a prod <=>
     operand_producer bb.bb_instructions
       (resolve_block_assigns (REVERSE (TAKE j bb.bb_instructions)) a) =
         SOME prod /\ prod.inst_opcode <> ASSIGN)` by
    (rpt strip_tac >> irule inv_forward_terminal_producer_use >>
     simp[is_pseudo_def] >> metis_tac[]) >>
  gvs[] >> metis_tac[operand_producer_def, NOT_SOME_NONE]
QED
