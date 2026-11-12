Theory fmpStageCoverBackLaterArity
Ancestors
  o1PassContract o1ContractMakeSsaSrcOpcodes singleUseExpansionDefs
  dftLifting callLayoutDefs venomInst list rich_list

Theorem make_ssa_current_fn_user_count:
  ALL_DISTINCT (fn_labels fn) /\ make_ssa_current_fn s fn = (fn',s') ==>
  LENGTH (fn_user_param_insts fn') = LENGTH (fn_user_param_insts fn)
Proof
  strip_tac >> drule_all make_ssa_current_fn_key >>
  Cases_on `fn.fn_blocks` >> Cases_on `fn'.fn_blocks` >>
  simp[block_key_def, fn_user_param_insts_def, fn_entry_insts_def,
       entry_block_def] >> strip_tac >>
  gvs[] >>
  `kept_opcode PARAM` by simp[kept_opcode_def] >>
  simp[kept_opcode_count]
QED

Theorem fmp_make_ssa_user_count:
  fn_pass_step rpolicy (CFP_Simple VP_MakeSSA) observed s fn out /\
  ALL_DISTINCT (fn_labels fn) ==>
  LENGTH (fn_user_param_insts fn) <=
  LENGTH (fn_user_param_insts out.fpo_function)
Proof
  rw[fn_pass_step_def] >>
  gvs[AllCaseEqs()] >>
  drule_all make_ssa_current_fn_user_count >> simp[]
QED

Theorem sue_insts_user_count[local]:
  !insts s outs s'. sue_expand_insts_supply dfg s insts = (outs,s') ==>
  LENGTH (FILTER (\i. i.inst_opcode = PARAM) insts) <=
  LENGTH (FILTER (\i. i.inst_opcode = PARAM) outs)
Proof
  Induct >> simp[sue_expand_insts_supply_def] >> rpt gen_tac >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  Cases_on `sue_expand_insts_supply dfg r insts` >>
  strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  Cases_on `h.inst_opcode = PARAM` >> gvs[FILTER_APPEND_DISTRIB] >>
  gvs[sue_expand_inst_supply_def, sue_should_skip_def, is_param_opcode_def]
QED

Theorem sue_blocks_user_count[local]:
  !bbs s outs s'. sue_expand_blocks_supply dfg s bbs = (outs,s') ==>
  LENGTH (fn_user_param_insts (fn with fn_blocks := bbs)) <=
  LENGTH (fn_user_param_insts (fn with fn_blocks := outs))
Proof
  Cases >> simp[sue_expand_blocks_supply_def] >> rpt gen_tac >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[sue_expand_block_supply_def, AllCaseEqs(), fn_user_param_insts_def,
      fn_entry_insts_def, entry_block_def] >>
  drule sue_insts_user_count >> simp[]
QED

Theorem sue_function_user_count:
  sue_expand_function_supply s fn = (fn',s') ==>
  LENGTH (fn_user_param_insts fn) <= LENGTH (fn_user_param_insts fn')
Proof
  simp[sue_expand_function_supply_def] >> strip_tac >>
  gvs[AllCaseEqs()] >> drule sue_blocks_user_count >>
  disch_then (qspec_then `fn` mp_tac) >> simp[]
QED

Theorem fmp_sue_user_count:
  fn_pass_step rpolicy (CFP_Simple VP_SingleUseExpansion) observed s fn out ==>
  LENGTH (fn_user_param_insts fn) <=
  LENGTH (fn_user_param_insts out.fpo_function)
Proof
  rw[fn_pass_step_def] >> gvs[AllCaseEqs()] >>
  drule sue_function_user_count >> simp[]
QED

Theorem dft_blocks_user_params[local]:
  !bbs bbs'. LIST_REL dft_block_rel bbs bbs' ==>
  fn_user_param_insts (fn with fn_blocks := bbs') =
  fn_user_param_insts (fn with fn_blocks := bbs)
Proof
  Cases >> Cases >> simp[] >> strip_tac >>
  gvs[dft_block_rel_def, fn_user_param_insts_def, fn_entry_insts_def,
      entry_block_def] >>
  `FILTER (\i. i.inst_opcode = PARAM)
     (FILTER (\i. is_pseudo i.inst_opcode) h'.bb_instructions) =
   FILTER (\i. i.inst_opcode = PARAM)
     (FILTER (\i. is_pseudo i.inst_opcode) h.bb_instructions)` by simp[] >>
  gvs[FILTER_FILTER, SF CONJ_ss, is_pseudo_def, is_param_opcode_def]
QED

Theorem fmp_dft_user_count:
  fn_pass_step rpolicy (CFP_Simple VP_DFT) observed s fn out /\
  wf_function fn /\ fn_inst_wf fn /\ EVERY inst_shape_ok (fn_insts fn) ==>
  LENGTH (fn_user_param_insts fn) <=
  LENGTH (fn_user_param_insts out.fpo_function)
Proof
  strip_tac >> drule_all dft_fn_block_rel >>
  strip_tac >> drule dft_blocks_user_params >>
  disch_then (qspec_then `fn` mp_tac) >>
  gvs[fn_pass_step_def, fn_user_param_insts_def, fn_entry_insts_def,
      entry_block_def]
QED
