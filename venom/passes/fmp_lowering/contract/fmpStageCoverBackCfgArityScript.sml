Theory fmpStageCoverBackCfgArity
Ancestors
  o1PassContract o1ContractMakeSsaSrcOpcodes cfgNormSupplySim
  cfgNormSupplyProofs cfgNormDefs cfgTransform cfgTransformProps
  venomPassDispatcher irSupply callLayoutDefs venomInst list
  fmpStepBridge venomFnScheduleRunner venomFnScheduleRunnerProps

Theorem subst_terminator_key[local]:
  block_key (subst_label_terminator old new bb) = block_key bb
Proof
  simp[block_key_def, subst_label_terminator_def,
       supply_subst_terminator_opcodes]
QED

Theorem update_split_phis_key[local]:
  block_key (update_phis_for_split old new repls bb) = block_key bb
Proof
  simp[block_key_def, update_phis_for_split_def,
       supply_update_phis_opcodes]
QED

Theorem insert_split_keys[local]:
  ALL_DISTINCT (fn_labels fn) /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  insert_split_supply s fn pred target = (fn',s') ==>
  ?extra. MAP block_key fn'.fn_blocks = MAP block_key fn.fn_blocks ++ [extra]
Proof
  strip_tac >>
  gvs[insert_split_supply_def, AllCaseEqs()] >>
  qmatch_goalsub_abbrev_tac `replace_block target.bb_label target' bbs` >>
  `MAP block_key bbs = MAP block_key fn.fn_blocks` by
    (simp[Abbr `bbs`] >> irule replace_block_key >>
     simp[GSYM fn_labels_def] >> qexists_tac `pred` >> simp[subst_terminator_key] >>
     metis_tac[venomExecProofsTheory.MEM_lookup_block, fn_labels_def]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs)` by
    metis_tac[block_key_labels, fn_labels_def] >>
  `MAP block_key (replace_block target.bb_label target' bbs) = MAP block_key bbs` by
    (irule replace_block_key >> simp[] >>
     Cases_on `pred.bb_label = target.bb_label`
     >- (qexists_tac `subst_label_terminator target.bb_label split_bb.bb_label pred` >>
         simp[Abbr `target'`, subst_terminator_key, update_split_phis_key] >>
         simp[Abbr `bbs`] >> irule lookup_block_replace_eq >>
         simp[subst_label_terminator_def] >>
         metis_tac[venomExecProofsTheory.MEM_lookup_block, fn_labels_def])
     >> qexists_tac `target` >>
     simp[Abbr `target'`, update_split_phis_key, Abbr `bbs`] >>
     simp[lookup_block_replace_neq, subst_label_terminator_def] >>
     metis_tac[venomExecProofsTheory.MEM_lookup_block, fn_labels_def]) >>
  simp[]
QED

Theorem cfg_round_keys[local]:
  ALL_DISTINCT (fn_labels fn) /\
  cfg_norm_round_supply s fn = (fn',changed,s') ==>
  ?extra. MAP block_key fn'.fn_blocks = MAP block_key fn.fn_blocks ++ extra
Proof
  strip_tac >> drule cfg_norm_round_supply_cases >> strip_tac >> gvs[] >>
  drule_all insert_split_keys >> strip_tac >> simp[]
QED

Theorem keys_entry_user_count[local]:
  MAP block_key fn'.fn_blocks = MAP block_key fn.fn_blocks ++ extra ==>
  LENGTH (fn_user_param_insts fn) <= LENGTH (fn_user_param_insts fn')
Proof
  Cases_on `fn.fn_blocks`
  >- simp[fn_user_param_insts_def, fn_entry_insts_def, entry_block_def] >>
  Cases_on `fn'.fn_blocks` >> simp[] >> strip_tac >>
  gvs[block_key_def, fn_user_param_insts_def, fn_entry_insts_def,
      entry_block_def] >>
  `kept_opcode PARAM` by simp[kept_opcode_def] >>
  simp[kept_opcode_count]
QED

Theorem forwarding_supply_labels[local]:
  !vars s repls insts s'.
  build_forwarding_assigns_supply s vars = (repls,insts,s') ==>
  s'.irs_used_labels = s.irs_used_labels
Proof
  Induct >> simp[build_forwarding_assigns_supply_def] >> rpt gen_tac >>
  strip_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >>
  gvs[fresh_ir_var_def, fresh_inst_id_def, AllCaseEqs()]
QED

Theorem split_supply_labels[local]:
  build_split_block_supply s pred target = (bb,repls,s') ==>
  ~MEM bb.bb_label s.irs_used_labels /\
  s'.irs_used_labels = bb.bb_label :: s.irs_used_labels
Proof
  simp[build_split_block_supply_def] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  drule fresh_ir_label_contract >> strip_tac >>
  drule forwarding_supply_labels >> strip_tac >>
  gvs[fresh_inst_id_def]
QED

Theorem cfg_round_label_transport[local]:
  EVERY (\l. MEM l s.irs_used_labels) (fn_labels fn) /\
  ALL_DISTINCT (fn_labels fn) /\
  cfg_norm_round_supply s fn = (fn',changed,s') ==>
  EVERY (\l. MEM l s'.irs_used_labels) (fn_labels fn') /\
  ALL_DISTINCT (fn_labels fn')
Proof
  strip_tac >> drule cfg_norm_round_supply_cases >> strip_tac >> gvs[] >>
  drule insert_split_supply_labels >> strip_tac >>
  drule split_supply_labels >> strip_tac >>
  gvs[EVERY_MEM, ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem cfg_iter_keys[local]:
  !n s fn fn' s'.
  EVERY (\l. MEM l s.irs_used_labels) (fn_labels fn) /\
  ALL_DISTINCT (fn_labels fn) /\
  cfg_norm_iter_supply n s fn = (fn',s') ==>
  ?extra. MAP block_key fn'.fn_blocks = MAP block_key fn.fn_blocks ++ extra
Proof
  Induct >- simp[cfg_norm_iter_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `cfg_norm_round_supply s fn` >> PairCases_on `r` >>
  rename1 `cfg_norm_round_supply s fn = (fn1,changed,s1)` >>
  drule_all cfg_round_keys >> strip_tac >>
  drule_all cfg_round_label_transport >> strip_tac >>
  Cases_on `changed` >> gvs[cfg_norm_iter_supply_def]
  >- (first_x_assum drule_all >> strip_tac >>
      simp[APPEND_ASSOC] >> metis_tac[APPEND_ASSOC]) >>
  metis_tac[]
QED

Theorem cfg_function_user_count[local]:
  EVERY (\l. MEM l s.irs_used_labels) (fn_labels fn) /\
  ALL_DISTINCT (fn_labels fn) /\
  cfg_norm_function_supply s fn = (fn',s') ==>
  LENGTH (fn_user_param_insts fn) <= LENGTH (fn_user_param_insts fn')
Proof
  simp[cfg_norm_function_supply_def] >> strip_tac >>
  drule_all cfg_iter_keys >> strip_tac >>
  irule keys_entry_user_count >> metis_tac[]
QED

Theorem fmp_cfg_normalization_user_count:
  fn_pass_step rpolicy (CFP_Simple VP_CFGNormalization) observed supply fn out /\
  ALL_DISTINCT (fn_labels fn) ==>
  LENGTH (fn_user_param_insts fn) <=
  LENGTH (fn_user_param_insts out.fpo_function)
Proof
  strip_tac >>
  `ir_supply_covers_fn supply fn` by
    (irule ir_supply_covers_unit_member >> qexists_tac `observed` >>
     gvs[fn_pass_step_def] >>
     drule lookup_unique_function_member >> simp[]) >>
  `EVERY (\l. MEM l supply.irs_used_labels) (fn_labels fn)` by
    (gvs[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM] >>
     metis_tac[MEM_fn_labels_fn_ir_labels]) >>
  gvs[fn_pass_step_def, AllCaseEqs()] >>
  irule cfg_function_user_count >> metis_tac[]
QED
