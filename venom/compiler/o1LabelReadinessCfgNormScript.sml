Theory o1LabelReadinessCfgNorm
Ancestors
  o1PassContract cfgNormDefs cfgTransform o1ContractCfgNormStep
  unitShapeDefs irSupply venomInst list rich_list venomPassDispatcher

(* Both block names and operands avoid the forbidden symbol. *)
Definition cfg_label_absent_def:
  cfg_label_absent l fn <=>
    EVERY (\bb. bb.bb_label <> l /\
      EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions) fn.fn_blocks
End

Theorem subst_terminator_label_absent[local]:
  EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions /\ new <> l ==>
  EVERY (\i. ~MEM (Label l) i.inst_operands)
    (subst_label_terminator old new bb).bb_instructions
Proof
  simp[subst_label_terminator_def, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> Cases_on `is_terminator inst.inst_opcode` >>
  gvs[subst_label_inst_def, MEM_MAP] >>
  rename1 `Label l = subst_label_op old new op` >> Cases_on `op` >>
  gvs[subst_label_op_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem update_phis_label_absent[local]:
  EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions /\ new <> l ==>
  EVERY (\i. ~MEM (Label l) i.inst_operands)
    (update_phis_for_split old new repls bb).bb_instructions
Proof
  simp[update_phis_for_split_def, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> Cases_on `inst.inst_opcode = PHI` >> gvs[] >>
  metis_tac[cfgNormSupplySimTheory.supply_update_phi_ops_label_origin]
QED

Theorem forwarding_label_absent[local]:
  !vars s repls insts s'.
  build_forwarding_assigns_supply s vars = (repls,insts,s') ==>
  EVERY (\i. ~MEM (Label l) i.inst_operands) insts
Proof
  Induct >> simp[build_forwarding_assigns_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem split_label_absent[local]:
  build_split_block_supply s pred target = (split,repls,s') /\
  target.bb_label <> "runtime_begin" ==>
  split.bb_label <> "runtime_begin" /\
  EVERY (\i. ~MEM (Label "runtime_begin") i.inst_operands) split.bb_instructions
Proof
  strip_tac >>
  `split.bb_label <> "runtime_begin"` by
    (drule supply_split_not_reserved >> simp[reserved_label_def] >> metis_tac[]) >>
  gvs[build_split_block_supply_def, AllCaseEqs()] >>
  drule forwarding_label_absent >> simp[]
QED

Theorem insert_split_label_absent[local]:
  cfg_label_absent "runtime_begin" fn /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  insert_split_supply s fn pred target = (fn',s') ==>
  cfg_label_absent "runtime_begin" fn'
Proof
  strip_tac >>
  Cases_on `build_split_block_supply s pred target` >> PairCases_on `r` >>
  rename1 `build_split_block_supply s pred target = (split,repls,s1)` >>
  `target.bb_label <> "runtime_begin"` by
    (fs[cfg_label_absent_def, EVERY_MEM] >> metis_tac[]) >>
  drule_all split_label_absent >> strip_tac >>
  `EVERY (\i. ~MEM (Label "runtime_begin") i.inst_operands) pred.bb_instructions /\
   EVERY (\i. ~MEM (Label "runtime_begin") i.inst_operands) target.bb_instructions` by
    (fs[cfg_label_absent_def, EVERY_MEM] >> metis_tac[]) >>
  gvs[insert_split_supply_def, cfg_label_absent_def] >>
  simp[EVERY_APPEND] >>
  irule cfgNormSupplyProofsTheory.EVERY_replace_block_covered >> reverse conj_tac
  >- (irule cfgNormSupplyProofsTheory.EVERY_replace_block_covered >>
      simp[] >>
      gvs[subst_terminator_label_absent, subst_label_terminator_def, EVERY_MEM]) >>
  Cases_on `pred.bb_label = target.bb_label` >> gvs[] >>
  irule update_phis_label_absent >> simp[] >>
  irule subst_terminator_label_absent >> simp[]
QED

Theorem find_split_label_absent[local]:
  !bbs fn s fn' changed s'.
  cfg_label_absent "runtime_begin" fn /\
  EVERY (\bb. MEM bb fn.fn_blocks) bbs /\
  find_and_split_supply fn s bbs = (fn',changed,s') ==>
  cfg_label_absent "runtime_begin" fn'
Proof
  Induct_on `bbs` >> rpt strip_tac
  >- gvs[find_and_split_supply_def] >>
  Cases_on `LENGTH (block_preds fn h.bb_label) <= 1`
  >- (gvs[find_and_split_supply_def] >> metis_tac[]) >>
  Cases_on `FIND (\p. num_succs p > 1) (block_preds fn h.bb_label)`
  >- (gvs[find_and_split_supply_def] >> metis_tac[]) >>
  Cases_on `insert_split_supply s fn x h` >>
  gvs[find_and_split_supply_def] >>
  `MEM x (block_preds fn h.bb_label)` by metis_tac[cfgNormSupplyProofsTheory.FIND_SOME_MEM] >>
  `MEM x fn.fn_blocks` by gvs[block_preds_def, MEM_FILTER] >>
  metis_tac[insert_split_label_absent]
QED

Theorem iter_label_absent[local]:
  !n s fn fn' s'.
  cfg_label_absent "runtime_begin" fn /\
  cfg_norm_iter_supply n s fn = (fn',s') ==>
  cfg_label_absent "runtime_begin" fn'
Proof
  Induct >> rpt strip_tac
  >- gvs[cfg_norm_iter_supply_def] >>
  Cases_on `cfg_norm_round_supply s fn` >> PairCases_on `r` >>
  rename1 `cfg_norm_round_supply s fn = (fn1,changed,s1)` >>
  `cfg_label_absent "runtime_begin" fn1` by
    (irule find_split_label_absent >>
     qexistsl [`fn.fn_blocks`, `changed`, `fn`, `s`, `s1`] >>
     gvs[cfg_norm_round_supply_def, EVERY_MEM]) >>
  gvs[cfg_norm_iter_supply_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem cfgnorm_pass_no_runtime_begin:
 !rpolicy observed s fn out.
 fn_pass_step rpolicy (CFP_Simple VP_CFGNormalization) observed s fn out /\
 o1_fn_shape observed.cu_context fn /\
 (!i. MEM i (fn_insts fn) ==> ~MEM (Label "runtime_begin") i.inst_operands) ==>
 !i. MEM i (fn_insts out.fpo_function) ==> ~MEM (Label "runtime_begin") i.inst_operands
Proof
  rpt gen_tac >> strip_tac >>
  `cfg_label_absent "runtime_begin" fn` by
    (gvs[cfg_label_absent_def, o1_fn_shape_def, fn_shape_ok_def,
         EVERY_MEM, reserved_label_def] >>
     rpt strip_tac >>
     `MEM i (fn_insts fn)` by
       (simp[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
     metis_tac[]) >>
  gvs[fn_pass_step_def, execute_configured_fn_pass_def, AllCaseEqs()] >>
  gvs[cfg_norm_function_supply_def] >>
  drule_all iter_label_absent >>
  simp[cfg_label_absent_def, EVERY_MEM, fn_insts_def,
       MEM_fn_insts_blocks_iff] >> metis_tac[]
QED
