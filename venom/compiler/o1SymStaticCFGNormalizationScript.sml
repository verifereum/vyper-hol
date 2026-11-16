Theory o1SymStaticCFGNormalization
Ancestors
  cfgNormSupplySim cfgNormSupplyProofs cfgNormDefs cfgTransform irSupply
  venomInst unitShapeDefs o1PassContract list

Theorem cfg_static_fresh_label:
  fresh_ir_label s = (l,s') ==> l <> "runtime_begin"
Proof
  simp[fresh_ir_label_def, AllCaseEqs()] >> rpt strip_tac >>
  drule seek_fresh_name_interface >> simp[]
QED

Theorem cfg_static_subst:
  EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions /\
  new <> l ==>
  EVERY (\i. ~MEM (Label l) i.inst_operands)
    (subst_label_terminator old new bb).bb_instructions
Proof
  simp[subst_label_terminator_def] >>
  pure_rewrite_tac[EVERY_MAP, EVERY_MEM] >> simp[] >>
  rpt strip_tac >> Cases_on `is_terminator e.inst_opcode` >>
  gvs[subst_label_inst_def] >>
  metis_tac[supply_subst_label_ops_label_origin]
QED

Theorem cfg_static_phis:
  EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions /\
  new <> l ==>
  EVERY (\i. ~MEM (Label l) i.inst_operands)
    (update_phis_for_split old new repls bb).bb_instructions
Proof
  simp[update_phis_for_split_def] >>
  pure_rewrite_tac[EVERY_MAP, EVERY_MEM] >> simp[] >>
  rpt strip_tac >> Cases_on `e.inst_opcode = PHI` >> gvs[] >>
  metis_tac[supply_update_phi_ops_label_origin]
QED

Theorem cfg_static_split:
  build_split_block_supply s pred target = (split,repls,s') /\
  target.bb_label <> "runtime_begin" ==>
  split.bb_label <> "runtime_begin" /\
  EVERY (\i. ~MEM (Label "runtime_begin") i.inst_operands)
    split.bb_instructions
Proof
  Cases_on `fresh_ir_label s` >> rename1 `fresh_ir_label s = (lbl,s1)` >>
  Cases_on `build_forwarding_assigns_supply s1
    (nub (phi_vars_needing_forward pred.bb_label pred target.bb_instructions))` >>
  PairCases_on `r` >> Cases_on `fresh_inst_id r1` >>
  gvs[build_split_block_supply_def] >> strip_tac >>
  drule cfg_static_fresh_label >> strip_tac >> simp[] >>
  drule supply_forwarding_no_labels >> strip_tac >>
  gvs[EVERY_MEM, MEM_APPEND] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem cfg_static_insert:
  EVERY (\bb. bb.bb_label <> "runtime_begin" /\
    EVERY (\i. ~MEM (Label "runtime_begin") i.inst_operands)
      bb.bb_instructions) f.fn_blocks /\
  MEM pred f.fn_blocks /\ MEM target f.fn_blocks /\
  insert_split_supply s f pred target = (g,s') ==>
  EVERY (\bb. bb.bb_label <> "runtime_begin" /\
    EVERY (\i. ~MEM (Label "runtime_begin") i.inst_operands)
      bb.bb_instructions) g.fn_blocks
Proof
  strip_tac >> Cases_on `build_split_block_supply s pred target` >>
  PairCases_on `r` >> rename1 `build_split_block_supply s pred target = (split,rs,t)` >>
  `target.bb_label <> "runtime_begin" /\ pred.bb_label <> "runtime_begin" /\
   EVERY (\i. ~MEM (Label "runtime_begin") i.inst_operands) target.bb_instructions /\
   EVERY (\i. ~MEM (Label "runtime_begin") i.inst_operands) pred.bb_instructions` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_all cfg_static_split >> strip_tac >>
  `EVERY (\i. ~MEM (Label "runtime_begin") i.inst_operands)
     (subst_label_terminator target.bb_label split.bb_label pred).bb_instructions` by
    (irule cfg_static_subst >> simp[]) >>
  gvs[insert_split_supply_def] >>
  simp[EVERY_APPEND] >> irule EVERY_replace_block_covered >> reverse conj_tac
  >- (irule EVERY_replace_block_covered >> simp[subst_label_terminator_def]) >>
  `EVERY (\i. ~MEM (Label "runtime_begin") i.inst_operands)
    (update_phis_for_split pred.bb_label split.bb_label rs
      (if pred.bb_label = target.bb_label then
         subst_label_terminator target.bb_label split.bb_label pred else target)).bb_instructions` by
    (irule cfg_static_phis >> simp[] >>
     Cases_on `pred.bb_label = target.bb_label` >> simp[]) >>
  simp[update_phis_for_split_def, subst_label_terminator_def] >>
  Cases_on `pred.bb_label = target.bb_label` >>
  gvs[update_phis_for_split_def, subst_label_terminator_def]
QED

Theorem cfg_static_find:
  !bbs f s g changed s'.
  EVERY (\bb. bb.bb_label <> "runtime_begin" /\
    EVERY (\i. ~MEM (Label "runtime_begin") i.inst_operands)
      bb.bb_instructions) f.fn_blocks /\
  EVERY (\bb. MEM bb f.fn_blocks) bbs /\
  find_and_split_supply f s bbs = (g,changed,s') ==>
  EVERY (\bb. bb.bb_label <> "runtime_begin" /\
    EVERY (\i. ~MEM (Label "runtime_begin") i.inst_operands)
      bb.bb_instructions) g.fn_blocks
Proof
  Induct_on `bbs` >> rpt gen_tac
  >- (simp[find_and_split_supply_def] >> rpt strip_tac >> gvs[]) >>
  simp[Once find_and_split_supply_def] >>
  Cases_on `LENGTH (block_preds f h.bb_label) <= 1` >> simp[]
  >- metis_tac[] >>
  Cases_on `FIND (\p. num_succs p > 1) (block_preds f h.bb_label)` >> simp[]
  >- metis_tac[] >>
  Cases_on `insert_split_supply s f x h` >> simp[] >> rpt strip_tac >> gvs[] >>
  `MEM x f.fn_blocks` by
    (drule FIND_SOME_MEM >> simp[block_preds_def, MEM_FILTER]) >>
  metis_tac[cfg_static_insert]
QED

Theorem cfg_static_iter:
  !n s f g s'.
  EVERY (\bb. bb.bb_label <> "runtime_begin" /\
    EVERY (\i. ~MEM (Label "runtime_begin") i.inst_operands)
      bb.bb_instructions) f.fn_blocks /\
  cfg_norm_iter_supply n s f = (g,s') ==>
  EVERY (\bb. bb.bb_label <> "runtime_begin" /\
    EVERY (\i. ~MEM (Label "runtime_begin") i.inst_operands)
      bb.bb_instructions) g.fn_blocks
Proof
  Induct >> rpt gen_tac
  >- (simp[cfg_norm_iter_supply_def] >> rpt strip_tac >> gvs[]) >>
  Cases_on `cfg_norm_round_supply s f` >> PairCases_on `r` >>
  simp[cfg_norm_iter_supply_def] >> strip_tac >>
  `EVERY (\bb. bb.bb_label <> "runtime_begin" /\
    EVERY (\i. ~MEM (Label "runtime_begin") i.inst_operands)
      bb.bb_instructions) q.fn_blocks` by
    (irule cfg_static_find >> qexistsl [`f.fn_blocks`,`r0`,`f`,`s`,`r1`] >>
     gvs[cfg_norm_round_supply_def, EVERY_MEM] >> metis_tac[]) >>
  Cases_on `r0` >> gvs[] >> metis_tac[]
QED

Theorem cfg_norm_function_supply_runtime_reflect:
  o1_fn_shape C f /\ cfg_norm_function_supply s f = (g,s') ==>
  ((?i. MEM i (fn_insts g) /\ MEM (Label "runtime_begin") i.inst_operands) ==>
   (?i. MEM i (fn_insts f) /\ MEM (Label "runtime_begin") i.inst_operands))
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  `EVERY (\bb. bb.bb_label <> "runtime_begin" /\
    EVERY (\i. ~MEM (Label "runtime_begin") i.inst_operands)
      bb.bb_instructions) f.fn_blocks` by
    (gvs[o1_fn_shape_def, fn_shape_ok_def, reserved_label_def,
         fn_insts_def, EVERY_MEM, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  drule cfg_static_iter >>
  disch_then (qspecl_then [`2 * LENGTH f.fn_blocks`,`s`,`g`,`s'`] mp_tac) >>
  gvs[cfg_norm_function_supply_def, EVERY_MEM, fn_insts_def,
      MEM_fn_insts_blocks_iff, EXISTS_MEM] >>
  metis_tac[]
QED
