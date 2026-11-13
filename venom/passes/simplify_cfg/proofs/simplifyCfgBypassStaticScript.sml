(* Graph boundaries for the exact trivial-jump bypass. *)
Theory simplifyCfgBypassStatic
Ancestors
  simplifyCfgShapeCore
  simplifyCfgBypassPhi simplifyCfgMergeStatic simplifyCfgDefs
  cfgTransform venomInst venomWf list rich_list
  simplifyCfgDataflow simplifyCfgGraphShape

Theorem scfg_bypass_preds:
  lookup_block a.bb_label fn.fn_blocks = SOME a /\ can_bypass_jump fn a b ==>
  block_preds fn b.bb_label = [a]
Proof
  strip_tac >>
  `MEM a fn.fn_blocks` by metis_tac[lookup_block_member_label] >>
  `MEM a (block_preds fn b.bb_label)` by
    fs[can_bypass_jump_def, block_preds_def, MEM_FILTER] >>
  `LENGTH (block_preds fn b.bb_label) = 1` by
    fs[can_bypass_jump_def, num_preds_def] >>
  namedCases_on `block_preds fn b.bb_label` ["", "p rest"] >> gvs[] >>
  Cases_on `rest` >> gvs[]
QED

Theorem scfg_bypass_target_distinct:
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  bb_succs b = [target] ==> target <> b.bb_label
Proof
  strip_tac >> strip_tac >> drule_all scfg_bypass_preds >> strip_tac >>
  `MEM b fn.fn_blocks` by metis_tac[lookup_block_member_label] >>
  `MEM b (block_preds fn b.bb_label)` by
    (pure_rewrite_tac[block_preds_def, MEM_FILTER] >> simp[]) >>
  `a = b` by metis_tac[MEM] >> gvs[can_bypass_jump_def]
QED

Theorem scfg_bypass_not_entry:
  unitShapeDefs$first_block_no_preds fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\ can_bypass_jump fn a b ==>
  fn_entry_label fn <> SOME b.bb_label
Proof
  strip_tac >>
  `MEM a fn.fn_blocks` by metis_tac[lookup_block_member_label] >>
  Cases_on `fn.fn_blocks` >>
  fs[unitShapeDefsTheory.first_block_no_preds_def, EVERY_MEM,
    fn_entry_label_def, entry_block_def, can_bypass_jump_def] >> metis_tac[MEM]
QED

Theorem scfg_bypass_lookup:
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\
  can_bypass_jump fn a b /\ bb_succs b = [target] /\
  lookup_block target fn.fn_blocks = SOME t /\
  do_merge_jump fn a b lm = SOME (fn', lm') ==>
  lookup_block l fn'.fn_blocks =
    if l = b.bb_label then NONE
    else if l = a.bb_label then SOME (a with bb_instructions :=
      if target = a.bb_label then
        MAP (update_phi_bypass a.bb_label b.bb_label)
          (MAP (\i. if ~is_terminator i.inst_opcode then i
            else canon_jnz_inst (subst_label_inst b.bb_label target i)) a.bb_instructions)
      else MAP (\i. if ~is_terminator i.inst_opcode then i
        else canon_jnz_inst (subst_label_inst b.bb_label target i)) a.bb_instructions)
    else if l = target then SOME (t with bb_instructions :=
      MAP (update_phi_bypass a.bb_label b.bb_label) t.bb_instructions)
    else lookup_block l fn.fn_blocks
Proof
  strip_tac >>
  `a.bb_label <> b.bb_label` by metis_tac[can_bypass_jump_labels_distinct] >>
  `target <> b.bb_label` by metis_tac[scfg_bypass_target_distinct] >>
  `t.bb_label = target` by metis_tac[lookup_block_member_label] >>
  Cases_on `target = a.bb_label` >>
  fs[do_merge_jump_def] >> gvs[] >>
  simp[scfg_lookup_replace, scfg_lookup_remove] >>
  Cases_on `l = b.bb_label` >> Cases_on `l = a.bb_label` >>
  Cases_on `l = t.bb_label` >> gvs[]
QED

Theorem scfg_bypass_entry:
  fn_entry_label fn <> SOME b.bb_label /\
  do_merge_jump fn a b lm = SOME (fn', lm') ==>
  fn_entry_label fn' = fn_entry_label fn
Proof
  strip_tac >>
  gvs[do_merge_jump_def, AllCaseEqs()] >>
  rename1 `lookup_block tl fn.fn_blocks = SOME tb` >>
  `tb.bb_label = tl` by metis_tac[lookup_block_member_label] >>
  simp[scfg_entry_labels, fn_labels_def,
    cfgTransformPropsTheory.fn_labels_replace_block,
    cfgTransformPropsTheory.fn_labels_remove_block] >>
  Cases_on `fn.fn_blocks` >>
  gvs[fn_entry_label_def, entry_block_def, FILTER]
QED

Theorem scfg_canon_subst_successors:
  simplifyCfgShapeCore$scfg_label_positions i ==>
  (MEM l (get_successors (canon_jnz_inst (subst_label_inst old new i))) <=>
   ?k. MEM k (get_successors i) /\ l = if k = old then new else k)
Proof
  strip_tac >>
  rewrite_tac[GSYM subst_label_inst_successors_mem] >>
  namedCases_on `i.inst_operands` ["", "c xs"] >>
  simp[subst_label_inst_def, canon_jnz_inst_def] >>
  namedCases_on `xs` ["", "t ys"] >>
  simp[subst_label_inst_def, canon_jnz_inst_def] >>
  namedCases_on `ys` ["", "f zs"] >>
  simp[subst_label_inst_def, canon_jnz_inst_def] >>
  Cases_on `zs` >> simp[subst_label_inst_def, canon_jnz_inst_def] >>
  IF_CASES_TAC >> simp[] >>
  gvs[scfg_label_positions_def, unitShapeDefsTheory.label_positions_ok_def] >>
  Cases_on `c` >> Cases_on `t` >> Cases_on `f` >>
  gvs[stackPlanTypesTheory.is_label_operand_def, subst_label_op_def,
    venomStateTheory.get_label_def, get_successors_def, is_terminator_def] >>
  rpt IF_CASES_TAC >> gvs[venomStateTheory.get_label_def]
QED

Theorem scfg_bypass_source_succs:
  EVERY simplifyCfgShapeCore$scfg_label_positions bb.bb_instructions ==>
  (MEM l (bb_succs (bb with bb_instructions :=
    MAP (\i. if ~is_terminator i.inst_opcode then i
      else canon_jnz_inst (subst_label_inst old new i)) bb.bb_instructions)) <=>
   ?k. MEM k (bb_succs bb) /\ l = if k = old then new else k)
Proof
  Cases_on `bb.bb_instructions` using SNOC_CASES
  >- simp[bb_succs_def] >>
  rename1 `bb.bb_instructions = SNOC i xs` >>
  simp[EVERY_SNOC, MAP_SNOC, bb_succs_def, SNOC_APPEND] >>
  Cases_on `xs` >>
  simp[LAST_APPEND_CONS, LAST_CONS_cond, MEM_nub, MEM_REVERSE] >>
  rpt strip_tac >>
  (Cases_on `is_terminator i.inst_opcode`
   >- simp[scfg_canon_subst_successors] >>
   simp[get_successors_def])
QED

Theorem scfg_bypass_source_self_succs:
  EVERY simplifyCfgShapeCore$scfg_label_positions bb.bb_instructions ==>
  (MEM l (bb_succs (bb with bb_instructions :=
    if self then MAP (update_phi_bypass a b)
      (MAP (\i. if ~is_terminator i.inst_opcode then i
        else canon_jnz_inst (subst_label_inst b target i)) bb.bb_instructions)
    else MAP (\i. if ~is_terminator i.inst_opcode then i
      else canon_jnz_inst (subst_label_inst b target i)) bb.bb_instructions)) <=>
   ?k. MEM k (bb_succs bb) /\ l = if k = b then target else k)
Proof
  strip_tac >> Cases_on `self` >>
  simp[bb_succs_update_phi_bypass_map, scfg_bypass_source_succs]
QED

Theorem scfg_lookup_edge:
  ALL_DISTINCT (fn_labels fn) ==>
  (venomWf$fn_cfg_edge fn x y <=>
   ?bb. lookup_block x fn.fn_blocks = SOME bb /\ MEM y (bb_succs bb))
Proof
  strip_tac >> simp[simplifyCfgLabelPropsTheory.fn_cfg_edge_iff_fn_succ] >>
  Cases_on `lookup_block x fn.fn_blocks` >> simp[fn_succ_def]
QED

Theorem scfg_bypass_edge_redirect:
  ALL_DISTINCT (fn_labels fn) /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\
  can_bypass_jump fn a b /\ bb_succs b = [target] /\
  lookup_block target fn.fn_blocks = SOME t /\
  EVERY simplifyCfgShapeCore$scfg_label_positions a.bb_instructions /\
  do_merge_jump fn a b lm = SOME (fn', lm') ==>
  (venomWf$fn_cfg_edge fn' x y <=> x <> b.bb_label /\
    if x = a.bb_label then
      ?k. venomWf$fn_cfg_edge fn x k /\ y = if k = b.bb_label then target else k
    else venomWf$fn_cfg_edge fn x y)
Proof
  strip_tac >>
  `ALL_DISTINCT (fn_labels fn')` by
    (drule simplifyCfgGraphShapeTheory.do_merge_jump_labels >> simp[FILTER_ALL_DISTINCT]) >>
  simp[scfg_lookup_edge] >>
  drule_all scfg_bypass_lookup >>
  disch_then (qspec_then `x` assume_tac) >>
  Cases_on `x = b.bb_label` >> gvs[] >>
  Cases_on `x = a.bb_label` >> gvs[]
  >- (Cases_on `target = a.bb_label` >>
      gvs[bb_succs_update_phi_bypass_map, scfg_bypass_source_succs]) >>
  Cases_on `x = target` >> gvs[]
  >- simp[bb_succs_update_phi_bypass_map] >>
  metis_tac[]
QED
