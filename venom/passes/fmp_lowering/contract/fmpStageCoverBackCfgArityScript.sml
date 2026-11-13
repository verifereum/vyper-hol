Theory fmpStageCoverBackCfgArity
Ancestors
  o1PassContract o1ContractMakeSsaSrcOpcodes cfgNormSupplySim
  cfgNormSupplyProofs cfgNormDefs cfgTransform cfgTransformProps
  venomPassDispatcher irSupply callLayoutDefs venomInst list
  fmpStepBridge venomFnScheduleRunner venomFnScheduleRunnerProps
  simplifyCfgCollapseShape simplifyCfgGraphShape simplifyCfgInvariant
  simplifyCfgDefs simplifyCfgShape unitShapeDefs venomWf rich_list arithmetic

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

(* SimplifyCFG cannot discard user parameters from its protected entry. *)

Theorem scfg_param_map_count[local]:
  !xs. (!i. MEM i xs ==> ((h i).inst_opcode = PARAM <=> i.inst_opcode = PARAM)) ==>
  LENGTH (FILTER (\i. i.inst_opcode = PARAM) (MAP h xs)) =
  LENGTH (FILTER (\i. i.inst_opcode = PARAM) xs)
Proof
  Induct >- simp[] >> qx_gen_tac `y` >> simp[] >> rpt strip_tac >>
  `LENGTH (FILTER (\i. i.inst_opcode = PARAM) (MAP h xs)) =
   LENGTH (FILTER (\i. i.inst_opcode = PARAM) xs)` by
    (first_x_assum irule >> metis_tac[]) >>
  Cases_on `y.inst_opcode = PARAM` >> simp[]
QED

Theorem scfg_entry_count_blocks[local]:
  fn.fn_blocks <> [] ==>
  LENGTH (fn_user_param_insts fn) =
  LENGTH (FILTER (\i. i.inst_opcode = PARAM) (HD fn.fn_blocks).bb_instructions)
Proof
  Cases_on `fn.fn_blocks` >>
  simp[fn_user_param_insts_def, fn_entry_insts_def, entry_block_def]
QED

Theorem scfg_front_param_count[local]:
  !xs. xs <> [] /\ is_terminator (LAST xs).inst_opcode ==>
  LENGTH (FILTER (\i. i.inst_opcode = PARAM) (FRONT xs)) =
  LENGTH (FILTER (\i. i.inst_opcode = PARAM) xs)
Proof
  Induct >> simp[] >> qx_gen_tac `head` >> Cases_on `xs`
  >- (simp[] >> strip_tac >> Cases_on `head.inst_opcode` >>
      gvs[is_terminator_def]) >>
  simp[] >> strip_tac >>
  `LENGTH (FILTER (\i. i.inst_opcode = PARAM) (FRONT (h::t))) =
   LENGTH (FILTER (\i. i.inst_opcode = PARAM) (h::t))` by
    (first_x_assum irule >> simp[]) >>
  Cases_on `head.inst_opcode = PARAM` >> simp[]
QED

Theorem scfg_head_replace_count[local]:
  bs <> [] /\
  (bb.bb_label = (HD bs).bb_label ==>
   LENGTH (FILTER (\i. i.inst_opcode = PARAM) bb.bb_instructions) >=
   LENGTH (FILTER (\i. i.inst_opcode = PARAM) (HD bs).bb_instructions)) ==>
  LENGTH (FILTER (\i. i.inst_opcode = PARAM) (HD bs).bb_instructions) <=
  LENGTH (FILTER (\i. i.inst_opcode = PARAM)
    (HD (replace_block bb.bb_label bb bs)).bb_instructions)
Proof
  Cases_on `bs` >> simp[replace_block_def] >> rpt strip_tac >>
  Cases_on `h.bb_label = bb.bb_label` >> gvs[]
QED

Theorem scfg_update_succ_count[local]:
  !succs bs. bs <> [] ==>
  LENGTH (FILTER (\i. i.inst_opcode = PARAM)
    (HD (update_succ_phi_labels old new bs succs)).bb_instructions) =
  LENGTH (FILTER (\i. i.inst_opcode = PARAM) (HD bs).bb_instructions)
Proof
  Induct >- simp[update_succ_phi_labels_def] >> rpt strip_tac >>
  pure_once_rewrite_tac[update_succ_phi_labels_def] >> simp[] >>
  qpat_x_assum `!bs. _` (assume_tac o SRULE [update_succ_phi_labels_def, LET_THM]) >>
  Cases_on `lookup_block h bs` >- simp[] >> simp[] >>
  rename1 `lookup_block h bs = SOME bb` >>
  `bb.bb_label = h` by metis_tac[lookup_block_member_label] >>
  `bs <> []` by simp[] >>
  `replace_block h (bb with bb_instructions :=
    MAP (\i. if i.inst_opcode <> PHI then i else subst_label_inst old new i)
      bb.bb_instructions) bs <> []` by
    (Cases_on `bs` >> simp[replace_block_def] >> rw[]) >>
  first_x_assum drule >> disch_then SUBST1_TAC >>
  Cases_on `bs` >- gvs[] >>
  rename1 `lookup_block h (b0::rest) = SOME bb` >>
  simp[replace_block_def] >>
  Cases_on `b0.bb_label = h` >> simp[] >>
  `b0 = bb` by gvs[lookup_block_def, FIND_thm] >> gvs[] >>
  irule scfg_param_map_count >> simp[subst_label_inst_def] >> rw[]
QED

Theorem scfg_merge_entry_count[local]:
  f.fn_blocks <> [] /\ first_block_no_preds f /\
  EVERY bb_well_formed f.fn_blocks /\
  lookup_block lbl f.fn_blocks = SOME a /\
  lookup_block next f.fn_blocks = SOME b /\ can_merge_blocks f a b ==>
  LENGTH (FILTER (\i. i.inst_opcode = PARAM) (HD f.fn_blocks).bb_instructions) <=
  LENGTH (FILTER (\i. i.inst_opcode = PARAM)
    (HD (update_succ_phi_labels next lbl
      (replace_block lbl (merge_blocks a b) (remove_block next f.fn_blocks))
      (bb_succs (merge_blocks a b)))).bb_instructions)
Proof
  strip_tac >>
  `a.bb_label = lbl /\ b.bb_label = next /\ MEM a f.fn_blocks` by
    metis_tac[lookup_block_member_label] >>
  `next <> (HD f.fn_blocks).bb_label` by
    metis_tac[can_merge_blocks_not_entry] >>
  `remove_block next f.fn_blocks <> [] /\
   HD (remove_block next f.fn_blocks) = HD f.fn_blocks` by
    (irule remove_block_head >> simp[]) >>
  `replace_block lbl (merge_blocks a b) (remove_block next f.fn_blocks) <> []` by
    (irule (cj 1 replace_block_head_label) >> simp[merge_blocks_def]) >>
  simp[scfg_update_succ_count] >>
  `lbl = (merge_blocks a b).bb_label` by simp[merge_blocks_def] >>
  pop_assum SUBST1_TAC >>
  qpat_assum `HD (remove_block _ _) = _`
    (fn th => GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [GSYM th]) >>
  irule scfg_head_replace_count >> simp[] >> strip_tac >>
  `HD f.fn_blocks = a` by
    (Cases_on `f.fn_blocks` >>
     gvs[lookup_block_def, FIND_thm, merge_blocks_def]) >>
  `a.bb_instructions <> [] /\ is_terminator (LAST a.bb_instructions).inst_opcode` by
    gvs[EVERY_MEM, bb_well_formed_def] >>
  simp[merge_blocks_def, FILTER_APPEND, scfg_front_param_count]
QED

Theorem scfg_bypass_entry_count[local]:
  f.fn_blocks <> [] /\ first_block_no_preds f /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  can_bypass_jump f a b /\ do_merge_jump f a b lm = SOME (g,lm') ==>
  LENGTH (FILTER (\i. i.inst_opcode = PARAM) (HD f.fn_blocks).bb_instructions) <=
  LENGTH (FILTER (\i. i.inst_opcode = PARAM) (HD g.fn_blocks).bb_instructions)
Proof
  strip_tac >>
  `b.bb_label <> (HD f.fn_blocks).bb_label` by
    metis_tac[can_bypass_jump_not_entry] >>
  `remove_block b.bb_label f.fn_blocks <> [] /\
   HD (remove_block b.bb_label f.fn_blocks) = HD f.fn_blocks` by
    (irule remove_block_head >> simp[]) >>
  `!i. ((update_phi_bypass a.bb_label b.bb_label i).inst_opcode = PARAM <=>
         i.inst_opcode = PARAM)` by (simp[update_phi_bypass_def] >> rw[]) >>
  `!target_lbl i. ((if ~is_terminator i.inst_opcode then i else
        canon_jnz_inst (subst_label_inst b.bb_label target_lbl i)).inst_opcode = PARAM
        <=> i.inst_opcode = PARAM)` by
    (rpt gen_tac >> IF_CASES_TAC >- simp[] >>
     `i.inst_opcode <> PARAM` by
       (Cases_on `i.inst_opcode` >> gvs[is_terminator_def]) >>
     simp[] >>
     Cases_on `canon_jnz_inst (subst_label_inst b.bb_label target_lbl i) =
               subst_label_inst b.bb_label target_lbl i`
     >- gvs[subst_label_inst_def] >>
     drule canon_jnz_inst_changed >> strip_tac >> gvs[]) >>
  qpat_x_assum `do_merge_jump _ _ _ _ = _` mp_tac >>
  simp[do_merge_jump_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  `target.bb_label = target_lbl` by metis_tac[lookup_block_member_label] >>
  Cases_on `f.fn_blocks` >> gvs[remove_block_def, replace_block_def] >>
  Cases_on `h.bb_label = target.bb_label` >>
  Cases_on `h.bb_label = a.bb_label` >>
  Cases_on `target.bb_label = a.bb_label` >>
  simp[] >>
  qpat_x_assum `lookup_block a.bb_label _ = _` mp_tac >>
  qpat_x_assum `lookup_block target.bb_label _ = _` mp_tac >>
  simp[lookup_block_def, FIND_thm] >> rpt strip_tac >>
  simp[scfg_param_map_count] >> metis_tac[]
QED

val collapse_shape = ``\e f.
  ALL_DISTINCT (fn_labels f) /\ f.fn_blocks <> [] /\
  EVERY bb_well_formed f.fn_blocks /\
  EVERY inst_wf (fn_insts f) /\ EVERY label_positions_ok (fn_insts f) /\
  first_block_no_preds f /\ fn_succs_closed f /\
  (!bb i l. MEM bb f.fn_blocks /\ MEM i bb.bb_instructions /\
    i.inst_opcode = PHI /\ MEM (Label l) i.inst_operands ==>
    MEM l (pred_labels f bb.bb_label)) /\
  (HD f.fn_blocks).bb_label = e``;

val structural_shape = ``\e f.
  ALL_DISTINCT (fn_labels f) /\ f.fn_blocks <> [] /\
  EVERY bb_well_formed f.fn_blocks /\
  EVERY inst_wf (fn_insts f) /\ EVERY label_positions_ok (fn_insts f) /\
  first_block_no_preds f /\ fn_succs_closed f /\
  (HD f.fn_blocks).bb_label = e``;

val iteration_shape = ``\e f. ^structural_shape e f /\ fn_label_refs_ok f /\
  EVERY (\i. i.inst_opcode <> PHI) (HD f.fn_blocks).bb_instructions``;

Theorem scfg_collapse_count[local]:
  !f lm vis lbl. ^collapse_shape e f /\
    n <= LENGTH (fn_user_param_insts f) ==>
    n <= LENGTH (fn_user_param_insts (FST (collapse_dfs f lm vis lbl)))
Proof
  mp_tac (Q.INST [`Q` |-> `\f. ^collapse_shape e f /\
    n <= LENGTH (fn_user_param_insts f)`] collapse_dfs_preserves_predicate) >>
  reverse impl_tac
  >- (strip_tac >> rpt gen_tac >> strip_tac >>
      first_x_assum (qspecl_then [`f`, `lm`, `vis`, `lbl`] mp_tac) >> simp[]) >>
  conj_tac >> rpt gen_tac >> BETA_TAC >> strip_tac
  >- (drule_all (BETA_RULE do_merge_jump_collapse_shape) >> strip_tac >>
      drule_all scfg_bypass_entry_count >> strip_tac >>
      conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      gvs[scfg_entry_count_blocks] >> decide_tac) >>
  drule_all (BETA_RULE chain_merge_collapse_shape) >> strip_tac >>
  drule_all scfg_merge_entry_count >> strip_tac >>
  conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  gvs[scfg_entry_count_blocks] >> decide_tac
QED

Theorem scfg_remove_count[local]:
  f.fn_blocks <> [] ==>
  LENGTH (fn_user_param_insts (remove_unreachable_blocks f)) =
  LENGTH (fn_user_param_insts f)
Proof
  strip_tac >> drule remove_unreachable_blocks_head >> strip_tac >>
  simp[scfg_entry_count_blocks]
QED

Theorem scfg_fix_count[local]:
  f.fn_blocks <> [] ==>
  LENGTH (fn_user_param_insts (fix_all_phis f)) = LENGTH (fn_user_param_insts f)
Proof
  strip_tac >>
  `!ps i. (fix_phi_inst ps i).inst_opcode = PARAM <=> i.inst_opcode = PARAM` by
    (rpt gen_tac >> eq_tac
     >- (strip_tac >> irule fix_phi_inst_opcode_source >> simp[] >> metis_tac[]) >>
     simp[fix_phi_inst_def]) >>
  Cases_on `f.fn_blocks` >> gvs[] >>
  simp[fn_user_param_insts_def, fn_entry_insts_def, entry_block_def,
    fix_all_phis_def, fix_phis_in_block_def, FILTER_APPEND, FILTER_FILTER] >>
  `(\(i:instruction). i.inst_opcode = PARAM /\ i.inst_opcode = PHI) = (\i. F)` by
    (simp[FUN_EQ_THM] >> gen_tac >> Cases_on `i.inst_opcode` >> simp[]) >>
  `(\(i:instruction). i.inst_opcode = PARAM /\ i.inst_opcode <> PHI) =
    (\i. i.inst_opcode = PARAM)` by
    (simp[FUN_EQ_THM] >> gen_tac >> Cases_on `i.inst_opcode` >> simp[]) >>
  simp[] >> irule scfg_param_map_count >> simp[]
QED

Theorem scfg_round_count[local]:
  ^structural_shape e f ==>
  LENGTH (fn_user_param_insts f) <=
  LENGTH (fn_user_param_insts (FST (simplify_cfg_round_with_labels f)))
Proof
  strip_tac >>
  `^structural_shape e (remove_unreachable_blocks f)` by
    (irule remove_unreachable_blocks_structural_shape >> simp[]) >>
  `^collapse_shape e (fix_all_phis (remove_unreachable_blocks f))` by
    (irule fix_all_phis_collapse_shape >> simp[]) >>
  `LENGTH (fn_user_param_insts (fix_all_phis (remove_unreachable_blocks f))) =
   LENGTH (fn_user_param_insts f)` by (fs[] >> simp[scfg_fix_count, scfg_remove_count]) >>
  Cases_on `fn_entry_label f`
  >- (Cases_on `f.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def]) >>
  qabbrev_tac `a = fix_all_phis (remove_unreachable_blocks f)` >>
  Cases_on `collapse_dfs a [] [] x` >> PairCases_on `r` >>
  `^collapse_shape e q` by
    (mp_tac (CONJUNCT1 collapse_dfs_shape_joint) >>
     disch_then drule >>
     disch_then (qspecl_then [`[]`, `[]`, `x`] mp_tac) >> simp[] >> metis_tac[]) >>
  `LENGTH (fn_user_param_insts a) <= LENGTH (fn_user_param_insts q)` by
    (qspec_then `a` mp_tac (Q.INST [`n` |-> `LENGTH (fn_user_param_insts a)`] scfg_collapse_count) >>
     disch_then (qspecl_then [`[]`, `[]`, `x`] mp_tac) >> simp[]) >>
  `subst_block_labels_fn r0 q = q` by
    (irule collapse_dfs_empty_log_subst_identity >> metis_tac[]) >>
  `^structural_shape e q` by gvs[] >>
  `^structural_shape e (remove_unreachable_blocks q)` by
    (irule remove_unreachable_blocks_structural_shape >> simp[]) >>
  simp[simplify_cfg_round_with_labels_def, Abbr `a`] >>
  Cases_on `r0 = []` >> fs[] >> simp[scfg_fix_count, scfg_remove_count]
QED

Theorem scfg_iter_count[local]:
  !n f. ^iteration_shape e f ==>
  LENGTH (fn_user_param_insts f) <=
  LENGTH (fn_user_param_insts (FST (simplify_cfg_iter_with_labels n f)))
Proof
  Induct_on `n` >- simp[simplify_cfg_iter_with_labels_def] >>
  rpt gen_tac >> strip_tac >>
  `^structural_shape e f` by gvs[] >>
  `^iteration_shape e (FST (simplify_cfg_round_with_labels f))` by
    (drule simplify_cfg_round_collapse_shape >> strip_tac >>
     drule simplify_cfg_round_label_refs_ok >> strip_tac >> gvs[]) >>
  `LENGTH (fn_user_param_insts f) <=
   LENGTH (fn_user_param_insts (FST (simplify_cfg_round_with_labels f)))` by
    (irule scfg_round_count >> gvs[]) >>
  pure_once_rewrite_tac[simplify_cfg_iter_with_labels_def] >>
  Cases_on `simplify_cfg_round_with_labels f` >> simp[] >>
  Cases_on `q.fn_blocks = f.fn_blocks` >- gvs[] >>
  Cases_on `simplify_cfg_iter_with_labels n q` >> simp[] >>
  first_x_assum (qspec_then `q` mp_tac) >> gvs[]
QED

Theorem scfg_fn_user_param_count[local]:
  ALL_DISTINCT (fn_labels fn) /\ fn.fn_blocks <> [] /\
  EVERY bb_well_formed fn.fn_blocks /\ EVERY inst_wf (fn_insts fn) /\
  EVERY label_positions_ok (fn_insts fn) /\ first_block_no_preds fn /\
  fn_succs_closed fn /\ fn_label_refs_ok fn /\
  EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions ==>
  LENGTH (fn_user_param_insts fn) <=
  LENGTH (fn_user_param_insts (simplify_cfg_fn fn))
Proof
  strip_tac >>
  `^iteration_shape (HD fn.fn_blocks).bb_label fn` by
    (BETA_TAC >> simp[]) >>
  simp[simplify_cfg_fn_def, simplify_cfg_fn_with_labels_def] >>
  irule scfg_iter_count >> qexists_tac `(HD fn.fn_blocks).bb_label` >>
  first_assum ACCEPT_TAC
QED

Theorem scfg_user_param_count:
  ALL_DISTINCT (fn_labels fn) /\ fn.fn_blocks <> [] /\
  EVERY bb_well_formed fn.fn_blocks /\ EVERY inst_wf (fn_insts fn) /\
  EVERY label_positions_ok (fn_insts fn) /\ first_block_no_preds fn /\
  fn_succs_closed fn /\ fn_label_refs_ok fn /\
  EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
  fn_pass_step rpolicy (CFP_Simple VP_SimplifyCFG) observed s fn out ==>
  LENGTH (fn_user_param_insts fn) <=
  LENGTH (fn_user_param_insts out.fpo_function)
Proof
  simp[fn_pass_step_def, execute_configured_fn_pass_simplify_cfg] >>
  Cases_on `simplify_cfg_fn_with_labels fn` >>
  simp[simplify_cfg_fn_def] >> rpt strip_tac >> gvs[] >>
  drule scfg_fn_user_param_count >> simp[simplify_cfg_fn_def]
QED
