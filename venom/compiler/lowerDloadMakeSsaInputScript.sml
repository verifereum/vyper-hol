(*
 * LowerDload keeps make_ssa_input_ok, function by function.
 *
 * The expansion keeps labels, terminators, CFG edges and every PHI where
 * it was; it only replaces each DLOAD/DLOADBYTES by a run of
 * instructions whose new variables come from the supply and are defined
 * before their uses in the same run.  Distinct instruction ids pin a use
 * to one position of its block, which def_on_all_paths needs: it asks
 * for a definition before some occurrence of the use; instruction
 * well-formedness keeps DLOADBYTES output-free, since the expansion
 * would drop its outputs.
 *
 * TOP-LEVEL:
 *   lower_dload_fn_pass_step_make_ssa_input_ok
 *)
Theory lowerDloadMakeSsaInput
Ancestors
  o1ContractLowerDload o1PassContract lowerDloadDefs venomPassDispatcher
  venomFnScheduleRunner irSupply venomWf cfgWf venomInst list
  cfgNormSupplyProofs

Theorem lower_dload_step_supply:
  fn_pass_step rpolicy (CFP_Simple VP_LowerDload) observed s fn out ==>
  ir_supply_covers_fn s fn /\
  ?s'. lower_dload_function_supply s fn = (out.fpo_function,s')
Proof
  strip_tac >> gvs[fn_pass_step_def, AllCaseEqs()] >>
  `MEM fn observed.cu_context.ctx_functions` by
    (gvs[lookup_unique_function_def, AllCaseEqs()] >>
     `MEM fn (FILTER (\f. f.fn_name = fn.fn_name)
               observed.cu_context.ctx_functions)` by simp[] >>
     gvs[MEM_FILTER]) >>
  gvs[ir_supply_covers_unit_def, ir_supply_covers_fn_def,
      list_subset_def, unit_ir_inst_ids_def, unit_ir_vars_def,
      unit_ir_labels_def, EVERY_MEM, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem lower_dload_inst_supply_output_survives[local]:
  lower_dload_inst_supply s i = (xs,t) /\ inst_wf i /\
  MEM v i.inst_outputs ==> ?j. MEM j xs /\ MEM v j.inst_outputs
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      simp[RIGHT_AND_OVER_OR, EXISTS_OR_THM]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (rpt strip_tac >> gvs[inst_wf_def]) >>
  rpt strip_tac >> gvs[lower_dload_inst_supply_def]
QED

Theorem lower_dload_inst_supply_output_count[local]:
  lower_dload_inst_supply s i = (xs,t) /\ inst_wf i /\
  MEM v s.irs_used_vars ==>
  LENGTH (FILTER (\j. MEM v j.inst_outputs) xs) =
  if MEM v i.inst_outputs then 1 else 0
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> imp_res_tac (cj 1 fresh_ir_var_contract) >>
      imp_res_tac (cj 2 fresh_ir_var_contract) >>
      gvs[inst_wf_def] >> rpt IF_CASES_TAC >> gvs[] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> imp_res_tac (cj 1 fresh_ir_var_contract) >>
      imp_res_tac (cj 2 fresh_ir_var_contract) >>
      gvs[inst_wf_def] >> rpt IF_CASES_TAC >> gvs[] >> metis_tac[]) >>
  rpt strip_tac >> gvs[lower_dload_inst_supply_def] >>
  Cases_on `MEM v i.inst_outputs` >> simp[]
QED

Theorem lower_dload_inst_supply_ordered_operand[local]:
  lower_dload_inst_supply s i = (xs,t) /\ xs = pre ++ j::post /\
  j.inst_opcode <> PHI /\ MEM (Var v) j.inst_operands ==>
  (?d. MEM d pre /\ MEM v d.inst_outputs) \/
  (i.inst_opcode <> PHI /\ MEM (Var v) i.inst_operands)
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >>
      gvs[] >> qpat_x_assum `_ = _ ++ _` (mp_tac o SYM) >>
      simp[APPEND_EQ_CONS] >> rpt strip_tac >>
      gvs[RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
      metis_tac[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >>
      gvs[] >> qpat_x_assum `_ = _ ++ _` (mp_tac o SYM) >>
      simp[APPEND_EQ_CONS] >> rpt strip_tac >>
      gvs[RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
      metis_tac[]) >>
  rpt strip_tac >> gvs[lower_dload_inst_supply_def] >>
  qpat_x_assum `_ = _ ++ _` (mp_tac o SYM) >>
  simp[APPEND_EQ_CONS] >> rpt strip_tac >> gvs[]
QED

Theorem lower_dload_insts_supply_output_survives[local]:
  !s xs t. lower_dload_insts_supply s ins = (xs,t) ==>
  EVERY inst_wf ins ==>
  !i v. MEM i ins /\ MEM v i.inst_outputs ==>
  ?j. MEM j xs /\ MEM v j.inst_outputs
Proof
  Induct_on `ins`
  >- simp[lower_dload_insts_supply_def] >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >> rpt strip_tac
  >- (gvs[] >> drule_all lower_dload_inst_supply_output_survives >>
      strip_tac >> goal_assum (drule_at Any) >> simp[]) >>
  metis_tac[]
QED

Theorem lower_dload_insts_supply_output_count[local]:
  !s xs t v. lower_dload_insts_supply s ins = (xs,t) /\
  EVERY inst_wf ins /\ MEM v s.irs_used_vars ==>
  LENGTH (FILTER (\j. MEM v j.inst_outputs) xs) =
  LENGTH (FILTER (\j. MEM v j.inst_outputs) ins)
Proof
  Induct_on `ins`
  >- simp[lower_dload_insts_supply_def] >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >>
  rename1 `lower_dload_inst_supply s head = (piece,mid)` >>
  drule lower_dload_inst_supply_preserves_vars >> strip_tac >>
  drule_all lower_dload_inst_supply_output_count >> strip_tac >>
  `MEM v mid.irs_used_vars` by metis_tac[] >>
  qpat_x_assum `!s xs t v. _` (drule_all_then assume_tac) >>
  gvs[] >> pure_rewrite_tac[FILTER_APPEND_DISTRIB, LENGTH_APPEND] >>
  Cases_on `MEM v head.inst_outputs` >> gvs[]
QED

Theorem lower_dload_blocks_supply_pairing[local]:
  !s bs t. lower_dload_blocks_supply s bbs = (bs,t) ==>
  (!a. MEM a bbs ==> ?b u v.
     MEM b bs /\ lower_dload_block_supply u a = (b,v)) /\
  (!b. MEM b bs ==> ?a u v.
     MEM a bbs /\ lower_dload_block_supply u a = (b,v))
Proof
  Induct_on `bbs`
  >- simp[lower_dload_blocks_supply_def] >>
  simp[Once lower_dload_blocks_supply_def, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >> metis_tac[]
QED

Theorem lower_dload_blocks_supply_output_count[local]:
  !s bs t v. lower_dload_blocks_supply s bbs = (bs,t) /\
  EVERY (\b. EVERY inst_wf b.bb_instructions) bbs /\
  MEM v s.irs_used_vars ==>
  LENGTH (FILTER (\j. MEM v j.inst_outputs) (fn_insts_blocks bs)) =
  LENGTH (FILTER (\j. MEM v j.inst_outputs) (fn_insts_blocks bbs))
Proof
  Induct_on `bbs`
  >- simp[lower_dload_blocks_supply_def, fn_insts_blocks_def] >>
  simp[Once lower_dload_blocks_supply_def, lower_dload_block_supply_def,
       AllCaseEqs()] >> rpt gen_tac >> strip_tac >>
  rename1 `lower_dload_insts_supply s head.bb_instructions = (piece,mid)` >>
  drule lower_dload_insts_supply_reserved_operand >> strip_tac >>
  drule_all lower_dload_insts_supply_output_count >> strip_tac >>
  `MEM v mid.irs_used_vars` by metis_tac[] >>
  qpat_x_assum `!s bs t v. _` (drule_all_then assume_tac) >>
  gvs[fn_insts_blocks_def, FILTER_APPEND_DISTRIB]
QED

Theorem lower_dload_function_supply_output_count[local]:
  lower_dload_function_supply s f = (g,t) /\ fn_inst_wf f /\
  MEM v s.irs_used_vars ==>
  LENGTH (FILTER (\j. MEM v j.inst_outputs) (fn_insts g)) =
  LENGTH (FILTER (\j. MEM v j.inst_outputs) (fn_insts f))
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs()] >> strip_tac >>
  `EVERY (\b. EVERY inst_wf b.bb_instructions) f.fn_blocks` by
    (gvs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  drule_all lower_dload_blocks_supply_output_count >>
  gvs[fn_insts_def]
QED

Theorem lower_dload_insts_supply_occurrence[local]:
  !s xs t pre j post.
  lower_dload_insts_supply s ins = (xs,t) /\ xs = pre ++ j::post ==>
  ?a i b ap yp ys bp mid next.
    ins = a ++ i::b /\
    lower_dload_insts_supply s a = (ap,mid) /\
    lower_dload_inst_supply mid i = (yp ++ j::ys,next) /\
    lower_dload_insts_supply next b = (bp,t) /\
    pre = ap ++ yp /\ post = ys ++ bp
Proof
  Induct_on `ins`
  >- simp[lower_dload_insts_supply_def] >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  rename1 `lower_dload_inst_supply s head = (piece,mid_supply)` >>
  qpat_x_assum `_ ++ _ = _ ++ _` mp_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  pure_once_rewrite_tac[APPEND_EQ_APPEND] >> strip_tac
  >- (rename1 `piece = pre ++ overlap` >>
      Cases_on `overlap`
      >- (gvs[] >>
          first_x_assum (qspecl_then [`mid_supply`,`t`,`[]`,`j`,`post`]
            mp_tac) >> simp[] >> strip_tac >>
          rename1 `ins = a ++ [i] ++ b` >> qexists `head::a` >>
          simp[Once lower_dload_insts_supply_def] >>
          metis_tac[APPEND_ASSOC]) >>
      gvs[] >> qexists `[]` >> simp[lower_dload_insts_supply_def] >>
      metis_tac[]) >>
  gvs[] >> first_x_assum drule >> strip_tac >>
  rename1 `ins = a ++ [i] ++ b` >> qexists `head::a` >>
  simp[Once lower_dload_insts_supply_def] >>
  metis_tac[APPEND_ASSOC]
QED

Theorem lower_dload_source_block_distinct[local]:
  fn_inst_ids_distinct f /\ MEM b f.fn_blocks ==>
  ALL_DISTINCT b.bb_instructions
Proof
  rpt strip_tac >>
  `?pre post. f.fn_blocks = pre ++ b::post` by metis_tac[MEM_SPLIT] >>
  gvs[fn_inst_ids_distinct_def, MAP_APPEND, FLAT_APPEND,
      ALL_DISTINCT_APPEND] >>
  metis_tac[ALL_DISTINCT_MAP]
QED

Theorem lower_dload_function_supply_path[local]:
  lower_dload_function_supply s f = (g,t) ==>
  !path. is_fn_path g path = is_fn_path f path
Proof
  strip_tac >> drule lower_dload_function_supply_cfg_edge >> strip_tac >>
  Induct >> simp[is_fn_path_def] >>
  gen_tac >> rename1 `is_fn_path g (head::tail)` >> Cases_on `tail` >>
  gvs[is_fn_path_def]
QED

Theorem lower_dload_function_supply_pairing[local]:
  lower_dload_function_supply s f = (g,t) ==>
  (!a. MEM a f.fn_blocks ==> ?b u v.
     MEM b g.fn_blocks /\ lower_dload_block_supply u a = (b,v)) /\
  (!b. MEM b g.fn_blocks ==> ?a u v.
     MEM a f.fn_blocks /\ lower_dload_block_supply u a = (b,v))
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs()] >> strip_tac >>
  drule lower_dload_blocks_supply_pairing >> gvs[]
QED

Theorem lower_dload_block_supply_definition[local]:
  lower_dload_block_supply s a = (b,t) /\
  EVERY inst_wf a.bb_instructions /\
  MEM i a.bb_instructions /\ MEM v i.inst_outputs ==>
  ?j. MEM j b.bb_instructions /\ MEM v j.inst_outputs
Proof
  simp[lower_dload_block_supply_def, AllCaseEqs()] >> strip_tac >>
  drule_all lower_dload_insts_supply_output_survives >> gvs[]
QED

Theorem lower_dload_function_supply_definition[local]:
  lower_dload_function_supply s f = (g,t) /\ fn_inst_wf f /\
  MEM a f.fn_blocks /\ MEM i a.bb_instructions /\ MEM v i.inst_outputs ==>
  ?b j. MEM b g.fn_blocks /\ b.bb_label = a.bb_label /\
        MEM j b.bb_instructions /\ MEM v j.inst_outputs
Proof
  strip_tac >> drule lower_dload_function_supply_pairing >> strip_tac >>
  `?b u w. MEM b g.fn_blocks /\ lower_dload_block_supply u a = (b,w)`
    by metis_tac[] >>
  `EVERY inst_wf a.bb_instructions` by
    (gvs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  drule_all lower_dload_block_supply_definition >> strip_tac >>
  drule lower_dload_block_supply_structure >> strip_tac >> metis_tac[]
QED

Theorem lower_dload_def_on_all_paths_end[local]:
  lower_dload_function_supply s f = (g,t) /\ fn_inst_wf f /\
  MEM a f.fn_blocks /\ lower_dload_block_supply u a = (b,w) /\
  def_on_all_paths f a NONE v ==>
  def_on_all_paths g b NONE v
Proof
  strip_tac >> drule lower_dload_function_supply_path >> strip_tac >>
  drule lower_dload_function_supply_labels >> strip_tac >>
  drule lower_dload_block_supply_structure >> strip_tac >>
  `EVERY inst_wf a.bb_instructions` by
    (gvs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  gvs[def_on_all_paths_def] >> rpt strip_tac >>
  qpat_x_assum `!path. _` drule_all >> strip_tac
  >- (disj1_tac >>
      drule_all lower_dload_function_supply_definition >> strip_tac >>
      metis_tac[]) >>
  disj2_tac >>
  `?j. MEM j b.bb_instructions /\ MEM v j.inst_outputs` by
    (irule lower_dload_block_supply_definition >>
     goal_assum (drule_at Any) >> simp[MEM_EL] >> metis_tac[]) >>
  gvs[MEM_EL] >> metis_tac[]
QED

Theorem lower_dload_prefix_definition[local]:
  b.bb_instructions = pre ++ j::post /\ MEM d pre /\
  MEM v d.inst_outputs ==>
  def_on_all_paths g b (SOME j) v
Proof
  strip_tac >> qpat_x_assum `MEM d pre` mp_tac >>
  simp[MEM_EL] >> strip_tac >> gvs[] >>
  simp[def_on_all_paths_def] >> rpt strip_tac >> disj2_tac >>
  rename1 `MEM v (EL n pre).inst_outputs` >> qexists `n` >>
  simp[EL_APPEND_EQN] >> qexists `LENGTH pre` >> simp[EL_APPEND_EQN]
QED

Theorem lower_dload_source_prefix_definition[local]:
  ALL_DISTINCT ((pre ++ [i]) ++ post) /\
  n < m /\ m < LENGTH post + (LENGTH pre + 1) /\
  EL m ((pre ++ [i]) ++ post) = i /\
  MEM v (EL n ((pre ++ [i]) ++ post)).inst_outputs ==>
  ?d. MEM d pre /\ MEM v d.inst_outputs
Proof
  strip_tac >>
  `m = LENGTH pre` by
    (drule ALL_DISTINCT_EL_IMP >>
     disch_then (qspecl_then [`m`,`LENGTH pre`] mp_tac) >>
     simp[EL_APPEND_EQN]) >>
  gvs[EL_APPEND_EQN] >> qexists `EL n pre` >> simp[MEM_EL] >>
  metis_tac[]
QED

Theorem lower_dload_def_on_all_paths_use[local]:
  lower_dload_function_supply s f = (g,t) /\ fn_inst_wf f /\
  fn_inst_ids_distinct f /\ MEM a f.fn_blocks /\
  a.bb_instructions = pre ++ [i] ++ post /\
  lower_dload_insts_supply u pre = (outpre,mid) /\
  b.bb_instructions = outpre ++ localpre ++ [j] ++ suffix /\
  b.bb_label = a.bb_label /\ def_on_all_paths f a (SOME i) v ==>
  def_on_all_paths g b (SOME j) v
Proof
  strip_tac >> drule lower_dload_function_supply_path >> strip_tac >>
  drule lower_dload_function_supply_labels >> strip_tac >>
  `ALL_DISTINCT a.bb_instructions` by
    metis_tac[lower_dload_source_block_distinct] >>
  `EVERY inst_wf pre` by
    (qpat_x_assum `fn_inst_wf f` mp_tac >>
     simp[fn_inst_wf_def, EVERY_MEM] >>
     disch_then (qspec_then `a` mp_tac) >> simp[] >>
     metis_tac[]) >>
  gvs[def_on_all_paths_def] >> rpt strip_tac >>
  qpat_x_assum `!path. _` drule_all >> strip_tac
  >- (disj1_tac >> drule_all lower_dload_function_supply_definition >>
      strip_tac >> metis_tac[]) >>
  `?d. MEM d pre /\ MEM v d.inst_outputs` by
    (drule_all lower_dload_source_prefix_definition >> simp[]) >>
  `?d. MEM d outpre /\ MEM v d.inst_outputs` by
    (drule_all lower_dload_insts_supply_output_survives >> metis_tac[]) >>
  disj2_tac >>
  qpat_x_assum `MEM _ outpre` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  rename1 `d0 = EL k outpre` >>
  gvs[] >> qexists `k` >> simp[EL_APPEND_EQN] >>
  qexists `LENGTH outpre + LENGTH localpre` >> simp[EL_APPEND_EQN]
QED

Theorem lower_dload_phi_location[local]:
  lower_dload_function_supply s f = (g,t) /\ MEM b g.fn_blocks /\
  MEM i b.bb_instructions /\ i.inst_opcode = PHI ==>
  ?a. MEM a f.fn_blocks /\ a.bb_label = b.bb_label /\
      MEM i a.bb_instructions
Proof
  strip_tac >>
  drule lower_dload_function_supply_retained_location >>
  disch_then (qspecl_then [`b.bb_label`,`i`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem lower_dload_defs_reach_uses[local]:
  lower_dload_function_supply s f = (g,t) /\ fn_inst_wf f /\
  fn_inst_ids_distinct f /\ fn_defs_reach_uses f ==>
  fn_defs_reach_uses g
Proof
  strip_tac >> simp[fn_defs_reach_uses_def] >> rpt gen_tac >> strip_tac >>
  rename1 `MEM j b.bb_instructions` >>
  Cases_on `j.inst_opcode = PHI`
  >- (simp[] >> rpt strip_tac >>
      drule_all lower_dload_phi_location >> strip_tac >>
      drule lower_dload_function_supply_pairing >> strip_tac >>
      rename1 `MEM pred_bb g.fn_blocks` >>
      `?src u w. MEM src f.fn_blocks /\
         lower_dload_block_supply u src = (pred_bb,w)` by metis_tac[] >>
      drule lower_dload_block_supply_structure >> strip_tac >>
      drule lower_dload_function_supply_cfg_edge >> strip_tac >>
      `def_on_all_paths f src NONE v` by
        (gvs[fn_defs_reach_uses_def] >> metis_tac[]) >>
      drule_all lower_dload_def_on_all_paths_end >> simp[]) >>
  simp[] >> qx_gen_tac `v` >> strip_tac >>
  drule lower_dload_function_supply_pairing >> strip_tac >>
  `?a u w. MEM a f.fn_blocks /\ lower_dload_block_supply u a = (b,w)`
    by metis_tac[] >>
  `b.bb_label = a.bb_label` by metis_tac[lower_dload_block_supply_structure] >>
  `?pre post. b.bb_instructions = pre ++ j::post` by metis_tac[MEM_SPLIT] >>
  `lower_dload_insts_supply u a.bb_instructions = (b.bb_instructions,w)` by
    gvs[lower_dload_block_supply_def, AllCaseEqs()] >>
  drule_all lower_dload_insts_supply_occurrence >> strip_tac >>
  drule lower_dload_inst_supply_ordered_operand >>
  disch_then (qspecl_then [`v`,`yp`,`ys`,`j`] mp_tac) >>
  simp[] >> strip_tac
  >- (irule lower_dload_prefix_definition >>
      goal_assum (drule_at Any) >> simp[MEM_APPEND] >>
      qexistsl [`ys ++ bp`,`ap ++ yp`] >> simp[MEM_APPEND, APPEND_ASSOC]) >>
  `MEM i a.bb_instructions` by simp[] >>
  `def_on_all_paths f a (SOME i) v` by
    (qpat_x_assum `fn_defs_reach_uses f` mp_tac >>
     simp[fn_defs_reach_uses_def] >>
     disch_then (qspecl_then [`a`,`i`] mp_tac) >> simp[]) >>
  qpat_x_assum `lower_dload_insts_supply next _ = _` kall_tac >>
  qpat_x_assum `lower_dload_insts_supply u a.bb_instructions = _` kall_tac >>
  irule lower_dload_def_on_all_paths_use >>
  goal_assum (drule_at (Pat `lower_dload_function_supply _ _ = _`)) >>
  goal_assum (drule_at (Pat `def_on_all_paths _ _ _ _`)) >>
  goal_assum (drule_at (Pat `lower_dload_insts_supply u _ = (ap,mid)`)) >>
  simp[] >> qexistsl [`yp`,`ys ++ bp`] >> simp[APPEND_ASSOC]
QED

Theorem lower_dload_all_reachable[local]:
  lower_dload_function_supply s f = (g,t) /\ all_reachable f ==>
  all_reachable g
Proof
  strip_tac >> drule lower_dload_function_supply_reachable >> strip_tac >>
  drule lower_dload_function_supply_labels >> strip_tac >>
  gvs[all_reachable_def, fn_labels_def] >> rpt strip_tac >>
  `MEM bb.bb_label (MAP (\x. x.bb_label) f.fn_blocks)` by
    (qpat_x_assum `MAP _ g.fn_blocks = _` (rewrite_tac o single o GSYM) >>
     simp[MEM_MAP] >> metis_tac[]) >>
  gvs[MEM_MAP] >> metis_tac[]
QED

Theorem lower_dload_phis_cover_preds[local]:
  lower_dload_function_supply s f = (g,t) /\ fn_phis_cover_preds f ==>
  fn_phis_cover_preds g
Proof
  strip_tac >> drule lower_dload_function_supply_cfg_edge >> strip_tac >>
  simp[fn_phis_cover_preds_def] >> rpt strip_tac >>
  drule_all lower_dload_phi_location >> strip_tac >>
  gvs[fn_phis_cover_preds_def] >> metis_tac[]
QED

Theorem lower_dload_phis_non_degenerate[local]:
  lower_dload_function_supply s f = (g,t) /\ fn_phis_non_degenerate f ==>
  fn_phis_non_degenerate g
Proof
  strip_tac >> simp[fn_phis_non_degenerate_def] >> rpt strip_tac >>
  drule lower_dload_function_supply_retained_member >>
  rename1 `i.inst_opcode = PHI` >>
  disch_then (qspec_then `i` mp_tac) >>
  simp[] >> strip_tac >> gvs[fn_phis_non_degenerate_def] >> metis_tac[]
QED

Theorem lower_dload_source_var_reserved[local]:
  ir_supply_covers_fn s f /\ MEM b f.fn_blocks /\
  MEM i b.bb_instructions /\ MEM v (inst_ir_vars i) ==>
  MEM v s.irs_used_vars
Proof
  simp[ir_supply_covers_fn_def, list_subset_def, fn_ir_vars_def,
       block_ir_vars_def, MEM_FLAT, MEM_MAP, PULL_EXISTS, EVERY_MEM] >>
  metis_tac[]
QED

Theorem lower_dload_phi_operands_single_def[local]:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  fn_inst_wf f /\ fn_phi_operands_single_def f ==>
  fn_phi_operands_single_def g
Proof
  strip_tac >> simp[fn_phi_operands_single_def_def] >> rpt strip_tac >>
  drule_all lower_dload_phi_location >> strip_tac >>
  rename1 `MEM (pred,v) (phi_pairs i.inst_operands)` >>
  `MEM v (inst_ir_vars i)` by
    (simp[inst_ir_vars_def, inst_uses_def] >>
     drule MEM_phi_pairs_SND_operand_vars >> simp[]) >>
  `MEM v s.irs_used_vars` by metis_tac[lower_dload_source_var_reserved] >>
  drule_all lower_dload_function_supply_output_count >> strip_tac >>
  gvs[fn_phi_operands_single_def_def] >> metis_tac[]
QED

Theorem lower_dload_phi_outputs_single_def[local]:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  fn_inst_wf f /\ fn_phi_outputs_single_def f ==>
  fn_phi_outputs_single_def g
Proof
  strip_tac >> simp[fn_phi_outputs_single_def_def] >> rpt strip_tac >>
  drule_all lower_dload_phi_location >> strip_tac >>
  rename1 `MEM v i.inst_outputs` >>
  `MEM v (inst_ir_vars i)` by simp[inst_ir_vars_def] >>
  `MEM v s.irs_used_vars` by metis_tac[lower_dload_source_var_reserved] >>
  drule_all lower_dload_function_supply_output_count >> strip_tac >>
  gvs[fn_phi_outputs_single_def_def] >> metis_tac[]
QED

Theorem lower_dload_phi_edges[local]:
  lower_dload_function_supply s f = (g,t) /\
  (!bb i. MEM bb f.fn_blocks /\ MEM i bb.bb_instructions /\
    i.inst_opcode = PHI ==>
    ALL_DISTINCT (MAP FST (phi_pairs i.inst_operands)) /\
    !l v. MEM (l,v) (phi_pairs i.inst_operands) ==>
      fn_cfg_edge f l bb.bb_label) ==>
  (!bb i. MEM bb g.fn_blocks /\ MEM i bb.bb_instructions /\
    i.inst_opcode = PHI ==>
    ALL_DISTINCT (MAP FST (phi_pairs i.inst_operands)) /\
    !l v. MEM (l,v) (phi_pairs i.inst_operands) ==>
      fn_cfg_edge g l bb.bb_label)
Proof
  strip_tac >> drule lower_dload_function_supply_cfg_edge >> strip_tac >>
  rpt strip_tac >> drule_all lower_dload_phi_location >> strip_tac >>
  metis_tac[]
QED

(* Intuition, per conjunct of make_ssa_input_ok:
   - all_reachable and the PHI rows: the CFG (labels, edges, entry) is the
     same, and PHIs are kept unchanged in their same-labelled block
     (lower_dload_function_supply_cfg_edge, _labels, _retained_location).
   - the single-definition rows: fn_pass_step's ir_supply_covers_unit
     covers the observed unit, which contains fn (lookup_unique_function),
     so the supply's fresh variables avoid every variable of fn and no
     variable of fn gets a second definition.
   - fn_defs_reach_uses: a Var operand of an expanded instruction is a
     fresh variable defined earlier in the same expansion, or an operand of
     the original (non-PHI) instruction.  The original's definition before
     its occurrence (or in an earlier block of the path) is still there,
     before the expansion.  fn_inst_ids_distinct makes the occurrence
     unique, which matters because def_on_all_paths asks for a definition
     before SOME occurrence of the use.  fn_inst_wf keeps DLOADBYTES
     output-free (the expansion drops a DLOADBYTES's outputs) and gives
     DLOAD its one operand and output. *)
Theorem lower_dload_fn_pass_step_make_ssa_input_ok:
  fn_pass_step rpolicy (CFP_Simple VP_LowerDload) observed s fn out /\
  fn_inst_ids_distinct fn /\ fn_inst_wf fn /\ make_ssa_input_ok fn ==>
  make_ssa_input_ok out.fpo_function
Proof
  strip_tac >> drule lower_dload_step_supply >> strip_tac >>
  gvs[make_ssa_input_ok_def] >> rpt conj_tac
  >- metis_tac[lower_dload_all_reachable]
  >- metis_tac[lower_dload_defs_reach_uses]
  >- metis_tac[lower_dload_phi_operands_single_def]
  >- metis_tac[lower_dload_phis_cover_preds]
  >- metis_tac[lower_dload_phi_outputs_single_def]
  >- metis_tac[lower_dload_phis_non_degenerate] >>
  match_mp_tac (GEN_ALL lower_dload_phi_edges) >>
  goal_assum (drule_at Any) >> first_assum ACCEPT_TAC
QED
