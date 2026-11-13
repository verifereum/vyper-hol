Theory o1LabelFlowSimplifyPreservation
Ancestors
  o1LabelFlowLateSimplify o1LabelFlowRetention simplifyCfgWfssa
  allocaRemapSSA venomInst list simplifyCfgStruct simplifyCfgDataflow
  venomWf codegenSymRel unitShapeDefs symFrameBoundary
  simplifyCfgFixupShape simplifyCfgDefs simplifyCfgInvariant
  o1LabelFlowSimplifyChain o1LabelFlowSimplifyJump
  o1LabelFlowSimplifySubstitution

Theorem simplify_unreachable_inst_subset:
  wf_function f /\ MEM i (fn_insts (remove_unreachable_blocks f)) ==>
  MEM i (fn_insts f)
Proof
  simp[fn_insts_def, MEM_fn_insts_blocks_iff] >>
  metis_tac[remove_unreachable_blocks_member]
QED

(* Only ordinary readers need this closure: PHIs cannot read tainted values. *)
Theorem simplify_unreachable_reader_definition:
  wf_ssa f /\ wf_function f /\
  MEM i (fn_insts (remove_unreachable_blocks f)) /\
  i.inst_opcode <> PHI /\ MEM (Var x) i.inst_operands /\
  MEM d (fn_insts f) /\ MEM x d.inst_outputs ==>
  MEM d (fn_insts (remove_unreachable_blocks f))
Proof
  strip_tac >>
  `?bb. MEM bb (remove_unreachable_blocks f).fn_blocks /\
        MEM i bb.bb_instructions` by
    metis_tac[fn_insts_def, MEM_fn_insts_blocks_iff] >>
  `MEM bb f.fn_blocks` by metis_tac[remove_unreachable_blocks_member] >>
  `def_available_at f bb (SOME i) x` by
    (gvs[wf_ssa_def, def_dominates_uses_def] >> metis_tac[]) >>
  `def_available_at (remove_unreachable_blocks f) bb (SOME i) x` by
    metis_tac[remove_unreachable_blocks_def_available_at] >>
  pop_assum mp_tac >> simp[def_available_at_def] >>
  disch_then (qx_choose_then `db` (qx_choose_then `di` strip_assume_tac)) >>
  `MEM di (fn_insts (remove_unreachable_blocks f))` by
    (simp[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  `MEM di (fn_insts f)` by metis_tac[simplify_unreachable_inst_subset] >>
  `di = d` by metis_tac[wf_ssa_def, ssa_unique_output] >> gvs[]
QED

Theorem simplify_unreachable_code_end_reader:
  !f x. code_end_var f x ==>
  !ctx i. wf_ssa f /\ wf_function f /\
    label_flow_ok (ctx with ctx_functions := [f]) /\
    MEM i (fn_insts (remove_unreachable_blocks f)) /\
    MEM (Var x) i.inst_operands ==>
    code_end_var (remove_unreachable_blocks f) x
Proof
  Induct_on `code_end_var` >> rpt strip_tac >>
  `i.inst_opcode <> PHI` by
    (strip_tac >>
     `MEM f (ctx with ctx_functions := [f]).ctx_functions` by simp[] >>
     metis_tac[phi_input_not_code_end, simplify_unreachable_inst_subset,
               code_end_var_rules]) >>
  `MEM inst (fn_insts (remove_unreachable_blocks f))` by
    metis_tac[simplify_unreachable_reader_definition] >>
  metis_tac[code_end_var_rules, MEM]
QED

Theorem simplify_unreachable_label_flow:
  wf_ssa f /\ wf_function f /\
  label_flow_ok (ctx with ctx_functions := [f]) ==>
  label_flow_ok (ctx with ctx_functions := [remove_unreachable_blocks f])
Proof
  strip_tac >> simp[label_flow_ok_def] >> gen_tac >> strip_tac >>
  `MEM inst (fn_insts f)` by metis_tac[simplify_unreachable_inst_subset] >>
  qpat_assum `label_flow_ok _` mp_tac >> simp[NoAsms, label_flow_ok_def] >>
  disch_then (qspec_then `inst` mp_tac) >> simp[] >> strip_tac >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      `code_end_var f x` by
        metis_tac[code_end_var_instruction_subset,
                  simplify_unreachable_inst_subset] >> metis_tac[]) >>
  strip_tac >> gvs[] >>
  metis_tac[simplify_unreachable_code_end_reader, MEM]
QED

Theorem simplify_fix_phis_non_phi_member:
  MEM i (fn_insts f) /\ i.inst_opcode <> PHI ==>
  MEM i (fn_insts (fix_all_phis f))
Proof
  simp[fn_insts_def, MEM_fn_insts_blocks_iff, fix_all_phis_def, MEM_MAP] >>
  strip_tac >> qexists_tac `fix_phis_in_block (pred_labels f bb.bb_label) bb` >>
  simp[fix_phis_in_block_def, MEM_FILTER, MEM_MAP] >>
  metis_tac[fix_phi_inst_non_phi]
QED

Theorem simplify_fix_phis_code_end_forward:
  !f x. code_end_var f x ==> code_end_var (fix_all_phis f) x
Proof
  Induct_on `code_end_var` >> rpt strip_tac >>
  `MEM inst (fn_insts (fix_all_phis f))` by
    (irule simplify_fix_phis_non_phi_member >> simp[]) >>
  metis_tac[code_end_var_rules]
QED

Theorem simplify_fix_phis_code_end_backward:
  !g x. code_end_var g x ==>
  !f ctx. g = fix_all_phis f /\
    label_flow_ok (ctx with ctx_functions := [f]) ==> code_end_var f x
Proof
  Induct_on `code_end_var` >> rpt strip_tac >> gvs[] >>
  drule scfg_fix_all_phis_inst_mem >> strip_tac
  >- (`fix_phi_inst actual_preds inst' = inst'` by
        (irule scfg_fix_phi_seed_identity >> gvs[]) >>
      gvs[] >> metis_tac[code_end_var_rules]) >>
  rename1 `inst.inst_operands = [Var y]` >>
  `code_end_var f y` by metis_tac[] >>
  `MEM f (ctx with ctx_functions := [f]).ctx_functions` by simp[] >>
  `MEM (Var y) (fix_phi_inst actual_preds inst').inst_operands` by metis_tac[MEM] >>
  `fix_phi_inst actual_preds inst' = inst'` by
    metis_tac[fix_phi_inst_changed_no_code_end] >>
  gvs[] >> metis_tac[code_end_var_rules]
QED

Theorem simplify_fix_phis_label_flow:
  label_flow_ok (ctx with ctx_functions := [f]) ==>
  label_flow_ok (ctx with ctx_functions := [fix_all_phis f])
Proof
  strip_tac >> simp[label_flow_ok_def] >> gen_tac >> strip_tac >>
  drule scfg_fix_all_phis_inst_mem >> strip_tac >> gvs[] >>
  rename1 `MEM old (fn_insts f)` >>
  `MEM f (ctx with ctx_functions := [f]).ctx_functions` by simp[] >>
  conj_tac
  >- (`(fix_phi_inst actual_preds old).inst_opcode = CODESIZE ==>
        fix_phi_inst actual_preds old = old` by
        (strip_tac >> irule scfg_fix_phi_seed_identity >> simp[]) >>
      metis_tac[label_flow_ok_def]) >>
  conj_tac
  >- (rpt strip_tac >>
      `code_end_var f x` by metis_tac[simplify_fix_phis_code_end_backward] >>
      metis_tac[fix_phi_inst_code_end_use]) >>
  strip_tac >>
  `fix_phi_inst actual_preds old = old` by
    (irule scfg_fix_phi_seed_identity >> simp[]) >>
  gvs[] >>
  qpat_assum `label_flow_ok _` mp_tac >> simp[NoAsms, label_flow_ok_def] >>
  disch_then (qspec_then `old` mp_tac) >> simp[] >>
  metis_tac[simplify_fix_phis_code_end_forward]
QED

Theorem simplify_collapse_label_flow_invariant:
  !f lm vis lbl.
  wf_ssa f /\ wf_function f /\ fn_inst_wf f /\ first_block_no_preds f /\
  scfg_phi_safe f /\ fn_defs_reach_uses f /\
  EVERY label_positions_ok (fn_insts f) /\ all_reachable f /\
  label_flow_ok (ctx with ctx_functions := [f]) ==>
  wf_ssa (FST (collapse_dfs f lm vis lbl)) /\
  wf_function (FST (collapse_dfs f lm vis lbl)) /\
  fn_inst_wf (FST (collapse_dfs f lm vis lbl)) /\
  first_block_no_preds (FST (collapse_dfs f lm vis lbl)) /\
  scfg_phi_safe (FST (collapse_dfs f lm vis lbl)) /\
  fn_defs_reach_uses (FST (collapse_dfs f lm vis lbl)) /\
  EVERY label_positions_ok (fn_insts (FST (collapse_dfs f lm vis lbl))) /\
  all_reachable (FST (collapse_dfs f lm vis lbl)) /\
  label_flow_ok (ctx with ctx_functions := [FST (collapse_dfs f lm vis lbl)])
Proof
  ho_match_mp_tac collapse_dfs_preserves_predicate >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_all do_merge_jump_ssa_invariant >> strip_tac >> simp[] >>
      irule simplify_do_merge_jump_label_flow >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `a.bb_label = lbl /\ b.bb_label = next /\
   MEM a f.fn_blocks /\ MEM b f.fn_blocks` by
    metis_tac[lookup_block_member_label] >>
  rpt conj_tac >>
  metis_tac[chain_merge_ssa_invariant, simplify_chain_merge_label_flow]
QED

Theorem simplify_cfg_round_label_flow:
  wf_ssa f /\ wf_function f /\ fn_inst_wf f /\ first_block_no_preds f /\
  scfg_phi_safe f /\ fn_defs_reach_uses f /\
  EVERY label_positions_ok (fn_insts f) /\
  label_flow_ok (ctx with ctx_functions := [f]) ==>
  label_flow_ok (ctx with ctx_functions := [FST (simplify_cfg_round_with_labels f)])
Proof
  strip_tac >> Cases_on `fn_entry_label f`
  >- simp[simplify_cfg_round_with_labels_def] >>
  drule_all simplify_cfg_round_entry_ssa_invariant >> strip_tac >>
  `label_flow_ok (ctx with ctx_functions :=
     [fix_all_phis (remove_unreachable_blocks f)])` by
    (irule simplify_fix_phis_label_flow >>
     irule simplify_unreachable_label_flow >> simp[]) >>
  qabbrev_tac `start = fix_all_phis (remove_unreachable_blocks f)` >>
  Cases_on `collapse_dfs start [] [] x` >> PairCases_on `r` >>
  qspecl_then [`start`, `[]`, `[]`, `x`] mp_tac
    simplify_collapse_label_flow_invariant >> simp[] >> strip_tac >>
  `subst_block_labels_fn r0 q = q` by
    (drule_at (Pat `collapse_dfs _ _ _ _ = _`) collapse_dfs_subst_identity >> simp[]) >>
  `label_flow_ok (ctx with ctx_functions :=
     [fix_all_phis (remove_unreachable_blocks q)])` by
    (irule simplify_fix_phis_label_flow >>
     irule simplify_unreachable_label_flow >> simp[]) >>
  fs[Abbr `start`] >> simp[simplify_cfg_round_with_labels_def]
QED

Theorem simplify_cfg_iter_label_flow:
  !fuel f.
  wf_ssa f /\ wf_function f /\ fn_inst_wf f /\ first_block_no_preds f /\
  scfg_phi_safe f /\ fn_defs_reach_uses f /\
  EVERY label_positions_ok (fn_insts f) /\
  label_flow_ok (ctx with ctx_functions := [f]) ==>
  label_flow_ok (ctx with ctx_functions :=
    [FST (simplify_cfg_iter_with_labels fuel f)])
Proof
  Induct_on `fuel` >- simp[simplify_cfg_iter_with_labels_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all simplify_cfg_round_ssa_invariant >> strip_tac >>
  drule_all simplify_cfg_round_label_flow >> strip_tac >>
  Cases_on `simplify_cfg_round_with_labels f` >> gvs[] >>
  simp[simplify_cfg_iter_with_labels_def] >> IF_CASES_TAC >> simp[] >>
  Cases_on `simplify_cfg_iter_with_labels fuel q` >> simp[] >>
  first_x_assum (qspec_then `q` mp_tac) >> simp[]
QED

Theorem simplify_cfg_fn_label_flow:
  wf_ssa f /\ wf_function f /\ fn_inst_wf f /\ first_block_no_preds f /\
  scfg_phi_safe f /\ fn_defs_reach_uses f /\
  EVERY label_positions_ok (fn_insts f) /\
  label_flow_ok (ctx with ctx_functions := [f]) ==>
  label_flow_ok (ctx with ctx_functions := [FST (simplify_cfg_fn_with_labels f)])
Proof
  simp[simplify_cfg_fn_with_labels_def] >>
  metis_tac[simplify_cfg_iter_label_flow]
QED
