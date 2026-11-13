(* Feasible incoming edges avoid collisions in chain PHI relabeling. *)
Theory simplifyCfgMergeEntry
Ancestors
  simplifyCfgMergeExec simplifyCfgMergeClosure simplifyCfgMergePaths
  simplifyCfgControl simplifyCfgControlExec simplifyCfgControlState
  simplifyCfgPhiSemantics simplifyCfgStaticInterface
  simplifyCfgDefs venomExecSemantics venomState venomWf venomInst
  cfgTransform cfgHelpers contextCodegenRel instIdxIndep list rich_list

Theorem scfg_resolve_phi_subst:
  !ops. phi_well_formed ops /\ ~MEM (Label a) ops /\ p <> a ==>
  resolve_phi (if p = b then a else p) (MAP (subst_label_op b a) ops) =
  resolve_phi p ops
Proof
  recInduct phi_well_formed_ind >>
  simp[phi_well_formed_def, resolve_phi_def, subst_label_op_def] >>
  rpt strip_tac >> rpt IF_CASES_TAC >> gvs[resolve_phi_def]
QED

Theorem scfg_chain_phi_excludes_a:
  scfg_chain_hyp fn a b /\ MEM bb fn.fn_blocks /\ bb.bb_label <> b.bb_label /\
  MEM i bb.bb_instructions /\ i.inst_opcode = PHI ==>
  ~MEM (Label a.bb_label) i.inst_operands
Proof
  strip_tac >> strip_tac >>
  `MEM a.bb_label (pred_labels fn bb.bb_label)` by
    metis_tac[scfg_chain_hyp_def, scfg_normalized_phi_support] >>
  `fn_cfg_edge fn a.bb_label bb.bb_label` by
    (fs[pred_labels_def, block_preds_def, MEM_MAP, MEM_FILTER, fn_cfg_edge_def] >>
     metis_tac[]) >>
  metis_tac[simplifyCfgMergeAvailabilityTheory.scfg_chain_old_pred_not_a]
QED

Theorem scfg_chain_resolve_phi:
  scfg_chain_hyp fn a b /\ MEM bb fn.fn_blocks /\ bb.bb_label <> b.bb_label /\
  MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\
  fn_cfg_edge fn p bb.bb_label ==>
  resolve_phi (if p = b.bb_label then a.bb_label else p)
    (scfg_phi_image a b bb.bb_label i).inst_operands = resolve_phi p i.inst_operands
Proof
  strip_tac >>
  `p <> a.bb_label` by
    metis_tac[simplifyCfgMergeAvailabilityTheory.scfg_chain_old_pred_not_a] >>
  `phi_well_formed i.inst_operands` by
    ( `fn_inst_wf fn` by metis_tac[scfg_chain_hyp_def, scfg_normalized_static,
        scfg_static_inst_wf] >>
      fs[fn_inst_wf_def, EVERY_MEM] >>
      `inst_wf i` by metis_tac[] >> gvs[inst_wf_def]) >>
  `~MEM (Label a.bb_label) i.inst_operands` by
    metis_tac[scfg_chain_phi_excludes_a] >>
  simp[scfg_phi_image_def] >> Cases_on `MEM bb.bb_label (bb_succs b)`
  >- (simp[subst_label_inst_def] >> irule scfg_resolve_phi_subst >> simp[]) >>
  `p <> b.bb_label` by
    (strip_tac >>
     qpat_x_assum `fn_cfg_edge _ _ _`
       (qx_choose_then `pb` strip_assume_tac o REWRITE_RULE [fn_cfg_edge_def]) >>
     `pb = b` by metis_tac[scfg_chain_hyp_def, scfg_chain_old_wf,
       wf_function_def, venomExecProofsTheory.same_label_same_block,
       lookup_block_member_label] >> gvs[]) >>
  simp[]
QED

Theorem scfg_chain_eval_one_phi:
  scfg_chain_hyp fn a b /\ MEM bb fn.fn_blocks /\ bb.bb_label <> b.bb_label /\
  MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\
  fn_cfg_edge fn p bb.bb_label /\ s.vs_prev_bb = SOME p ==>
  eval_one_phi (scfg_ctrl c (SOME (if p = b.bb_label then a.bb_label else p)) n s)
    (scfg_phi_image a b bb.bb_label i) = eval_one_phi s i
Proof
  strip_tac >> drule_all scfg_chain_resolve_phi >> strip_tac >>
  simp[eval_one_phi_def, scfg_ctrl_def] >>
  namedCases_on `i.inst_outputs` ["", "out outs"] >> simp[] >>
  Cases_on `outs` >> simp[] >>
  Cases_on `resolve_phi p i.inst_operands` >> simp[] >>
  metis_tac[scfg_ctrl_operand, scfg_ctrl_def]
QED

Theorem scfg_eval_phis_map:
  !xs. (!i. MEM i xs ==> ((f i).inst_opcode = PHI <=> i.inst_opcode = PHI)) /\
  (!i. MEM i xs /\ i.inst_opcode = PHI ==>
    eval_one_phi (scfg_ctrl c p n s) (f i) = eval_one_phi s i) ==>
  eval_phis (scfg_ctrl c p n s) (MAP f xs) =
    exec_result_map (scfg_ctrl c p n) (eval_phis s xs)
Proof
  Induct >- simp[eval_phis_def, exec_result_map_def] >>
  pure_rewrite_tac[MEM, MAP] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[eval_phis_def, exec_result_map_def] >>
  `eval_one_phi (scfg_ctrl c p n s) (f h) = eval_one_phi s h` by metis_tac[] >>
  simp[] >> Cases_on `eval_one_phi s h` >> simp[exec_result_map_def] >>
  PairCases_on `x` >> simp[] >>
  `eval_phis (scfg_ctrl c p n s) (MAP f xs) =
   exec_result_map (scfg_ctrl c p n) (eval_phis s xs)` by metis_tac[] >>
  simp[] >> Cases_on `eval_phis s xs` >>
  simp[exec_result_map_def, simplifyCfgControlStateTheory.scfg_ctrl_update_var]
QED

Theorem scfg_chain_eval_phis_image:
  scfg_chain_hyp fn a b /\ MEM bb fn.fn_blocks /\ bb.bb_label <> b.bb_label /\
  fn_cfg_edge fn p bb.bb_label /\ s.vs_prev_bb = SOME p ==>
  eval_phis (scfg_ctrl c (SOME (if p = b.bb_label then a.bb_label else p)) n s)
    (MAP (scfg_phi_image a b bb.bb_label) bb.bb_instructions) =
  exec_result_map (scfg_ctrl c (SOME (if p = b.bb_label then a.bb_label else p)) n)
    (eval_phis s bb.bb_instructions)
Proof
  strip_tac >> irule scfg_eval_phis_map >> simp[] >>
  rpt strip_tac >> irule scfg_chain_eval_one_phi >> metis_tac[]
QED


Theorem scfg_phi_splice:
  !xs. xs <> [] /\ (LAST xs).inst_opcode <> PHI /\
  EVERY (\i. i.inst_opcode <> PHI) ys ==>
  phi_prefix_length (FRONT xs ++ ys) = phi_prefix_length xs /\
  eval_phis s (FRONT xs ++ ys) = eval_phis s xs
Proof
  Induct >> simp[] >> gen_tac >> Cases_on `xs = []`
  >- (simp[] >> rpt strip_tac >>
      simp[eval_phis_def, phi_prefix_length_def,
        venomExecProofsTheory.eval_phis_no_phis,
        venomExecProofsTheory.no_phis_phi_prefix_length_zero]) >>
  Cases_on `xs` >> gvs[] >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  simp[phi_prefix_length_def, eval_phis_def]
QED

Theorem scfg_chain_phi_splice:
  scfg_chain_hyp fn a b /\ MEM bb fn.fn_blocks ==>
  phi_prefix_length (scfg_chain_block a b bb).bb_instructions =
    phi_prefix_length bb.bb_instructions /\
  eval_phis s (scfg_chain_block a b bb).bb_instructions =
    eval_phis s (MAP (scfg_phi_image a b bb.bb_label) bb.bb_instructions)
Proof
  strip_tac >> simp[scfg_chain_block_def] >>
  Cases_on `bb.bb_label = a.bb_label`
  >- (`bb = a` by metis_tac[scfg_chain_hyp_def, scfg_chain_old_wf,
        wf_function_def, venomExecProofsTheory.same_label_same_block,
        lookup_block_member_label] >> gvs[] >>
      `a.bb_instructions <> []` by metis_tac[scfg_chain_blocks_nonempty] >>
      `(LAST a.bb_instructions).inst_opcode <> PHI` by
        (drule scfg_chain_transfer_shape >> strip_tac >> simp[]) >>
      `EVERY (\i. i.inst_opcode <> PHI) b.bb_instructions` by
        metis_tac[scfg_chain_no_phis, no_phis_def] >>
      qspecl_then [`MAP (scfg_phi_image a b a.bb_label) a.bb_instructions`]
        mp_tac (Q.INST [`ys` |->
          `MAP (scfg_phi_image a b a.bb_label) b.bb_instructions`] scfg_phi_splice) >>
      simp[MAP_FRONT, MAP_APPEND, LAST_MAP, EVERY_MAP] >>
      metis_tac[venomExecProofsTheory.phi_prefix_length_map_congruent,
        scfg_phi_image_opcode]) >>
  simp[] >> irule venomExecProofsTheory.phi_prefix_length_map_congruent >> simp[]
QED

Theorem scfg_chain_eval_phis_edge:
  scfg_chain_hyp fn a b /\ MEM bb fn.fn_blocks /\ bb.bb_label <> b.bb_label /\
  fn_cfg_edge fn p bb.bb_label /\ s.vs_prev_bb = SOME p ==>
  eval_phis (scfg_ctrl c (SOME (if p = b.bb_label then a.bb_label else p)) n s)
    (scfg_chain_block a b bb).bb_instructions =
  exec_result_map (scfg_ctrl c (SOME (if p = b.bb_label then a.bb_label else p)) n)
    (eval_phis s bb.bb_instructions)
Proof
  strip_tac >> drule_all scfg_chain_phi_splice >> strip_tac >>
  simp[] >> irule scfg_chain_eval_phis_image >> metis_tac[]
QED

Theorem scfg_chain_entry_no_phis:
  scfg_chain_hyp fn a b /\ lookup_block l fn.fn_blocks = SOME bb /\
  fn_entry_label fn = SOME l ==>
  EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions
Proof
  strip_tac >>
  `simplify_cfg_fn_ok fn` by
    metis_tac[scfg_chain_hyp_def, scfg_normalized_static, scfg_static_ok] >>
  `wf_function fn` by metis_tac[scfg_chain_old_wf] >>
  Cases_on `fn.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def] >>
  `bb = h` by
    metis_tac[lookup_block_member_label, venomExecProofsTheory.same_label_same_block,
      wf_function_def, MEM] >>
  gvs[simplify_cfg_fn_ok_def]
QED

Theorem scfg_chain_eval_phis_entry:
  scfg_chain_hyp fn a b /\ lookup_block l fn.fn_blocks = SOME bb /\
  fn_entry_label fn = SOME l ==>
  eval_phis (scfg_ctrl c p n s) (scfg_chain_block a b bb).bb_instructions =
    exec_result_map (scfg_ctrl c p n) (eval_phis s bb.bb_instructions)
Proof
  strip_tac >> drule_all scfg_chain_entry_no_phis >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_member_label] >>
  drule_all scfg_chain_phi_splice >> strip_tac >> simp[] >>
  `EVERY (\i. i.inst_opcode <> PHI)
    (MAP (scfg_phi_image a b bb.bb_label) bb.bb_instructions)` by
    simp[EVERY_MAP] >>
  simp[venomExecProofsTheory.eval_phis_no_phis, exec_result_map_def]
QED

(* A missing predecessor is admitted only at the function's real entry. *)
Theorem scfg_chain_eval_phis:
  scfg_chain_hyp fn a b /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_current_bb <> b.bb_label /\
  (case s.vs_prev_bb of NONE => fn_entry_label fn = SOME s.vs_current_bb
    | SOME p => fn_cfg_edge fn p s.vs_current_bb) ==>
  eval_phis (scfg_ctrl s.vs_current_bb
    (OPTION_MAP (\p. if p = b.bb_label then a.bb_label else p) s.vs_prev_bb) n s)
    (scfg_chain_block a b bb).bb_instructions =
  exec_result_map (scfg_ctrl s.vs_current_bb
    (OPTION_MAP (\p. if p = b.bb_label then a.bb_label else p) s.vs_prev_bb) n)
    (eval_phis s bb.bb_instructions)
Proof
  strip_tac >> Cases_on `s.vs_prev_bb` >> gvs[]
  >- (irule scfg_chain_eval_phis_entry >> metis_tac[]) >>
  irule scfg_chain_eval_phis_edge >>
  metis_tac[lookup_block_member_label]
QED

Theorem scfg_chain_enters_block:
  scfg_chain_hyp fn a b /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_current_bb <> b.bb_label /\
  (case s.vs_prev_bb of NONE => fn_entry_label fn = SOME s.vs_current_bb
    | SOME p => fn_cfg_edge fn p s.vs_current_bb) ==>
  (enters_block (scfg_chain fn a b)
    (scfg_ctrl s.vs_current_bb
      (OPTION_MAP (\p. if p = b.bb_label then a.bb_label else p) s.vs_prev_bb) 0 s) t1 <=>
   ?s1. enters_block fn s s1 /\
    t1 = scfg_ctrl s.vs_current_bb
      (OPTION_MAP (\p. if p = b.bb_label then a.bb_label else p) s.vs_prev_bb)
      s1.vs_inst_idx s1)
Proof
  strip_tac >> drule_all scfg_chain_eval_phis >>
  disch_then (qspec_then `0` assume_tac) >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_member_label] >>
  drule_all scfg_chain_phi_splice >> strip_tac >>
  fs[scfg_ctrl_def] >>
  simp[enters_block_def, scfg_chain_lookup_eq] >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  gvs[exec_result_map_def, scfg_ctrl_def]
QED
