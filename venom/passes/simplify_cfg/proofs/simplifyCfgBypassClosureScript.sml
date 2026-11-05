(* Static closure for the guarded bypass performed by try_bypass. *)
Theory simplifyCfgBypassClosure
Ancestors
  simplifyCfgShapeCore
  simplifyCfgBypassPaths simplifyCfgBypassStatic simplifyCfgMergePaths
  simplifyCfgStaticInterface simplifyCfgBypassPhi simplifyCfgMergeAvailability
  simplifyCfgDefs venomWf venomInst unitShapeDefs cfgTransform venomExecProofs
  venomExecProps list rich_list cfgTransformInstWf simplifyCfgShape
  simplifyCfgStruct

Definition scfg_bypass_hyp_def:
  scfg_bypass_hyp fn a b fn' <=>
    scfg_normalized fn /\
    lookup_block a.bb_label fn.fn_blocks = SOME a /\
    lookup_block b.bb_label fn.fn_blocks = SOME b /\
    can_bypass_jump fn a b /\
    ?target t lm lm'. bb_succs b = [target] /\
      lookup_block target fn.fn_blocks = SOME t /\
      phi_values_agree a.bb_label b.bb_label t.bb_instructions /\
      do_merge_jump fn a b lm = SOME (fn', lm')
End

Theorem scfg_bypass_old_static:
  scfg_bypass_hyp fn a b fn' ==> scfg_static fn
Proof
  simp[scfg_bypass_hyp_def] >> metis_tac[scfg_normalized_static]
QED

(* The premises of the base's do_merge_jump closure lemmas. *)
Theorem scfg_bypass_base_hyp:
  scfg_bypass_hyp fn a b fn' ==>
  wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\
  scfg_phi_safe fn /\ fn_defs_reach_uses fn /\ scfg_phi_preds fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  ?lm lm'. do_merge_jump fn a b lm = SOME (fn',lm')
Proof
  strip_tac >>
  `scfg_static fn` by metis_tac[scfg_bypass_old_static] >>
  fs[scfg_static_def, simplifyCfgPhiRepairTheory.simplify_cfg_fn_ok_phi_safe] >>
  fs[scfg_bypass_hyp_def] >> reverse conj_tac >- metis_tac[] >>
  simp[simplifyCfgPhiPredsTheory.scfg_phi_preds_def] >> rpt strip_tac >>
  drule scfg_phi_pair_label >> strip_tac >>
  `MEM p (pred_labels fn bb.bb_label)` by metis_tac[scfg_normalized_phi_support] >>
  fs[pred_labels_def, block_preds_def, MEM_MAP, MEM_FILTER, fn_cfg_edge_def] >>
  metis_tac[]
QED

Theorem scfg_bypass_entry_eq:
  scfg_bypass_hyp fn a b fn' ==> fn_entry_label fn' = fn_entry_label fn
Proof
  strip_tac >> `first_block_no_preds fn` by
    metis_tac[scfg_bypass_old_static, scfg_static_first_no_preds] >>
  fs[scfg_bypass_hyp_def] >> irule scfg_bypass_entry >>
  metis_tac[scfg_bypass_not_entry]
QED

Theorem scfg_bypass_edge_eq:
  scfg_bypass_hyp fn a b fn' ==>
  ?target. bb_succs b = [target] /\ target <> b.bb_label /\
    (!x y. venomWf$fn_cfg_edge fn' x y <=>
      x <> b.bb_label /\ y <> b.bb_label /\
      (venomWf$fn_cfg_edge fn x y \/ x = a.bb_label /\ y = target))
Proof
  strip_tac >>
  `wf_function fn /\ scfg_shape fn` by
    metis_tac[scfg_bypass_old_static, scfg_static_wf, scfg_static_shape] >>
  `ALL_DISTINCT (fn_labels fn)` by fs[wf_function_def] >>
  fs[scfg_bypass_hyp_def] >> conj_tac
  >- metis_tac[scfg_bypass_target_distinct] >>
  rpt gen_tac >> irule scfg_bypass_edge >> simp[] >>
  fs[scfg_shape_def, scfg_inst_shape_def, unitLabelMapIdentityTheory.fn_insts_MEM,
    EVERY_MEM] >> metis_tac[lookup_block_member_label]
QED

Theorem scfg_bypass_not_entry_label:
  scfg_bypass_hyp fn a b fn' ==> fn_entry_label fn <> SOME b.bb_label
Proof
  strip_tac >> `first_block_no_preds fn` by
    metis_tac[scfg_bypass_old_static, scfg_static_first_no_preds] >>
  fs[scfg_bypass_hyp_def] >> metis_tac[scfg_bypass_not_entry]
QED

Theorem scfg_bypass_contract_entry_path:
  scfg_bypass_hyp fn a b fn' /\ scfg_entry_path fn p l /\ l <> b.bb_label ==>
  scfg_entry_path fn' (FILTER (\x. x <> b.bb_label) p) l
Proof
  strip_tac >> drule scfg_bypass_edge_eq >> strip_tac >>
  `fn_entry_label fn' = fn_entry_label fn /\
   fn_entry_label fn <> SOME b.bb_label` by
    metis_tac[scfg_bypass_entry_eq, scfg_bypass_not_entry_label] >>
  `wf_function fn` by metis_tac[scfg_bypass_old_static, scfg_static_wf] >>
  irule scfg_bypass_filter_entry_path >>
  simp[] >> qexistsl [`a.bb_label`, `fn`, `target`] >> simp[] >>
  fs[scfg_bypass_hyp_def] >>
  metis_tac[scfg_bypass_incoming, scfg_bypass_outgoing, wf_function_def]
QED

Theorem scfg_bypass_reachable:
  scfg_bypass_hyp fn a b fn' /\ fn_reachable fn l /\ l <> b.bb_label ==>
  fn_reachable fn' l
Proof
  strip_tac >> fs[fn_reachable_def] >>
  drule rtc_to_fn_path >> strip_tac >>
  `scfg_entry_path fn path l` by (simp[scfg_entry_path_def] >> metis_tac[]) >>
  drule_all scfg_bypass_contract_entry_path >>
  simp[scfg_entry_path_def] >> strip_tac >>
  drule_all is_fn_path_rtc >> simp[] >> metis_tac[]
QED

Theorem scfg_bypass_all_reachable:
  scfg_bypass_hyp fn a b fn' /\ MEM bb fn'.fn_blocks ==>
  fn_reachable fn' bb.bb_label
Proof
  strip_tac >>
  `fn_labels fn' = FILTER (\l. l <> b.bb_label) (fn_labels fn)` by
    (fs[scfg_bypass_hyp_def] >> metis_tac[simplifyCfgGraphShapeTheory.do_merge_jump_labels]) >>
  `MEM bb.bb_label (fn_labels fn')` by
    (pure_rewrite_tac[venomInstTheory.fn_labels_def, MEM_MAP] >>
     qexists `bb` >> simp[]) >>
  `bb.bb_label <> b.bb_label /\ MEM bb.bb_label (fn_labels fn)` by gvs[MEM_FILTER] >>
  `fn_reachable fn bb.bb_label` by
    (fs[venomInstTheory.fn_labels_def, MEM_MAP] >>
     metis_tac[scfg_bypass_hyp_def, scfg_normalized_reachable]) >>
  metis_tac[scfg_bypass_reachable]
QED

Theorem scfg_bypass_expand_surviving_entry:
  scfg_bypass_hyp fn a b fn' /\ scfg_entry_path fn' p l ==>
  ?q. scfg_entry_path fn q l /\ FILTER (\x. x <> b.bb_label) q = p
Proof
  strip_tac >> drule scfg_bypass_edge_eq >> strip_tac >>
  `fn_entry_label fn' = fn_entry_label fn /\
   fn_entry_label fn <> SOME b.bb_label` by
    metis_tac[scfg_bypass_entry_eq, scfg_bypass_not_entry_label] >>
  `wf_function fn` by metis_tac[scfg_bypass_old_static, scfg_static_wf] >>
  irule scfg_bypass_expand_entry_path >>
  simp[] >> qexistsl [`a.bb_label`, `fn'`, `target`] >> simp[] >>
  fs[scfg_bypass_hyp_def] >>
  metis_tac[scfg_lookup_edge, scfg_bypass_outgoing, wf_function_def,
    simplifyCfgDefsTheory.can_bypass_jump_def]
QED

Theorem scfg_bypass_dominates:
  scfg_bypass_hyp fn a b fn' /\ fn_dominates fn d l /\
  d <> b.bb_label /\ l <> b.bb_label ==> fn_dominates fn' d l
Proof
  strip_tac >> rewrite_tac[fn_dominates_def] >> conj_tac
  >- metis_tac[scfg_bypass_reachable, fn_dominates_def] >>
  rpt strip_tac >>
  `scfg_entry_path fn' path l` by (simp[scfg_entry_path_def] >> metis_tac[]) >>
  drule_all scfg_bypass_expand_surviving_entry >> strip_tac >>
  `MEM d q` by fs[fn_dominates_def, scfg_entry_path_def] >>
  qpat_x_assum `FILTER _ q = path` (SUBST1_TAC o SYM) >> simp[MEM_FILTER]
QED

(* Instruction images keep positions and outputs; PHIs and terminators are disjoint. *)
Definition scfg_bypass_term_def:
  scfg_bypass_term B target i =
    if ~is_terminator i.inst_opcode then i
    else canon_jnz_inst (subst_label_inst B target i)
End

Definition scfg_bypass_image_def:
  scfg_bypass_image A B target l i =
    if l = target then update_phi_bypass A B
      (if l = A then scfg_bypass_term B target i else i)
    else if l = A then scfg_bypass_term B target i else i
End

Definition scfg_bypass_block_def:
  scfg_bypass_block a b bb = bb with bb_instructions :=
    MAP (\i. scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) bb.bb_label i)
      bb.bb_instructions
End

Theorem scfg_bypass_block_label[simp]:
  (scfg_bypass_block a b bb).bb_label = bb.bb_label
Proof
  simp[scfg_bypass_block_def]
QED

Theorem scfg_bypass_labels_distinct_new:
  scfg_bypass_hyp fn a b fn' ==> ALL_DISTINCT (fn_labels fn')
Proof
  strip_tac >> `wf_function fn` by
    metis_tac[scfg_bypass_old_static, scfg_static_wf] >>
  fs[scfg_bypass_hyp_def] >> drule simplifyCfgGraphShapeTheory.do_merge_jump_labels >>
  strip_tac >> fs[wf_function_def] >> irule FILTER_ALL_DISTINCT >> simp[]
QED

Theorem scfg_bypass_lookup_eq:
  scfg_bypass_hyp fn a b fn' ==>
  lookup_block l fn'.fn_blocks =
    if l = b.bb_label then NONE
    else OPTION_MAP (scfg_bypass_block a b) (lookup_block l fn.fn_blocks)
Proof
  strip_tac >> fs[scfg_bypass_hyp_def] >>
  drule_all scfg_bypass_lookup >> disch_then (qspec_then `l` mp_tac) >>
  `t.bb_label = target` by metis_tac[lookup_block_member_label] >>
  simp[scfg_bypass_block_def, scfg_bypass_image_def, scfg_bypass_term_def] >>
  Cases_on `l = b.bb_label` >> simp[] >>
  Cases_on `l = a.bb_label` >> simp[]
  >- (Cases_on `target = a.bb_label` >>
      simp[scfg_bypass_block_def, scfg_bypass_image_def, scfg_bypass_term_def,
        MAP_MAP_o, combinTheory.o_DEF]) >>
  Cases_on `l = target` >> simp[]
  >- (gvs[scfg_bypass_block_def, scfg_bypass_image_def, scfg_bypass_term_def] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  Cases_on `lookup_block l fn.fn_blocks` >> simp[] >>
  `x.bb_label = l` by metis_tac[lookup_block_member_label] >>
  simp[scfg_bypass_block_def, scfg_bypass_image_def]
QED

Theorem scfg_bypass_mem:
  scfg_bypass_hyp fn a b fn' ==>
  (MEM bb' fn'.fn_blocks <=>
   ?bb. MEM bb fn.fn_blocks /\ bb.bb_label <> b.bb_label /\
     bb' = scfg_bypass_block a b bb)
Proof
  strip_tac >> eq_tac
  >- (strip_tac >>
      `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn'.fn_blocks)` by
        metis_tac[scfg_bypass_labels_distinct_new, venomInstTheory.fn_labels_def] >>
      `lookup_block bb'.bb_label fn'.fn_blocks = SOME bb'` by
        metis_tac[MEM_lookup_block] >>
      drule scfg_bypass_lookup_eq >>
      disch_then (qspec_then `bb'.bb_label` mp_tac) >> simp[] >>
      Cases_on `bb'.bb_label = b.bb_label` >> simp[] >>
      Cases_on `lookup_block bb'.bb_label fn.fn_blocks` >> simp[] >>
      strip_tac >> gvs[] >> metis_tac[lookup_block_member_label]) >>
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    metis_tac[scfg_bypass_old_static, scfg_static_wf, wf_function_def,
      venomInstTheory.fn_labels_def] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by metis_tac[MEM_lookup_block] >>
  `lookup_block bb.bb_label fn'.fn_blocks = SOME (scfg_bypass_block a b bb)` by
    (drule scfg_bypass_lookup_eq >> disch_then (qspec_then `bb.bb_label` mp_tac) >> simp[]) >>
  metis_tac[lookup_block_member_label]
QED

Theorem scfg_bypass_term_fields[simp]:
  (scfg_bypass_term B target i).inst_id = i.inst_id /\
  (scfg_bypass_term B target i).inst_outputs = i.inst_outputs
Proof
  simp[scfg_bypass_term_def] >> IF_CASES_TAC >>
  simp[canon_jnz_inst_shape, subst_label_inst_shape]
QED

Theorem scfg_bypass_image_fields[simp]:
  (scfg_bypass_image A B target l i).inst_id = i.inst_id /\
  (scfg_bypass_image A B target l i).inst_outputs = i.inst_outputs
Proof
  simp[scfg_bypass_image_def] >> rpt IF_CASES_TAC >> simp[update_phi_bypass_shape]
QED

Theorem scfg_bypass_block_length[simp]:
  LENGTH (scfg_bypass_block a b bb).bb_instructions = LENGTH bb.bb_instructions
Proof
  simp[scfg_bypass_block_def]
QED

Theorem scfg_bypass_term_classes[simp]:
  is_terminator (scfg_bypass_term B target i).inst_opcode =
    is_terminator i.inst_opcode /\
  ((scfg_bypass_term B target i).inst_opcode = PHI <=> i.inst_opcode = PHI)
Proof
  simp[scfg_bypass_term_def] >> IF_CASES_TAC >>
  simp[canon_jnz_inst_shape, subst_label_inst_shape]
QED

Theorem scfg_bypass_image_classes[simp]:
  is_terminator (scfg_bypass_image A B target l i).inst_opcode =
    is_terminator i.inst_opcode /\
  ((scfg_bypass_image A B target l i).inst_opcode = PHI <=> i.inst_opcode = PHI)
Proof
  simp[scfg_bypass_image_def] >> rpt IF_CASES_TAC >>
  simp[update_phi_bypass_def] >> rpt IF_CASES_TAC >> simp[]
QED

Theorem scfg_bypass_block_wf:
  bb_well_formed bb ==> bb_well_formed (scfg_bypass_block a b bb)
Proof
  simp[bb_well_formed_def, scfg_bypass_block_def, LENGTH_MAP] >>
  strip_tac >> simp[LAST_MAP] >> conj_tac >> rpt strip_tac >>
  gvs[EL_MAP] >> metis_tac[]
QED

Theorem scfg_bypass_blocks_eq:
  scfg_bypass_hyp fn a b fn' ==>
  fn'.fn_blocks = MAP (scfg_bypass_block a b)
    (FILTER (\bb. bb.bb_label <> b.bb_label) fn.fn_blocks)
Proof
  strip_tac >> `wf_function fn` by
    metis_tac[scfg_bypass_old_static, scfg_static_wf] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    fs[wf_function_def, venomInstTheory.fn_labels_def] >>
  fs[scfg_bypass_hyp_def] >>
  `t.bb_label = target` by metis_tac[lookup_block_member_label] >>
  `!bb. MEM bb fn.fn_blocks /\ bb.bb_label = a.bb_label ==> bb = a` by
    metis_tac[MEM_lookup_block, optionTheory.SOME_11] >>
  `!bb. MEM bb fn.fn_blocks /\ bb.bb_label = target ==> bb = t` by
    metis_tac[MEM_lookup_block, optionTheory.SOME_11] >>
  gvs[do_merge_jump_def] >>
  pure_rewrite_tac[replace_block_def, remove_block_def, MAP_MAP_o, combinTheory.o_DEF] >>
  BETA_TAC >> irule MAP_CONG >> simp[NoAsms, MEM_FILTER] >>
  qx_gen_tac `bb` >> strip_tac >>
  Cases_on `bb.bb_label = a.bb_label` >>
  Cases_on `bb.bb_label = t.bb_label` >>
  qpat_x_assum `!bb. MEM bb _ /\ bb.bb_label = a.bb_label ==> _`
    (qspec_then `bb` mp_tac) >>
  qpat_x_assum `!bb. MEM bb _ /\ bb.bb_label = t.bb_label ==> _`
    (qspec_then `bb` mp_tac) >>
  simp[] >> rpt strip_tac >> gvs[] >>
  simp[scfg_bypass_block_def, scfg_bypass_image_def, scfg_bypass_term_def,
    MAP_MAP_o, combinTheory.o_DEF] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem scfg_bypass_name:
  scfg_bypass_hyp fn a b fn' ==> fn'.fn_name = fn.fn_name
Proof
  simp[scfg_bypass_hyp_def] >> rpt strip_tac >>
  gvs[do_merge_jump_def, AllCaseEqs()]
QED
