(* Proof-only chain representation and endpoint transport interface. *)
Theory simplifyCfgMergePaths
Ancestors
  simplifyCfgMergeStatic simplifyCfgStaticInterface simplifyCfgDefs
  venomWf venomInst cfgTransform list rich_list
  simplifyCfgStruct

Definition scfg_chain_def:
  scfg_chain fn a b = fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label fn.fn_blocks)) (bb_succs (merge_blocks a b))
End

Definition scfg_chain_hyp_def:
  scfg_chain_hyp fn a b <=> scfg_normalized fn /\
    lookup_block a.bb_label fn.fn_blocks = SOME a /\
    lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_merge_blocks fn a b
End

Definition scfg_phi_image_def:
  scfg_phi_image a b l = \i.
    if MEM l (bb_succs b) then
      (if i.inst_opcode <> PHI then i else subst_label_inst b.bb_label a.bb_label i)
    else i
End

Definition scfg_chain_block_def:
  scfg_chain_block a b bb = bb with bb_instructions :=
    MAP (scfg_phi_image a b bb.bb_label)
      (if bb.bb_label = a.bb_label then FRONT a.bb_instructions ++ b.bb_instructions
       else bb.bb_instructions)
End

Theorem scfg_chain_old_wf:
  scfg_chain_hyp fn a b ==> wf_function fn
Proof
  metis_tac[scfg_chain_hyp_def, scfg_normalized_static, scfg_static_wf]
QED

Theorem scfg_chain_blocks_nonempty:
  scfg_chain_hyp fn a b ==> a.bb_instructions <> [] /\ b.bb_instructions <> []
Proof
  strip_tac >> drule scfg_chain_old_wf >>
  fs[scfg_chain_hyp_def, wf_function_def] >>
  `MEM a fn.fn_blocks /\ MEM b fn.fn_blocks` by
    metis_tac[lookup_block_member_label] >>
  metis_tac[bb_well_formed_def]
QED

Theorem scfg_chain_no_phis:
  scfg_chain_hyp fn a b ==> no_phis b
Proof
  simp[scfg_chain_hyp_def, can_merge_blocks_def]
QED

Theorem scfg_phi_image_outputs[simp]:
  (scfg_phi_image a b l i).inst_outputs = i.inst_outputs
Proof
  simp[scfg_phi_image_def] >> rpt IF_CASES_TAC >> simp[subst_label_inst_def]
QED

Theorem scfg_phi_image_opcode[simp]:
  (scfg_phi_image a b l i).inst_opcode = i.inst_opcode
Proof
  simp[scfg_phi_image_def] >> rpt IF_CASES_TAC >> simp[subst_label_inst_def]
QED

Theorem scfg_phi_image_nonphi:
  i.inst_opcode <> PHI ==> scfg_phi_image a b l i = i
Proof
  simp[scfg_phi_image_def]
QED

Theorem scfg_chain_block_label[simp]:
  (scfg_chain_block a b bb).bb_label = bb.bb_label
Proof
  simp[scfg_chain_block_def]
QED

Theorem scfg_chain_edge_eq:
  scfg_chain_hyp fn a b ==>
  (fn_cfg_edge (scfg_chain fn a b) x y <=> x <> b.bb_label /\
    if x = a.bb_label then fn_cfg_edge fn b.bb_label y else fn_cfg_edge fn x y)
Proof
  strip_tac >> irule scfg_chain_edge >>
  metis_tac[scfg_chain_def, scfg_chain_hyp_def, scfg_chain_old_wf,
    wf_function_def, scfg_chain_blocks_nonempty]
QED

Theorem scfg_chain_entry_eq:
  scfg_chain_hyp fn a b ==> fn_entry_label (scfg_chain fn a b) = fn_entry_label fn
Proof
  strip_tac >> simp[scfg_chain_def] >> irule scfg_chain_entry >>
  irule scfg_merge_not_entry >>
  metis_tac[scfg_chain_hyp_def, scfg_normalized_static, scfg_static_first_no_preds]
QED

Theorem scfg_chain_lookup_eq:
  scfg_chain_hyp fn a b ==>
  lookup_block l (scfg_chain fn a b).fn_blocks =
  OPTION_MAP (scfg_chain_block a b) (if l = b.bb_label then NONE
    else lookup_block l fn.fn_blocks)
Proof
  strip_tac >>
  `a.bb_label <> b.bb_label` by
    metis_tac[scfg_chain_hyp_def, can_merge_blocks_distinct] >>
  `b.bb_instructions <> []` by metis_tac[scfg_chain_blocks_nonempty] >>
  fs[scfg_chain_hyp_def] >>
  simp[scfg_chain_def, scfg_succ_phi_lookup, scfg_chain_body_lookup, bb_succs_merge_blocks] >>
  Cases_on `l = b.bb_label` >- simp[] >>
  Cases_on `l = a.bb_label`
  >- (Cases_on `MEM a.bb_label (bb_succs b)` >>
      simp[scfg_chain_block_def, merge_blocks_def, scfg_phi_image_def]) >>
  Cases_on `lookup_block l fn.fn_blocks` >> simp[] >>
  `x.bb_label = l` by metis_tac[lookup_block_member_label] >>
  simp[scfg_chain_block_def, scfg_phi_image_def] >>
  Cases_on `MEM l (bb_succs b)` >> simp[]
QED

Theorem scfg_chain_labels_distinct:
  scfg_chain_hyp fn a b ==> ALL_DISTINCT (fn_labels (scfg_chain fn a b))
Proof
  simp[scfg_chain_def] >> strip_tac >> irule scfg_chain_distinct >>
  metis_tac[scfg_chain_old_wf, wf_function_def]
QED

Theorem scfg_chain_lookup_member:
  scfg_chain_hyp fn a b /\ MEM bb fn.fn_blocks /\ bb.bb_label <> b.bb_label ==>
  lookup_block bb.bb_label (scfg_chain fn a b).fn_blocks = SOME (scfg_chain_block a b bb)
Proof
  rpt strip_tac >> simp[scfg_chain_lookup_eq] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    metis_tac[scfg_chain_old_wf, wf_function_def, fn_labels_def] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    metis_tac[venomExecPropsTheory.MEM_lookup_block] >> simp[]
QED

Theorem scfg_chain_mem:
  scfg_chain_hyp fn a b ==>
  (MEM bb' (scfg_chain fn a b).fn_blocks <=>
   ?bb. MEM bb fn.fn_blocks /\ bb.bb_label <> b.bb_label /\
     bb' = scfg_chain_block a b bb)
Proof
  strip_tac >> eq_tac
  >- (strip_tac >>
      `ALL_DISTINCT (MAP (\bb. bb.bb_label) (scfg_chain fn a b).fn_blocks)` by
        metis_tac[scfg_chain_labels_distinct, fn_labels_def] >>
      `lookup_block bb'.bb_label (scfg_chain fn a b).fn_blocks = SOME bb'` by
        metis_tac[venomExecPropsTheory.MEM_lookup_block] >>
      drule scfg_chain_lookup_eq >>
      disch_then (qspec_then `bb'.bb_label` mp_tac) >> simp[] >>
      Cases_on `bb'.bb_label = b.bb_label` >> simp[] >>
      Cases_on `lookup_block bb'.bb_label fn.fn_blocks` >> simp[] >>
      strip_tac >> gvs[] >>
      metis_tac[lookup_block_member_label, scfg_chain_block_label]) >>
  rpt strip_tac >> drule_all scfg_chain_lookup_member >>
  metis_tac[lookup_block_member_label]
QED

Theorem scfg_phi_image_el_outputs:
  j < LENGTH insts ==>
  (EL j (MAP (scfg_phi_image a b l) insts)).inst_outputs = (EL j insts).inst_outputs
Proof
  simp[EL_MAP]
QED

Definition scfg_entry_path_def:
  scfg_entry_path fn p t <=> is_fn_path fn p /\ p <> [] /\
    (?e. fn_entry_label fn = SOME e /\ HD p = e) /\ LAST p = t
End

Theorem scfg_chain_distinct_labels:
  scfg_chain_hyp fn a b ==> a.bb_label <> b.bb_label
Proof
  metis_tac[scfg_chain_hyp_def, can_merge_blocks_distinct]
QED

Theorem scfg_chain_incoming:
  scfg_chain_hyp fn a b /\ fn_cfg_edge fn x b.bb_label ==> x = a.bb_label
Proof
  simp[fn_cfg_edge_def] >> rpt strip_tac >>
  `bb = a` by metis_tac[scfg_merge_incoming, scfg_chain_hyp_def] >> gvs[]
QED

Theorem scfg_filter_endpoints:
  p <> [] /\ P (HD p) /\ P (LAST p) ==>
  FILTER P p <> [] /\ HD (FILTER P p) = HD p /\ LAST (FILTER P p) = LAST p
Proof
  strip_tac >>
  `FILTER P p <> [] /\ HD (FILTER P p) = HD p` by
    (Cases_on `p` >> gvs[]) >> simp[] >>
  Cases_on `p` using SNOC_CASES >>
  gvs[FILTER_SNOC, LAST_SNOC]
QED
