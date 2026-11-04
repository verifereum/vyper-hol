(* Static closure of the exact chain contraction: the base's chain_merge
   lemmas, specialized to scfg_chain, plus shape and PHI support. *)
Theory simplifyCfgMergeClosure
Ancestors
  simplifyCfgShapeCore
  simplifyCfgMergePaths simplifyCfgMergeAvailability simplifyCfgPhiSemantics
  simplifyCfgMergeStatic simplifyCfgStaticInterface simplifyCfgDefs
  venomWf venomInst cfgTransform unitShapeDefs unitLabelMapIdentity list rich_list
  simplifyCfgStruct simplifyCfgPhiRepair simplifyCfgPhiPreds
  simplifyCfgChainDataflow simplifyCfgWfssa simplifyCfgReachuses cfgWf

Theorem scfg_chain_base_hyp:
  scfg_chain_hyp fn a b ==>
  wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\
  scfg_phi_safe fn /\ fn_defs_reach_uses fn /\ scfg_phi_preds fn /\
  all_reachable fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  can_merge_blocks fn a b
Proof
  strip_tac >>
  `scfg_static fn` by metis_tac[scfg_chain_hyp_def, scfg_normalized_static] >>
  fs[scfg_static_def, simplify_cfg_fn_ok_phi_safe] >> rpt conj_tac
  >- (simp[scfg_phi_preds_def] >> rpt strip_tac >>
      drule scfg_phi_pair_label >> strip_tac >>
      `MEM p (pred_labels fn bb.bb_label)` by
        metis_tac[scfg_chain_hyp_def, scfg_normalized_phi_support] >>
      fs[pred_labels_def, block_preds_def, MEM_MAP, MEM_FILTER, fn_cfg_edge_def] >>
      metis_tac[])
  >- fs[scfg_chain_hyp_def, scfg_normalized_def, all_reachable_def] >>
  metis_tac[scfg_chain_hyp_def, lookup_block_member_label]
QED

Theorem scfg_chain_wf:
  scfg_chain_hyp fn a b ==> wf_function (scfg_chain fn a b)
Proof
  strip_tac >> drule scfg_chain_base_hyp >> strip_tac >>
  rewrite_tac[scfg_chain_def] >> irule chain_merge_wf >> fs[scfg_chain_hyp_def]
QED

Theorem scfg_chain_ok:
  scfg_chain_hyp fn a b ==> simplify_cfg_fn_ok (scfg_chain fn a b)
Proof
  strip_tac >> drule scfg_chain_base_hyp >> strip_tac >>
  rewrite_tac[simplify_cfg_fn_ok_phi_safe] >> conj_tac
  >- (mp_tac (Q.INST [`fn'` |-> `scfg_chain fn a b`] chain_merge_phi_safe) >>
      simp[scfg_chain_def]) >>
  mp_tac (Q.INST [`fn'` |-> `scfg_chain fn a b`]
    simplifyCfgReachusesTheory.chain_merge_defs_reach_uses) >>
  simp[scfg_chain_def]
QED

Theorem scfg_chain_pred_transport:
  scfg_chain_hyp fn a b /\ l <> b.bb_label /\ MEM p (pred_labels fn l) ==>
  MEM (if p = b.bb_label then a.bb_label else p)
    (pred_labels (scfg_chain fn a b) l)
Proof
  strip_tac >>
  `fn_cfg_edge fn p l` by
    (fs[pred_labels_def, block_preds_def, MEM_MAP, MEM_FILTER, fn_cfg_edge_def] >>
     metis_tac[]) >>
  `p <> a.bb_label` by
    (drule_all scfg_chain_old_pred_not_a >> simp[]) >>
  `fn_cfg_edge (scfg_chain fn a b)
     (if p = b.bb_label then a.bb_label else p) l` by
    (simp[scfg_chain_edge_eq] >> Cases_on `p = b.bb_label` >> gvs[] >>
     metis_tac[scfg_chain_hyp_def, can_merge_blocks_distinct]) >>
  fs[fn_cfg_edge_def, pred_labels_def, block_preds_def, MEM_MAP, MEM_FILTER] >>
  metis_tac[]
QED

Theorem scfg_phi_image_labels:
  i.inst_opcode = PHI ==>
  (MEM (Label p) (scfg_phi_image a b l i).inst_operands <=>
   ?q. MEM (Label q) i.inst_operands /\
     p = if MEM l (bb_succs b) /\ q = b.bb_label then a.bb_label else q)
Proof
  strip_tac >> simp[scfg_phi_image_def] >>
  Cases_on `MEM l (bb_succs b)` >> simp[subst_label_inst_def, MEM_MAP] >>
  eq_tac >> rpt strip_tac >> gvs[]
  >- (Cases_on `y` >> gvs[subst_label_op_def] >>
      Cases_on `s = b.bb_label` >> gvs[] >> metis_tac[]) >>
  qexists_tac `Label q` >> simp[subst_label_op_def] >>
  Cases_on `q = b.bb_label` >> gvs[]
QED

Theorem scfg_chain_phi_support:
  scfg_chain_hyp fn a b /\ MEM bb (scfg_chain fn a b).fn_blocks /\
  MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\ MEM (Label l) i.inst_operands ==>
  MEM l (pred_labels (scfg_chain fn a b) bb.bb_label)
Proof
  strip_tac >>
  `no_phis b` by metis_tac[scfg_chain_no_phis] >>
  drule scfg_chain_mem >> disch_then (qspec_then `bb` mp_tac) >>
  simp[] >> strip_tac >> rename1 `bb = scfg_chain_block _ _ ob` >>
  gvs[scfg_chain_block_def, MEM_MAP] >>
  rename1 `MEM old (if _ then _ else _)` >>
  `old.inst_opcode = PHI` by metis_tac[scfg_phi_image_opcode] >>
  `MEM old ob.bb_instructions` by
    (Cases_on `ob.bb_label = a.bb_label` >> gvs[MEM_APPEND]
     >- (`ob = a` by metis_tac[scfg_chain_hyp_def, scfg_chain_old_wf,
           wf_function_def, venomExecProofsTheory.same_label_same_block,
           lookup_block_member_label] >>
         metis_tac[APPEND_FRONT_LAST, MEM_APPEND, scfg_chain_blocks_nonempty]) >>
     fs[no_phis_def, EVERY_MEM] >> metis_tac[]) >>
  `?q. MEM (Label q) old.inst_operands /\
    l = if MEM ob.bb_label (bb_succs b) /\ q = b.bb_label then a.bb_label else q` by
    metis_tac[scfg_phi_image_labels] >>
  `MEM q (pred_labels fn ob.bb_label)` by
    metis_tac[scfg_chain_hyp_def, scfg_normalized_phi_support] >>
  `MEM (if q = b.bb_label then a.bb_label else q)
     (pred_labels (scfg_chain fn a b) ob.bb_label)` by
    metis_tac[scfg_chain_pred_transport] >>
  Cases_on `q = b.bb_label` >> gvs[] >>
  `MEM ob.bb_label (bb_succs b)` by
    (fs[pred_labels_def, block_preds_def, MEM_MAP, MEM_FILTER] >>
     rename1 `b.bb_label = pred.bb_label` >>
     `pred = b` by metis_tac[scfg_chain_hyp_def, scfg_chain_old_wf,
       wf_function_def, venomExecProofsTheory.same_label_same_block,
       lookup_block_member_label] >> metis_tac[]) >> simp[]
QED

Theorem scfg_chain_inst_mem:
  scfg_chain_hyp fn a b /\ MEM i (fn_insts (scfg_chain fn a b)) ==>
  ?old l. MEM old (fn_insts fn) /\ i = scfg_phi_image a b l old
Proof
  simp[fn_insts_MEM] >> rpt strip_tac >>
  drule scfg_chain_mem >> disch_then (qspec_then `bb` mp_tac) >>
  simp[] >> strip_tac >> rename1 `bb = scfg_chain_block _ _ ob` >>
  gvs[scfg_chain_block_def, MEM_MAP] >>
  qexistsl_tac [`y`, `ob.bb_label`] >> simp[] >>
  Cases_on `ob.bb_label = a.bb_label` >> gvs[MEM_APPEND] >>
  metis_tac[scfg_chain_hyp_def, lookup_block_member_label,
    APPEND_FRONT_LAST, MEM_APPEND, scfg_chain_blocks_nonempty]
QED

Theorem scfg_phi_image_var:
  MEM (Var x) (scfg_phi_image a b l i).inst_operands <=> MEM (Var x) i.inst_operands
Proof
  simp[scfg_phi_image_def] >> rpt IF_CASES_TAC >>
  simp[subst_label_inst_def, MEM_MAP] >> eq_tac >> rpt strip_tac >> gvs[]
  >- (Cases_on `y` >> gvs[subst_label_op_def] >>
      Cases_on `s = b.bb_label` >> gvs[]) >>
  qexists_tac `Var x` >> simp[subst_label_op_def]
QED

Theorem scfg_phi_image_shape:
  scfg_inst_shape i ==> scfg_inst_shape (scfg_phi_image a b l i)
Proof
  strip_tac >> Cases_on `i.inst_opcode = PHI`
  >- simp[scfg_inst_shape_def, is_read0_opcode_def, scfg_label_positions_def, label_positions_ok_def] >>
  simp[scfg_phi_image_nonphi]
QED

Theorem scfg_chain_copy_phi_var:
  scfg_chain_hyp fn a b /\ copy_phi_var origin (scfg_chain fn a b) x ==>
  copy_phi_var origin fn x
Proof
  `!origin f x. copy_phi_var origin f x ==> !fn a b.
    f = scfg_chain fn a b /\ scfg_chain_hyp fn a b ==> copy_phi_var origin fn x`
    suffices_by metis_tac[] >>
  Induct_on `copy_phi_var` >> rpt strip_tac
  >- (gvs[] >> drule_all scfg_chain_inst_mem >> strip_tac >> gvs[] >>
      metis_tac[copy_phi_var_seed, scfg_phi_image_opcode, scfg_phi_image_outputs])
  >- (gvs[] >> drule_all scfg_chain_inst_mem >> strip_tac >> gvs[] >>
      `old.inst_opcode = ASSIGN` by metis_tac[scfg_phi_image_opcode] >>
      `scfg_phi_image a b l old = old` by simp[scfg_phi_image_nonphi] >>
      metis_tac[copy_phi_var_assign]) >>
  gvs[] >> drule_all scfg_chain_inst_mem >> strip_tac >> gvs[] >>
  metis_tac[copy_phi_var_phi, scfg_phi_image_opcode, scfg_phi_image_outputs,
    scfg_phi_image_var]
QED

Theorem scfg_phi_image_opaque_use:
  (gas_use_ok i x ==> gas_use_ok (scfg_phi_image a b l i) x) /\
  (retpc_use_ok i x ==> retpc_use_ok (scfg_phi_image a b l i) x)
Proof
  Cases_on `i.inst_opcode = PHI`
  >- simp[gas_use_ok_def, retpc_use_ok_def] >>
  simp[scfg_phi_image_nonphi]
QED

Theorem scfg_chain_opaque:
  scfg_chain_hyp fn a b ==> opaque_use_ok (scfg_chain fn a b)
Proof
  strip_tac >>
  `opaque_use_ok fn` by metis_tac[scfg_chain_hyp_def, scfg_normalized_static,
    scfg_static_shape, scfg_shape_def] >>
  simp[opaque_use_ok_def] >> rpt strip_tac >>
  drule_all scfg_chain_inst_mem >> strip_tac >> gvs[] >>
  `MEM (Var x) old.inst_operands` by metis_tac[scfg_phi_image_var] >>
  `!v. gas_var (scfg_chain fn a b) v ==> gas_var fn v` by
    (simp[gas_var_def] >> metis_tac[scfg_chain_copy_phi_var]) >>
  `!v. retpc_var (scfg_chain fn a b) v ==> retpc_var fn v` by
    (simp[retpc_var_def] >> metis_tac[scfg_chain_copy_phi_var]) >>
  fs[opaque_use_ok_def] >> metis_tac[scfg_phi_image_opaque_use]
QED

Theorem scfg_chain_shape:
  scfg_chain_hyp fn a b ==> scfg_shape (scfg_chain fn a b)
Proof
  strip_tac >>
  `scfg_shape fn` by metis_tac[scfg_chain_hyp_def, scfg_normalized_static,
    scfg_static_shape] >>
  rewrite_tac[scfg_shape_def] >> conj_tac
  >- (simp[scfg_chain_entry_eq, scfg_chain_def] >> fs[scfg_shape_def]) >>
  conj_tac >- metis_tac[scfg_chain_opaque] >> conj_tac
  >- (fs[scfg_shape_def, EVERY_MEM] >>
      metis_tac[scfg_chain_mem, scfg_chain_block_label]) >>
  simp[EVERY_MEM] >> rpt strip_tac >> drule_all scfg_chain_inst_mem >>
  strip_tac >> gvs[] >> irule scfg_phi_image_shape >>
  fs[scfg_shape_def, EVERY_MEM] >> metis_tac[]
QED

Theorem scfg_chain_normalized:
  scfg_chain_hyp fn a b ==> scfg_normalized (scfg_chain fn a b)
Proof
  strip_tac >> drule scfg_chain_base_hyp >> strip_tac >>
  rewrite_tac[scfg_normalized_def, scfg_static_def] >> rpt conj_tac
  >- metis_tac[scfg_chain_wf]
  >- (rewrite_tac[scfg_chain_def] >> irule chain_merge_fn_inst_wf >> simp[])
  >- metis_tac[scfg_chain_shape]
  >- (rewrite_tac[scfg_chain_def] >> irule chain_merge_first_block_no_preds >>
      simp[])
  >- metis_tac[scfg_chain_ok]
  >- (mp_tac (Q.INST [`fn'` |-> `scfg_chain fn a b`] chain_merge_all_reachable) >>
      simp[scfg_chain_def] >> simp[all_reachable_def]) >>
  metis_tac[scfg_chain_phi_support]
QED
