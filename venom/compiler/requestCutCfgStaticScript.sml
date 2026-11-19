Theory requestCutCfgStatic
Ancestors
  o1ContractCfgNormJointCursors o1ContractCfgNormCursors o1ContractCfgNorm
  cfgNormSupplySim staticAbortDefs stateFrame venomWfProps venomWf
  contextCodegenRel venomExecProofs venomInst venomState list pair

Theorem static_abort_at_not_terminator[local]:
  static_abort_at bb i /\ get_instruction bb i = SOME inst ==>
  ~is_terminator inst.inst_opcode
Proof
  simp_tac pure_ss [static_abort_at_def] >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `j` assume_tac) assume_tac) >>
  Cases_on `i = j`
  >- (`j < LENGTH bb.bb_instructions` by fs[static_abort_pair_def] >>
      `inst = EL j bb.bb_instructions` by fs[get_instruction_def] >>
      qpat_x_assum `static_abort_pair bb i j` mp_tac >>
      simp[static_abort_pair_def] >> strip_tac >> gvs[is_terminator_def]) >>
  fs[static_abort_pair_def] >>
  `i < j` by decide_tac >>
  qpat_x_assum `!k inst'. _` (qspecl_then [`i`,`inst`] mp_tac) >>
  simp[]
QED

Theorem cfg_norm_cursors_static_prefix[local]:
  !C rounds cells. cfg_norm_cursors C rounds cells ==>
    in_static_abort_prefix (FST (SND (HD rounds))) (SND (FST (HD cells))) ==>
    in_static_abort_prefix (FST (SND (LAST rounds))) (SND (FST (LAST cells)))
Proof
  ho_match_mp_tac cfg_norm_cursors_ind >>
  pure_rewrite_tac [HD, LAST_CONS, FST, SND, NOT_CONS_NIL] >> rpt strip_tac
  >- suspend "body"
  >> suspend "split"
QED

Resume cfg_norm_cursors_static_prefix[body]:
  first_x_assum irule >>
  `wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s` by
    fs[supply_norm_inv_def] >>
  gvs[in_static_abort_prefix_def] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >>
  gvs[] >>
  `~MEM split.bb_label (fn_labels fn)` by metis_tac[supply_split_label_not_old] >>
  `split.bb_label <> bb.bb_label` by
    (fs[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `lookup_block bb.bb_label next_fn.fn_blocks =
    SOME (supply_block_image pred target split repls bb)` by
    (irule insert_split_supply_image_lookup >> metis_tac[]) >>
  `v.vs_call_ctx = a.vs_call_ctx` by fs[supply_state_agree_def, execution_frame_def] >>
  simp[static_abort_at_def] >> fs[static_abort_at_def] >>
  metis_tac[supply_block_image_static_abort_pair]
QED

Resume cfg_norm_cursors_static_prefix[split]:
  `wf_function fn` by fs[supply_norm_inv_def] >>
  gvs[in_static_abort_prefix_def, active_inst_def] >>
  `lookup_block pred.bb_label fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >>
  `get_instruction bb a.vs_inst_idx = SOME (EL a.vs_inst_idx bb.bb_instructions)` by
    simp[get_instruction_def] >>
  metis_tac[static_abort_at_not_terminator, optionTheory.SOME_11]
QED

Finalise cfg_norm_cursors_static_prefix

Theorem request_cut_cfg_static_prefix:
  cfg_norm_joint_cursors C8 C9 (schedules,(rounds,cells),saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
  in_static_abort_prefix fn8 s8 ==>
  in_static_abort_prefix fn9 s9
Proof
  strip_tac >> fs[cfg_norm_joint_cursors_def] >>
  qpat_x_assum `EVERY _ schedules` (mp_tac o SIMP_RULE (srw_ss()) [EVERY_MEM]) >>
  disch_then (qspec_then `(fn8,fn9,rounds)` mp_tac) >>
  simp[] >> strip_tac >>
  drule cfg_norm_cursors_static_prefix >> simp[]
QED
