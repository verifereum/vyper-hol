Theory loadElimActualPhiFrame
Ancestors
  loadElimPhiTransport loadElimMemoryRel loadElimPaddedSimHelpers loadElimDynamicCapture
  loadElimHistoryHelpers loadElimOperationalHistory venomState stateFrame
  list finite_map pred_set venomExecSemantics analysisSimDefs loadElimDefs
  loadElimTargetWrites loadElimOccurrenceCoverage loadElimPhiCapture

Theorem padded_exec_equiv_update_fresh_right:
  v IN vars /\ padded_exec_equiv vars s t ==>
  padded_exec_equiv vars s (update_var v w t)
Proof
  simp[padded_exec_equiv_def, lookup_var_def, update_var_def,
       read_memory_def, execution_frame_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* All reads use t, not the recursively updated state. *)
Theorem le_snapshot_batch_fresh_right:
  !ys t s.
    padded_exec_equiv vars s t /\
    (!j. MEM j ys ==> ?v w. read t j = SOME (v,w) /\ v IN vars) ==>
    ?q. le_snapshot_batch read t ys = SOME q /\ padded_exec_equiv vars s q
Proof
  Induct >- simp[le_snapshot_batch_def] >>
  rpt gen_tac >> strip_tac >>
  `?v w. read t h = SOME (v,w) /\ v IN vars` by metis_tac[MEM] >>
  `?q. le_snapshot_batch read t ys = SOME q /\ padded_exec_equiv vars s q` by
    (first_x_assum irule >> simp[] >> metis_tac[MEM]) >>
  simp[le_snapshot_batch_def] >>
  metis_tac[padded_exec_equiv_update_fresh_right]
QED

(* Original prefix, followed by fresh generated outputs, one snapshot. *)
Theorem le_snapshot_batch_append_fresh_transport:
  !xs s t p.
    padded_exec_equiv vars s t /\
    (!j. MEM j xs ==> read s j = read t j) /\
    le_snapshot_batch read s xs = SOME p /\
    (!j. MEM j ys ==> ?v w. read t j = SOME (v,w) /\ v IN vars) ==>
    ?q. le_snapshot_batch read t (xs ++ ys) = SOME q /\
        padded_exec_equiv vars p q
Proof
  Induct >- (simp[le_snapshot_batch_def] >>
    metis_tac[le_snapshot_batch_fresh_right]) >>
  rpt gen_tac >> strip_tac >>
  gvs[le_snapshot_batch_def, AllCaseEqs()] >>
  `read t h = SOME (out,value)` by metis_tac[MEM] >>
  `?q. le_snapshot_batch read t (xs ++ ys) = SOME q /\
       padded_exec_equiv vars t' q` by
    (first_x_assum irule >> simp[] >> metis_tac[MEM]) >>
  simp[le_snapshot_batch_def] >>
  metis_tac[padded_exec_equiv_update_var]
QED

Theorem le_phi_prefix_insert_after_prefix:
  !xs ys. EVERY (\j. j.inst_opcode = PHI) ys ==>
    le_phi_prefix (TAKE (phi_prefix_length xs) xs ++ ys ++
                   DROP (phi_prefix_length xs) xs) = le_phi_prefix xs ++ ys
Proof
  Induct >- (simp[phi_prefix_length_def, le_phi_prefix_def] >>
    Induct_on `ys` >> simp[le_phi_prefix_def]) >>
  rpt strip_tac >> Cases_on `h.inst_opcode = PHI` >>
  simp[phi_prefix_length_def, le_phi_prefix_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  drule le_phi_prefix_append >>
  disch_then (qspec_then `h::xs` mp_tac) >>
  simp[le_phi_prefix_def]
QED

Theorem le_actual_prepend_phi_prefix:
  le_configured_context ctx ==>
  le_phi_prefix
    (analysis_block_transform_prepend NONE result (load_phi_prepend actions)
      (\ll inst. [load_elim_inst ctx actions ll inst]) bb).bb_instructions =
    le_phi_prefix bb.bb_instructions ++ phis_for_block actions bb.bb_label
Proof
  strip_tac >>
  `EVERY (\j. j.inst_opcode = PHI) (phis_for_block actions bb.bb_label)` by
    simp[phis_for_block_def, EVERY_MAP, EVERY_FILTER] >>
  simp[analysis_block_transform_prepend_def, load_phi_prepend_def,
       passSimulationPropsTheory.flat_mapi_singleton,
       le_phi_prefix_insert_after_prefix, le_configured_transformed_phi_prefix]
QED

Theorem le_actual_prepend_phis_transport:
  le_configured_context ctx /\ padded_exec_equiv vars u r /\
  u.vs_prev_bb = r.vs_prev_bb /\ u.vs_labels = r.vs_labels /\
  (!j v. MEM j (le_phi_prefix bb.bb_instructions) /\
     MEM (Var v) j.inst_operands ==> lookup_var v u = lookup_var v r) /\
  eval_phis u bb.bb_instructions = OK p /\
  (!j. MEM j (phis_for_block actions bb.bb_label) ==>
       ?v w. eval_one_phi r j = SOME (v,w) /\ v IN vars) ==>
  ?q. eval_phis r
    (analysis_block_transform_prepend NONE result (load_phi_prepend actions)
      (\ll inst. [load_elim_inst ctx actions ll inst]) bb).bb_instructions = OK q /\
    padded_exec_equiv vars p q
Proof
  strip_tac >> simp[le_eval_phis_snapshot, le_actual_prepend_phi_prefix] >>
  irule le_snapshot_batch_append_fresh_transport >>
  conj_tac >- simp[] >> qexists_tac `u` >> simp[] >>
  conj_tac >- (rpt strip_tac >> irule le_eval_one_phi_agreement >>
    simp[] >> metis_tac[]) >>
  metis_tac[le_eval_phis_snapshot]
QED

Theorem le_snapshot_batch_append_frame:
  !xs s q.
    le_snapshot_batch read s ys = SOME z /\
    le_snapshot_batch read s (xs ++ ys) = SOME q /\
    (!j w. MEM j xs ==> read s j <> SOME (v,w)) ==>
    lookup_var v q = lookup_var v z
Proof
  Induct >- (rpt strip_tac >> gvs[]) >> rpt gen_tac >> strip_tac >>
  gvs[le_snapshot_batch_def, AllCaseEqs()] >>
  `out <> v` by metis_tac[MEM] >>
  `lookup_var v t = lookup_var v z` by
    (first_x_assum irule >> metis_tac[MEM]) >>
  gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem le_collected_generated_reads_in_set:
  eval_phis r (phis_for_block (collect_phi_actions m ctx cfg result fn) lbl) = OK z /\
  (!pa. MEM pa (collect_phi_actions m ctx cfg result fn) ==> pa.pa_phi_out IN G) ==>
  !j. MEM j (phis_for_block (collect_phi_actions m ctx cfg result fn) lbl) ==>
    ?v w. eval_one_phi r j = SOME (v,w) /\ v IN G
Proof
  strip_tac >>
  `le_phi_prefix (phis_for_block (collect_phi_actions m ctx cfg result fn) lbl) =
    phis_for_block (collect_phi_actions m ctx cfg result fn) lbl` by
    (`EVERY (\j. j.inst_opcode = PHI)
       (phis_for_block (collect_phi_actions m ctx cfg result fn) lbl)` by
       simp[phis_for_block_def, EVERY_MAP, EVERY_FILTER] >>
     drule le_phi_prefix_append >> disch_then (qspec_then `[]` mp_tac) >>
     simp[le_phi_prefix_def]) >>
  gvs[le_eval_phis_snapshot] >> rpt strip_tac >>
  drule_all le_snapshot_batch_reads >> strip_tac >>
  qexistsl [`out`, `value`] >> simp[] >>
  drule venomExecProofsTheory.eval_one_phi_output_mem >>
  qpat_x_assum `MEM j _` mp_tac >>
  simp[phis_for_block_def, MEM_MAP, MEM_FILTER] >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem le_actual_prepend_generated_lookup:
  le_configured_context ctx /\
  eval_phis r (phis_for_block actions bb.bb_label) = OK z /\
  eval_phis r
    (analysis_block_transform_prepend NONE result (load_phi_prepend actions)
      (\ll inst. [load_elim_inst ctx actions ll inst]) bb).bb_instructions = OK q /\
  (!j. MEM j bb.bb_instructions ==> ~MEM v j.inst_outputs) ==>
  lookup_var v q = lookup_var v z
Proof
  strip_tac >> irule (INST_TYPE [alpha |-> ``:instruction``] le_snapshot_batch_append_frame) >>
  qexistsl [`eval_one_phi`, `r`, `le_phi_prefix bb.bb_instructions`,
             `phis_for_block actions bb.bb_label`] >>
  conj_tac >- (rpt strip_tac >>
    drule venomExecProofsTheory.eval_one_phi_output_mem >>
    `MEM j bb.bb_instructions` by
      (fs[le_phi_prefix_take] >> metis_tac[rich_listTheory.MEM_TAKE]) >>
    metis_tac[]) >>
  fs[le_eval_phis_snapshot, le_actual_prepend_phi_prefix] >>
  `le_phi_prefix (phis_for_block actions bb.bb_label) =
    phis_for_block actions bb.bb_label` by
    (`EVERY (\j. j.inst_opcode = PHI) (phis_for_block actions bb.bb_label)` by
       simp[phis_for_block_def, EVERY_MAP, EVERY_FILTER] >>
     drule le_phi_prefix_append >> disch_then (qspec_then `[]` mp_tac) >>
     simp[le_phi_prefix_def]) >> gvs[le_actual_prepend_phi_prefix]
QED

Theorem le_snapshot_batch_controls:
  !xs r q. le_snapshot_batch read r xs = SOME q ==>
    q.vs_current_bb = r.vs_current_bb /\
    q.vs_inst_idx = r.vs_inst_idx /\ q.vs_prev_bb = r.vs_prev_bb /\
    q.vs_labels = r.vs_labels
Proof
  Induct >> simp[le_snapshot_batch_def] >> rpt gen_tac >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[update_var_def] >>
  first_x_assum drule >> simp[]
QED

Theorem le_occ_prefix_actual_phis_frame:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  le_occ_prefix C fn s0 (pre ++ PhiOcc bb u p :: suffix) i s /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  r.vs_prev_bb = u.vs_prev_bb /\ r.vs_labels = u.vs_labels /\
  DISJOINT G (set (fn_all_vars fn)) /\
  (!pa. MEM pa (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) ==>
    pa.pa_phi_out IN G) /\
  padded_exec_equiv G u r /\
  ALL_DISTINCT (cfg_preds_of (cfg_analyze fn) bb.bb_label) ==>
  ?q. eval_phis r
    (analysis_block_transform_prepend NONE (load_analyze ctx fn)
      (load_phi_prepend (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn))
      (\ll inst. [load_elim_inst ctx
        (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) ll inst]) bb).bb_instructions = OK q /\
    padded_exec_equiv G p q /\
    q.vs_current_bb = r.vs_current_bb /\ q.vs_inst_idx = r.vs_inst_idx /\
    q.vs_prev_bb = r.vs_prev_bb /\ q.vs_labels = r.vs_labels /\
    (!pa. MEM pa (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) /\
      bb.bb_label = pa.pa_join_lbl ==>
      ?key lbl inst w.
        compute_phi_action m (cfg_analyze fn) (load_analyze ctx fn) key lbl inst = SOME pa /\
        le_key_read ctx.lctx_addr_space key u = SOME w /\
        lookup_var pa.pa_phi_out q = SOME w)
Proof
  strip_tac >>
  `!v. v NOTIN G ==> lookup_var v u = lookup_var v r` by
    fs[padded_exec_equiv_def] >>
  `eval_phis r [] = OK r` by simp[eval_phis_def] >>
  drule_all le_occ_prefix_all_entries_phis_success >>
  disch_then (qspec_then `m` (qx_choose_then `z` assume_tac)) >>
  `eval_phis r (phis_for_block
     (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
     bb.bb_label) = OK z` by fs[] >>
  drule loadElimOccurrenceInversionTheory.le_occ_prefix_phi_semantics >> strip_tac >>
  `!j v. MEM j (le_phi_prefix bb.bb_instructions) /\ MEM (Var v) j.inst_operands ==>
     lookup_var v u = lookup_var v r` by
    (rpt strip_tac >>
     `MEM j bb.bb_instructions` by
       (fs[le_phi_prefix_take] >> metis_tac[rich_listTheory.MEM_TAKE]) >>
     `MEM bb fn.fn_blocks` by metis_tac[livenessTransferProofsTheory.lookup_block_mem] >>
     `MEM v (fn_all_vars fn)` by
       metis_tac[cfgNormBaseTheory.inst_operand_var_in_fn_all_vars] >>
     fs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
  `!j. MEM j (phis_for_block
      (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) bb.bb_label) ==>
      ?v w. eval_one_phi r j = SOME (v,w) /\ v IN G` by
     (metis_tac[le_collected_generated_reads_in_set]) >>
  `u.vs_prev_bb = r.vs_prev_bb /\ u.vs_labels = r.vs_labels` by simp[] >>
  drule_all le_actual_prepend_phis_transport >>
  disch_then (qspec_then `load_analyze ctx fn` (qx_choose_then `q` strip_assume_tac)) >>
  qpat_assum `eval_phis r (analysis_block_transform_prepend _ _ _ _ _).bb_instructions = OK q`
    (mp_tac o REWRITE_RULE [le_eval_phis_snapshot]) >>
  disch_then (mp_tac o MATCH_MP le_snapshot_batch_controls) >> strip_tac >>
  qexists_tac `q` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  `ALL_DISTINCT (cfg_preds_of (cfg_analyze fn) pa.pa_join_lbl)` by metis_tac[] >>
  `eval_phis r (phis_for_block
      (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
      pa.pa_join_lbl ++ []) = OK z` by metis_tac[APPEND_NIL] >>
  drule_all le_occ_prefix_collected_action_capture >> strip_tac >>
  `!j. MEM j bb.bb_instructions ==> ~MEM pa.pa_phi_out j.inst_outputs` by
    (`pa.pa_phi_out NOTIN set (fn_all_vars fn)` by
       (fs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
     rpt strip_tac >>
     `MEM bb fn.fn_blocks` by metis_tac[livenessTransferProofsTheory.lookup_block_mem] >>
     fs[cfgTransformTheory.fn_all_vars_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
     metis_tac[]) >>
  drule_all le_actual_prepend_generated_lookup >> disch_tac >> metis_tac[]
QED
