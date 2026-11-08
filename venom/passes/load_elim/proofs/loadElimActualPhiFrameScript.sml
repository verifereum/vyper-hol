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

Theorem le_collected_generated_reads_reserved:
  eval_phis r (phis_for_block (collect_phi_actions m ctx cfg result fn) lbl) = OK z ==>
  !j. MEM j (phis_for_block (collect_phi_actions m ctx cfg result fn) lbl) ==>
    ?v w. eval_one_phi r j = SOME (v,w) /\ isPREFIX "$le_phi_" v
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
  drule loadElimActionFreshnessTheory.le_collected_action_output_prefix >> simp[]
QED

Theorem le_occ_prefix_actual_phis_frame:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  le_occ_prefix C fn s0 (pre ++ PhiOcc bb u p :: suffix) i s /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  ctx.lctx_aliases = ma_analyze ctx.lctx_bp fn ctx.lctx_addr_space /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  (!bb' n fuel u' t'. MEM (StepOcc bb' n fuel u' t')
    (pre ++ PhiOcc bb u p :: suffix) ==> dfg_assigns_sound ctx.lctx_dfg u') /\
  r.vs_prev_bb = u.vs_prev_bb /\ r.vs_labels = u.vs_labels /\
  EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars fn) /\
  padded_exec_equiv {v | isPREFIX "$le_phi_" v} u r /\
  ALL_DISTINCT (cfg_preds_of (cfg_analyze fn) bb.bb_label) ==>
  ?q. eval_phis r
    (analysis_block_transform_prepend NONE (load_analyze ctx fn)
      (load_phi_prepend (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn))
      (\ll inst. [load_elim_inst ctx
        (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) ll inst]) bb).bb_instructions = OK q /\
    padded_exec_equiv {v | isPREFIX "$le_phi_" v} p q
Proof
  strip_tac >>
  `!v. ~isPREFIX "$le_phi_" v ==> lookup_var v u = lookup_var v r` by
    fs[padded_exec_equiv_def] >>
  `eval_phis r [] = OK r` by simp[eval_phis_def] >>
  drule_all le_occ_prefix_all_entries_phis_success >>
  disch_then (qspec_then `m` strip_assume_tac) >>
  drule loadElimOccurrenceInversionTheory.le_occ_prefix_phi_semantics >> strip_tac >>
  irule le_actual_prepend_phis_transport >> simp[] >>
  reverse conj_tac >- (qexists_tac `u` >> simp[] >>
    reverse conj_tac >- fs[] >> rpt strip_tac >>
    `MEM j bb.bb_instructions` by (qpat_x_assum `MEM j (le_phi_prefix _)` mp_tac >> rewrite_tac[le_phi_prefix_take] >> disch_then (mp_tac o MATCH_MP rich_listTheory.MEM_TAKE) >> simp[]) >>
    `MEM bb fn.fn_blocks` by metis_tac[livenessTransferProofsTheory.lookup_block_mem] >>
    `MEM v (fn_all_vars fn)` by
      metis_tac[cfgNormBaseTheory.inst_operand_var_in_fn_all_vars] >>
    fs[EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `eval_phis r (_ ++ []) = OK _` mp_tac >>
  pure_rewrite_tac[APPEND_NIL] >>
  disch_then (mp_tac o MATCH_MP le_collected_generated_reads_reserved) >> simp[]
QED
