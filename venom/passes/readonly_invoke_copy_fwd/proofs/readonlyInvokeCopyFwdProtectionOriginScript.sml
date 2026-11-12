(* Backward SSA availability for the static roots of forwarding events. *)
Theory readonlyInvokeCopyFwdProtectionOrigin
Ancestors
  ssaAvailablePred internalReturnCopyFwdPlan list venomInst
  readonlyInvokeCopyFwdOccurrenceAlias readonlyInvokeCopyFwdProtection
  invokeCopyFwdCommonDefs readonlyInvokeCopyFwdDefs finite_map words
  venomWfProps venomExecSemantics readonlyInvokeCopyFwdPlan
  o1LowerDloadOccurrence internalReturnCopyFwdAlias venomInstProps venomExecProofs
  ptrDiscipline venomState arithmetic

Theorem ircf_alias_boundary_available_root:
  !fn root v. ircf_alias fn root v ==>
  !bb n. wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
    MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    n <= LENGTH bb.bb_instructions /\
    (!P. boundary_pred fn bb n P ==> P v) ==>
    (!P. boundary_pred fn bb n P ==> P root)
Proof
  ho_match_mp_tac ircf_alias_ind >> conj_tac
  >- simp[] >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `!P. boundary_pred fn bb n P ==> P v` by
    (`inst.inst_opcode <> PHI /\ MEM v' inst.inst_outputs` by
       (qpat_assum `inst.inst_opcode = _` (fn th => rewrite_tac[th]) >>
        qpat_assum `inst.inst_outputs = _` (fn th => rewrite_tac[th]) >>
        simp[NoAsms]) >>
     metis_tac[boundary_pred_definition_input_available]) >>
  metis_tac[]
QED

(* Static witnesses are extracted only against the DFG of this exact function. *)
Theorem ricf_event_alloca_witnesses:
  ricf_event_ok e bb /\ e.rfe_ctx.icf_dfg = dfg_build_function fn /\
  MEM bb fn.fn_blocks /\ fn_inst_wf fn /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn ==>
  ?dst sv dr sr sz da sa.
    (ricf_event_copy e bb).inst_operands = [Var dst;Var sv;Lit sz] /\
    ricf_event_roots e bb = SOME (dr,Var sr,Lit sz) /\
    MEM da (fn_insts fn) /\ da.inst_opcode = ALLOCA /\
    da.inst_outputs = [dr] /\ da.inst_operands = [Lit sz] /\
    MEM sa (fn_insts fn) /\ sa.inst_opcode = ALLOCA /\
    sa.inst_outputs = [sr] /\ sa.inst_operands = [Lit sz] /\
    ircf_alias fn dr dst /\ ircf_alias fn sr sv
Proof
  strip_tac >> drule ricf_event_copy_shape >> strip_tac >>
  `MEM (ricf_event_copy e bb) bb.bb_instructions` by
    metis_tac[ricf_event_copy_def, EL_MEM] >>
  `?di. dfg_get_def (dfg_build_function fn)
    (icf_assign_root (dfg_build_function fn) {} dst) = SOME di /\
    icf_is_alloca di` by
    (qpat_x_assum `ricf_event_ok _ _` mp_tac >>
     simp[ricf_event_ok_def, ricf_try_forward_def] >>
     gvs[AllCaseEqs(), ricf_event_copy_def, icf_is_alloca_def] >> metis_tac[]) >>
  `?sv si. src = Var sv /\
    dfg_get_def (dfg_build_function fn) sv = SOME si /\ icf_is_alloca si` by
    (fs[ricf_src_alloca_def] >> metis_tac[ricf_event_copy_def]) >>
  `?z. sz = Lit z /\ icf_matches_alloca_size di z` by
    (fs[ricf_full_alloca_copies_def] >> metis_tac[]) >>
  gvs[] >>
  `icf_assign_root (dfg_build_function fn) {} sv = sv` by
    (simp[Once icf_assign_root_def, icf_is_alloca_def] >>
     fs[icf_is_alloca_def]) >>
  `icf_matches_alloca_size si z` by
    (fs[ricf_full_alloca_copies_def] >>
     qpat_x_assum `!bb copy_inst dst src_op size_op. _`
       (qspecl_then [`bb`,`ricf_event_copy e bb`,`dst`,`Var sv`,`Lit z`] mp_tac) >>
     simp[icf_assign_root_op_def] >> metis_tac[]) >>
  `ircf_alloca_of fn (icf_assign_root (dfg_build_function fn) {} dst) z /\
   ircf_alloca_of fn sv z` by metis_tac[ircf_alloca_of_dfg] >>
  fs[ircf_alloca_of_def] >>
  simp[ricf_event_roots_def, icf_assign_root_op_def] >>
  metis_tac[ircf_assign_root_alias, ircf_alias_refl]
QED

Theorem ricf_actual_copy_origin:
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  occ_frame_reachable vs C stk PG G tn fn (ricf_event_copy e bb) s n a U B HP H /\
  ricf_event_ok e bb /\ e.rfe_ctx.icf_dfg = dfg_build_function fn /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx = e.rfe_index /\
  step_inst fuel C (ricf_event_copy e bb) s = OK t ==>
  ?p. p.rpe_event = e /\ p.rpe_block = bb /\ p.rpe_fn = fn /\
    p.rpe_before = s /\ p.rpe_after = t /\ p.rpe_owner = a /\
    ricf_protection_origin vs C p stk PG G tn
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  drule occurrence_alias_reachable >> simp[] >> strip_tac >>
  drule_all ricf_event_alloca_witnesses >> strip_tac >>
  `e.rfe_index < LENGTH bb.bb_instructions /\
   (ricf_event_copy e bb).inst_opcode = MCOPY` by
    metis_tac[ricf_event_copy_shape] >>
  `frame_reachable vs C stk PG G tn fn (ricf_event_copy e bb) s` by
    metis_tac[occ_frame_reachable_projection] >>
  `ircf_alias_site_value fn s G dst /\ ircf_alias_site_value fn s G sv` by
    (conj_tac >> irule ircf_alias_reachable_operand >>
     goal_assum (drule_at Any) >> simp[] >>
     drule ricf_event_copy_shape >> simp[]) >>
  `?db. lookup_var dst s = SOME (n2w db) /\
    FLOOKUP s.vs_allocas da.inst_id = SOME (db,w2n sz)` by
    metis_tac[ircf_alias_site_value_def] >>
  `?sb. lookup_var sv s = SOME (n2w sb) /\
    FLOOKUP s.vs_allocas sa.inst_id = SOME (sb,w2n sz)` by
    metis_tac[ircf_alias_site_value_def] >>
  `FLOOKUP H dst = SOME (a,da.inst_id) /\
   FLOOKUP H sv = SOME (a,sa.inst_id)` by
    (`MEM (Var dst) (ricf_event_copy e bb).inst_operands /\
      MEM (Var sv) (ricf_event_copy e bb).inst_operands` by simp[] >>
     `(ricf_event_copy e bb).inst_opcode <> PHI` by simp[] >>
     metis_tac[occurrence_alias_reachable_operand]) >>
  `(!P. boundary_pred fn bb s.vs_inst_idx P ==> P dst) /\
   (!P. boundary_pred fn bb s.vs_inst_idx P ==> P sv)` by
    (conj_tac >> rpt strip_tac >> irule boundary_pred_operand >>
     goal_assum (drule_at Any) >>
     simp[GSYM ricf_event_copy_def] >> metis_tac[]) >>
  `fn_reachable fn bb.bb_label` by
    fs[occurrence_alias_boundary_def] >>
  `(!P. boundary_pred fn bb s.vs_inst_idx P ==> P dr) /\
   (!P. boundary_pred fn bb s.vs_inst_idx P ==> P sr)` by
    metis_tac[ircf_alias_boundary_available_root, LESS_IMP_LESS_OR_EQ] >>
  `FLOOKUP H dr = SOME (a,da.inst_id) /\
   FLOOKUP H sr = SOME (a,sa.inst_id)` by
    metis_tac[occurrence_alias_reachable_available, ircf_alias_refl] >>
  `FLOOKUP B (a,da.inst_id) = SOME (db,w2n sz) /\
   FLOOKUP B (a,sa.inst_id) = SOME (sb,w2n sz)` by
    metis_tac[occ_frame_reachable_annotation, occurrence_annotation_ok_def,
              occurrence_allocas_ok_def] >>
  rpt (qpat_x_assum `!P. boundary_pred _ _ _ P ==> _` kall_tac) >>
  qexists_tac `<| rpe_event := e; rpe_block := bb; rpe_fn := fn;
    rpe_before := s; rpe_after := t; rpe_owner := a;
    rpe_dst := (a,da.inst_id); rpe_src := (a,sa.inst_id);
    rpe_db := db; rpe_sb := sb; rpe_size := w2n sz |>` >>
  simp[ricf_protection_origin_def] >>
  qexistsl_tac [`n`,`U`,`B`,`HP`,`H`] >>
  simp[op_prov_def, eval_operands_def, eval_operand_def] >> metis_tac[]
QED
