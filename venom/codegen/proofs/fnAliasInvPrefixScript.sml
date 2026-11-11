Theory fnAliasInvPrefix
Ancestors
  fnAliasInvPhi fnEntryParams fnBlockPlanStaticBodyPrefix fnBlockPlanStaticRegion

(* PARAM residents are self-normalizing, independently of execution state. *)
Theorem lineage_entry_params_alias:
  codegen_ready_fn fn /\ bb = HD fn.fn_blocks /\
  lineage_state (liveness_analyze fn) (dfg_build_function fn) (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth sb ctr) bb.bb_label ps /\
  prepare_params_plan (liveness_analyze fn) fn
    (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) =
    (param_ops,qs) /\
  (if LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) = 1 then
    clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb qs
    else ([],qs)) = (clean_ops,last) ==>
  regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn) sb bb
    (LENGTH (get_params bb.bb_instructions)) last /\
  (!at. MEM at last.ps_stack \/ at IN FDOM last.ps_spilled ==>
    operand_val (frame_view fn ra vs) lo at =
    operand_val (frame_view fn ra vs) lo
      (normalize_operand (dfg_build_function fn) [] at))
Proof
  strip_tac >>
  conj_tac >- (irule regional_entry_lower_start >> metis_tac[]) >>
  `ps = init_cleanup_plan_state ch growth sb ctr` by
    metis_tac[regional_entry_lineage_initial] >>
  `cfg_preds_of (cfg_analyze fn) bb.bb_label = []` by
    metis_tac[regional_entry_no_preds] >>
  gvs[] >>
  drule_all regional_prepare_params_initial_membership >> strip_tac >>
  drule_all regional_prepare_params_initial_spilled >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `MEM at (MAP (\i. Var (HD i.inst_outputs))
    (get_params (HD fn.fn_blocks).bb_instructions))` by gvs[] >>
  metis_tac[entry_param_normalize]
QED

Theorem lineage_entry_no_phi_lower_start:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  lineage_entry (liveness_analyze fn) (dfg_build_function fn) (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth sb ctr) edge lbl ps /\
  collect_phis bb.bb_instructions = [] ==>
  regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn) sb bb 0 ps
Proof
  strip_tac >>
  `bb.bb_label = lbl` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
  simp[regional_body_lower_inv_def] >>
  conj_tac >- metis_tac[fnLineageStaticTheory.lineage_entry_marked] >>
  conj_tac >- (rpt strip_tac >> irule fnLineageStaticTheory.lineage_entry_coverage >>
    goal_assum (drule_at (Pat `lineage_entry _ _ _ _ _ _ _ _`)) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))` by
    (irule fnLineageStaticTheory.lineage_entry_non_phi_fresh >>
     goal_assum (drule_at (Pat `lineage_entry _ _ _ _ _ _ _ _`)) >> simp[] >>
     metis_tac[]) >>
  gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  metis_tac[listTheory.MEM_EL]
QED

Theorem no_phi_clean_lower_inv:
  collect_phis bb.bb_instructions = [] /\
  regional_body_lower_inv lv dfg sb bb 0 ps /\
  clean_stack_plan lv cfg fn bb ps = (ops,qs) ==>
  regional_body_lower_inv lv dfg sb bb 0 qs
Proof
  strip_tac >>
  `generated_plan_state_wf_marked sb ps` by
    metis_tac[regional_body_lower_inv_wf] >>
  simp[regional_body_lower_inv_def] >>
  conj_tac >- metis_tac[regional_clean_stack_marked_wf] >>
  conj_tac
  >- (rpt strip_tac >> irule regional_clean_stack_protected_ownership >>
      goal_assum (drule_at (Pat `clean_stack_plan _ _ _ _ _ = _`)) >>
      qexists_tac `sb` >> simp[livenessDefsTheory.input_vars_from_def] >>
      gvs[regional_body_lower_inv_def]) >>
  `!op. MEM op qs.ps_stack \/ op IN FDOM qs.ps_spilled ==>
    !j v. j < LENGTH bb.bb_instructions /\
    (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
    ~MEM v (EL j bb.bb_instructions).inst_outputs` suffices_by metis_tac[] >>
  ho_match_mp_tac regional_clean_stack_identity_predicate >>
  goal_assum (drule_at (Pat `clean_stack_plan _ _ _ _ _ = _`)) >>
  simp[stackPlanGenTheory.dead_stack_marker_def, dfgDefsTheory.normalize_operand_def] >>
  gvs[regional_body_lower_inv_def] >> metis_tac[]
QED

Theorem lineage_no_phi_preparation_alias:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  lineage_entry (liveness_analyze fn) (dfg_build_function fn) (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth sb ctr) edge lbl ps /\
  collect_phis bb.bb_instructions = [] /\
  (if LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) = 1 then
    clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb
      (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>)
    else ([],ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>)) =
    (ops,qs) /\
  (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
    operand_val (frame_view fn ra vs) lo at =
    operand_val (frame_view fn ra vs) lo
      (normalize_operand (dfg_build_function fn) [] at)) ==>
  regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn) sb bb 0 qs /\
  (!at. MEM at qs.ps_stack \/ at IN FDOM qs.ps_spilled ==>
    operand_val (frame_view fn ra vs) lo at =
    operand_val (frame_view fn ra vs) lo
      (normalize_operand (dfg_build_function fn) [] at))
Proof
  strip_tac >>
  `regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn) sb bb 0 ps` by
    (irule lineage_entry_no_phi_lower_start >> metis_tac[]) >>
  `regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn) sb bb 0
    (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>)` by
    (gvs[regional_body_lower_inv_def, fnPlanPrefixTheory.wf_marked_cleanup_fields] >>
     metis_tac[]) >>
  Cases_on `LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) = 1` >> gvs[]
  >- (conj_tac >- (irule no_phi_clean_lower_inv >> metis_tac[]) >>
      ho_match_mp_tac (Q.INST
        [`ps` |-> `ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>`,
         `lv` |-> `liveness_analyze fn`, `cfg` |-> `cfg_analyze fn`]
        regional_clean_stack_identity_predicate) >>
      simp[stackPlanGenTheory.dead_stack_marker_def, dfgDefsTheory.normalize_operand_def] >>
      metis_tac[regional_body_lower_inv_wf]) >>
  metis_tac[]
QED
