Theory fnLineageInvSilentEnvelope
Ancestors fnLineageInvOrdinarySuffix fnPlanLineageSetup fnPlanLineageStages
  fnPlanLineageInventory stackModel list pred_set stackPlanGen venomWf

(* Unlike exact inventory, this interface admits surplus inherited spills. *)
Theorem offset_weak_envelope:
  !inst w lab x ps ops qs m core spillbase before after.
    inst.inst_operands = [Lit w; Label lab] /\ inst.inst_outputs = [x] /\
    generate_offset_plan inst ps = (ops,qs) /\
    lineage_core m core ps /\
    residual_budget_wf spillbase [] (ps with ps_stack := core) /\
    set before = set (FILTER (\v. v <> x) after) /\ MEM x after /\
    set core SUBSET set (MAP Var before) /\
    (!v. MEM v before ==> MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    ~MEM (Var x) core /\ Var x NOTIN FDOM ps.ps_spilled ==>
    lineage_core m (core ++ [Var x]) qs /\
    residual_budget_wf spillbase [] (qs with ps_stack := core ++ [Var x]) /\
    set (core ++ [Var x]) SUBSET set (MAP Var after) /\
    (!v. MEM v after ==> MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) /\
    qs.ps_spilled = ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `qs = FOLDL (\p v. p with ps_stack := stack_push (Var v) p.ps_stack) ps [x]` by
    (drule_all generate_offset_plan_frame >>
     disch_then (qspec_then `ps` assume_tac) >>
     gvs[stack_push_def, SNOC_APPEND]) >>
  `ps.ps_stack = REPLICATE m dead_stack_marker ++ core` by
    gvs[lineage_core_def] >>
  drule output_push_marker_core >>
  disch_then (qspec_then `spillbase` (qspecl_then [`[x]`, `qs`] mp_tac)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `qs = FOLDL _ _ _` kall_tac >>
  fs[] >>
  conj_tac >- simp[lineage_core_def] >>
  conj_tac
  >- (gvs[EXTENSION, SUBSET_DEF, MEM_MAP, MEM_FILTER] >> metis_tac[]) >>
  rpt strip_tac >> Cases_on `v = x` >- simp[] >>
  `MEM v before` by gvs[EXTENSION, MEM_FILTER] >>
  metis_tac[]
QED

Theorem offset_weak_envelope_fresh:
  !inst w lab x ps ops qs core v.
    inst.inst_operands = [Lit w; Label lab] /\ inst.inst_outputs = [x] /\
    generate_offset_plan inst ps = (ops,qs) /\ v <> x /\
    ~MEM (Var v) core /\ Var v NOTIN FDOM ps.ps_spilled ==>
    ~MEM (Var v) (core ++ [Var x]) /\ Var v NOTIN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule_all generate_offset_plan_frame >>
  disch_then (qspec_then `ps` assume_tac) >> gvs[]
QED

Theorem analyzed_offset_live_sets:
  !fn bb k w lab x.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    k < LENGTH bb.bb_instructions /\
    (EL k bb.bb_instructions).inst_opcode = OFFSET /\
    (EL k bb.bb_instructions).inst_operands = [Lit w; Label lab] /\
    (EL k bb.bb_instructions).inst_outputs = [x] ==>
    set (live_vars_at (liveness_analyze fn) bb.bb_label k) =
      set (FILTER (\v. v <> x)
        (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k))) /\
    MEM x (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k))
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def]) >>
  reverse conj_tac
  >- (rewrite_tac[arithmeticTheory.ADD1] >>
      irule fnLineageInvPointLiveTheory.analyzed_offset_output_live_after >>
      simp[] >> metis_tac[]) >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (drule cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
     simp[EXTENSION] >> metis_tac[codegenReadyComputeTheory.fn_reachable_cfg_analyze]) >>
  drule livenessProofsTheory.live_vars_at_transfer >>
  disch_then (qspecl_then [`bb.bb_label`, `bb`, `k`] mp_tac) >>
  simp[livenessDefsTheory.liveness_transfer_def, livenessDefsTheory.live_update_def,
       venomInstTheory.inst_uses_def, venomInstTheory.inst_defs_def,
       livenessDefsTheory.ordered_inst_uses_def, venomInstTheory.python_stack_operands_def,
       venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def,
       venomInstTheory.ir_specific_operand_order_def]
QED
