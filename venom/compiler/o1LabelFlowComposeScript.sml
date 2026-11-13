Theory o1LabelFlowCompose
Ancestors
  o1LabelFlowSource o1LabelFlowMiddle o1LabelFlowLateContracts
  o1PipelineCorrect o1PipelineCompose o1ScheduleDecomp
  o1PartialSchedule o1FnScheduleDecompHelpers o1ComposeSupport
  venomPassSchedule list irSupply venomPipelineRunner fcgPruning
  codegenSymRel o1LabelFlowSourceBoundary o1LabelFlowSourceSsaStep
  o1LabelFlowLowerDload o1LabelFlowMiddleConcretize o1LabelFlowMiddleFmp venomInst
  concretizeMemLocDefs venomPassDispatcher o1PassContract lowerDloadMakeSsaInput
  o1ContractMakeSsaReplay o1LabelFlowMiddleSsaAssembly unitShapeDefs
  o1LabelFlowSourcePreWalk
  venomFnScheduleRunnerProps o1LabelFlowStaticContracts

(* A named runner invariant avoids repeating the three phase boundaries in
   every contract. It adds no assumptions to the source or pass contracts. *)
Definition label_flow_row_extra_def:
  label_flow_row_extra ctx k f <=>
    label_flow_ok (ctx with ctx_functions := [f]) /\
    (k <= 1 ==> !i. MEM i (fn_insts f) ==>
      ~MEM (Label "code_end") i.inst_operands) /\
    (2 <= k /\ k <= 4 ==> middle_code_end_lifetime f)
End

Theorem label_flow_singleton_context[local]:
  label_flow_ok (C with ctx_functions := [f]) <=>
  label_flow_ok (D with ctx_functions := [f])
Proof
  simp[label_flow_ok_def]
QED

Theorem rows_step_contract_enrich_invariant[local]:
  rows_step_contract o1_fn_row k rp pass /\
  (!observed s f out.
    fn_pass_step rp pass observed s f out /\
    o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
    EVERY fmp_sig_no_param observed.cu_context.ctx_functions /\
    o1_fn_row k f /\ P k f ==> P (SUC k) out.fpo_function) ==>
  rows_step_contract (\j f. o1_fn_row j f /\ P j f) k rp pass
Proof
  rewrite_tac[rows_step_contract_def] >> rpt strip_tac >>
  `EVERY (\g. ?j. o1_fn_row j g) observed.cu_context.ctx_functions` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  `EVERY fmp_sig_no_param observed.cu_context.ctx_functions` by
    (fs[EVERY_MEM, o1_fn_row_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem compose_first_ssa[local]:
  fn_pass_step rp (CFP_Simple VP_MakeSSA) observed s f out /\
  o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
  o1_fn_row 0 f /\ label_flow_row_extra ctx 0 f ==>
  label_flow_row_extra ctx 1 out.fpo_function
Proof
  simp[label_flow_row_extra_def] >> strip_tac >>
  `!i. MEM i (fn_insts f) ==> i.inst_opcode <> CODESIZE /\
    (i.inst_opcode = CODECOPY ==>
      ?dst sz. i.inst_operands = [dst; Label "runtime_begin"; sz])` by
    metis_tac[label_flow_ok_seed_free_function] >>
  drule_all first_make_ssa_step_seed_free_flow >> strip_tac >>
  metis_tac[label_flow_ok_seed_free_function]
QED

Theorem compose_lower_dload[local]:
  fn_pass_step rp (CFP_Simple VP_LowerDload) observed s f out /\
  label_flow_row_extra ctx 1 f ==>
  label_flow_row_extra ctx 2 out.fpo_function
Proof
  simp[label_flow_row_extra_def] >> strip_tac >>
  drule lower_dload_step_supply >> strip_tac >> conj_tac
  >- (irule lower_dload_function_label_flow_ok >> metis_tac[]) >>
  rewrite_tac[middle_code_end_lifetime_def] >> rpt strip_tac >>
  irule lower_dload_function_code_end_lifetime >> metis_tac[]
QED

Theorem compose_concretize[local]:
  fn_pass_step rp (CFP_Simple VP_ConcretizeMemLoc) observed s f out /\
  label_flow_row_extra ctx 2 f ==>
  label_flow_row_extra ctx 3 out.fpo_function
Proof
  simp[label_flow_row_extra_def] >> strip_tac >>
  `execute_configured_fn_pass rp (CFP_Simple VP_ConcretizeMemLoc)
    observed s f = SOME out` by fs[fn_pass_step_def] >>
  gvs[execute_configured_fn_pass_concretize, AllCaseEqs()] >>
  gvs[concretize_function_fuel_in_context_def, AllCaseEqs()] >>
  `label_flow_ok (ctx with ctx_functions :=
    [concretize_function_with_positions layout.cl_positions f]) /\
   middle_code_end_lifetime
    (concretize_function_with_positions layout.cl_positions f)` by
    (conj_tac >- metis_tac[concretize_label_flow] >>
     drule (PURE_REWRITE_RULE [GSYM middle_code_end_lifetime_def]
       concretize_function_code_end_lifetime) >> simp[]) >>
  gvs[apply_context_concretize_layout_def, apply_concretize_layout_def] >>
  qmatch_goalsub_abbrev_tac `middle_code_end_lifetime g` >>
  `g.fn_blocks =
    (concretize_function_with_positions layout.cl_positions f).fn_blocks` by
    simp[Abbr `g`] >>
  `!x. code_end_var g x <=>
    code_end_var (concretize_function_with_positions layout.cl_positions f) x` by
    metis_tac[code_end_var_same_blocks] >>
  (conj_tac >- metis_tac[label_flow_ok_same_blocks] >>
   fs[middle_code_end_lifetime_def, fn_insts_def])
QED

Theorem compose_fmp[local]:
  fn_pass_step rp (CFP_Simple VP_FmpLowering) observed s f out /\
  EVERY fmp_sig_no_param observed.cu_context.ctx_functions /\
  o1_fn_row 3 f /\ label_flow_row_extra ctx 3 f ==>
  label_flow_row_extra ctx 4 out.fpo_function
Proof
  simp[label_flow_row_extra_def] >> strip_tac >> conj_tac
  >- metis_tac[fmp_row_label_flow_ok] >>
  irule (PURE_REWRITE_RULE [GSYM middle_code_end_lifetime_def]
    fmp_row_code_end_lifetime) >> metis_tac[]
QED

Theorem compose_second_ssa[local]:
  fn_pass_step rp (CFP_Simple VP_MakeSSA) observed s f out /\
  o1_ctx_shape observed.cu_context /\
  o1_fn_row 4 f /\ label_flow_row_extra ctx 4 f ==>
  label_flow_row_extra ctx 5 out.fpo_function
Proof
  simp[label_flow_row_extra_def] >> strip_tac >>
  `MEM f observed.cu_context.ctx_functions` by
    metis_tac[fn_pass_step_def, lookup_unique_function_member] >>
  `wf_function f /\ fn_inst_wf f /\ make_ssa_input_ok f` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, o1_fn_row_def, EVERY_MEM,
        fn_shape_ok_def] >> metis_tac[]) >>
  drule make_ssa_pass_step_replay >> strip_tac >>
  irule make_ssa_current_fn_label_flow >> goal_assum $ drule_at Any >>
  fs[middle_code_end_lifetime_def]
QED

Theorem compose_late[local]:
  ((k = 5 /\ pass = CFP_Simple VP_SimplifyCFG) \/
   (k = 6 /\ pass = CFP_Simple VP_SingleUseExpansion) \/
   (k = 7 /\ pass = CFP_Simple VP_DFT) \/
   (k = 8 /\ pass = CFP_Simple VP_CFGNormalization)) /\
  fn_pass_step rp pass observed s f out /\
  o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
  o1_fn_row k f /\ label_flow_row_extra ctx k f ==>
  label_flow_row_extra ctx (SUC k) out.fpo_function
Proof
  strip_tac >>
  `label_flow_ok (observed.cu_context with ctx_functions := [f])` by
    metis_tac[label_flow_row_extra_def, label_flow_singleton_context] >>
  `label_flow_ok (observed.cu_context with ctx_functions := [out.fpo_function])` by
    metis_tac[o1_late_row_label_flow_ok] >>
  gvs[label_flow_row_extra_def] >>
  metis_tac[label_flow_singleton_context]
QED

Theorem o1_label_flow_enriched_contracts:
  rows_step_contracts_from
    (\k f. o1_fn_row k f /\ label_flow_row_extra ctx k f)
    rp 0 o1_fn_passes
Proof
  mp_tac (Q.SPEC `rp` (GEN_ALL o1_label_flow_static_steps)) >>
  disch_then (mp_tac o MATCH_MP o1_step_contracts_from_rows) >>
  rewrite_tac[o1_fn_passes_def, rows_step_contracts_from_def] >> strip_tac >>
  rpt conj_tac >> irule rows_step_contract_enrich_invariant >> simp[]
  >- metis_tac[compose_first_ssa]
  >- metis_tac[compose_lower_dload]
  >- metis_tac[compose_concretize]
  >- metis_tac[compose_fmp]
  >- metis_tac[compose_second_ssa] >>
  rpt strip_tac
  >- (irule (SRULE [] (Q.INST [`k` |-> `5`] compose_late)) >> metis_tac[])
  >- (irule (SRULE [] (Q.INST [`k` |-> `6`] compose_late)) >> metis_tac[])
  >- (irule (SRULE [] (Q.INST [`k` |-> `7`] compose_late)) >> metis_tac[]) >>
  irule (SRULE [] (Q.INST [`k` |-> `8`] compose_late)) >> metis_tac[]
QED

Theorem o1_label_flow_walk:
  run_named_fn_schedules execute_configured_fn_pass rp o1_fn_passes names u s =
    SOME (u',s') /\ o1_ctx_shape u.cu_context /\
  ALL_DISTINCT (unit_label_namespace u) /\ ALL_DISTINCT names /\
  (!n. MEM n names <=> MEM n (ctx_fn_names u.cu_context)) /\
  ir_supply_inst_ok s /\ EVERY (o1_fn_row 0) u.cu_context.ctx_functions /\
  (!f i. MEM f u.cu_context.ctx_functions /\ MEM i (fn_insts f) ==>
    ~MEM (Label "code_end") i.inst_operands /\ i.inst_opcode <> CODESIZE /\
    (i.inst_opcode = CODECOPY ==>
     ?dst sz. i.inst_operands = [dst; Label "runtime_begin"; sz])) ==>
  label_flow_ok u'.cu_context
Proof
  strip_tac >>
  mp_tac (Q.INST [`ctx` |-> `u.cu_context`] o1_label_flow_enriched_contracts) >>
  disch_tac >>
  drule_at (Pos (el 1)) run_named_fn_schedules_decomp >>
  disch_then (drule_at (Pat `run_named_fn_schedules _ _ _ _ _ _ = _`)) >>
  impl_tac
  >- (simp[label_flow_row_extra_def, EVERY_MEM] >> rpt strip_tac
      >- fs[EVERY_MEM]
      >- (irule (iffRL label_flow_ok_seed_free_function) >> metis_tac[])
      >> metis_tac[]) >>
  disch_then (qx_choose_then `chains` strip_assume_tac) >>
  `!i. i < LENGTH chains ==>
    label_flow_ok (u.cu_context with ctx_functions :=
      [EL (LENGTH o1_fn_passes) (FST (EL i chains))])` by
    (rpt strip_tac >>
     qpat_x_assum `!i. i < LENGTH chains ==> chain_facts _ _ _ _ _ _ _`
       (qspec_then `i` mp_tac) >> impl_tac >- simp[] >> strip_tac >>
     drule_at (Pos (el 1)) chain_facts_row >>
     disch_then (qspec_then `LENGTH o1_fn_passes` mp_tac) >>
     simp[label_flow_row_extra_def]) >>
  gvs[stage_ctx_def, stage_fns_def, label_flow_ok_def, MEM_MAP] >>
  metis_tac[MEM_EL]
QED

Theorem o1_pipeline_label_flow_preserved:
  !rpolicy unit out.
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  label_flow_ok unit.cu_context /\
  (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
             ~MEM (Label "code_end") inst.inst_operands) ==>
  label_flow_ok out.po_unit.cu_context
Proof
  rpt strip_tac >> fs[o1_pipeline_def] >>
  drule o1_driver_runs >> strip_tac >>
  `o1_ctx_shape unit.cu_context` by metis_tac[o1_source_unit_ok_ctx_shape] >>
  `ir_supply_inst_ok (init_ir_supply unit)` by simp[init_ir_supply_inst_ok] >>
  drule_all o1_pre_walk_rows >> strip_tac >>
  drule o1_pre_walk_seed_free_flow >> simp[] >> disch_tac >>
  drule_all o1_pre_walk_sim >> strip_tac >>
  `unit.cu_context.ctx_entry = SOME entry` by metis_tac[] >>
  mp_tac (Q.INST [`unit` |-> `pre`, `fcg` |-> `fcg_analyze pre.cu_context`]
    o1_walk_callee_first) >> simp[] >> strip_tac >>
  drule unit_labels_wf_namespace >> strip_tac >>
  `o1_ctx_shape (prune_unit_fcg_unreachable pre
     (fcg_analyze pre.cu_context)).cu_context /\
   ALL_DISTINCT (unit_label_namespace
     (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)))` by
    metis_tac[o1_ctx_shape_prune] >>
  fs[run_callee_first_def] >>
  drule o1_label_flow_walk >> impl_tac
  >- (simp[o1_prune_every] >>
      metis_tac[MEM_prune_unit_fcg_unreachable_functions]) >>
  simp[]
QED

(* Audit publication at the kernel boundary, including imported runner facts.
   DISK_THM is HOL's ordinary persisted-theorem marker, not an admission. *)
val _ = List.app (fn (n, th) =>
  let val (ors, axs) = Tag.dest_tag (Thm.tag th)
      val bad = List.filter (fn s => s <> "DISK_THM") ors @ axs
  in print ("LABEL_FLOW_AUDIT " ^ n ^ ": " ^
       String.concatWith "," (ors @ axs) ^ "\n");
     if null bad then () else raise Fail ("oracle dependency: " ^ n)
  end)
  [("static_steps", o1_label_flow_static_steps),
   ("enriched_contracts", o1_label_flow_enriched_contracts),
   ("walk", o1_label_flow_walk),
   ("pipeline", o1_pipeline_label_flow_preserved),
   ("first_ssa", first_make_ssa_step_seed_free_flow),
   ("lower_dload_flow", lower_dload_function_label_flow_ok),
   ("lower_dload_lifetime", lower_dload_function_code_end_lifetime),
   ("concretize_flow", concretize_label_flow),
   ("concretize_lifetime", concretize_function_code_end_lifetime),
   ("fmp_flow", fmp_row_label_flow_ok),
   ("fmp_lifetime", fmp_row_code_end_lifetime),
   ("ssa_replay", make_ssa_pass_step_replay),
   ("second_ssa", make_ssa_current_fn_label_flow),
   ("late", o1_late_row_label_flow_ok),
   ("driver", o1_driver_runs),
   ("pre_rows", o1_pre_walk_rows),
   ("pre_flow", o1_pre_walk_seed_free_flow),
   ("pre_sim", o1_pre_walk_sim),
   ("walk_order", o1_walk_callee_first),
   ("prune_shape", o1_ctx_shape_prune),
   ("runner", run_named_fn_schedules_decomp)];
