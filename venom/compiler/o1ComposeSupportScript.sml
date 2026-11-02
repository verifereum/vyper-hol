(*
 * Support lemmas for the O1 composition (o1PipelineCompose): the source
 * unit's shape facts (source_*_shape, o1_source_ctx_shape), what pruning
 * keeps (pruned_member_shape, postorder_pruned_names), and the pre-walk
 * schedule as a stage pair (o1_mapped_pass_stage).
 *)
Theory o1ComposeSupport
Ancestors
  o1PassContract o1ScheduleDecomp o1PartialSchedule o1ScheduleDecompHelpers
  ctxLookupAgree
  venomCompilerWf
  unitShapeDefs fcgPruning venomWf venomInst o1FnScheduleDecomp
  venomPipelineRunner venomPassDispatcher venomFnScheduleRunner
  fcgBridge fcgDefs fcgPostorder fcgAnalysisProps venomPipelineDriver
  venomPassSchedule irSupply pred_set list rich_list

Theorem o1_ctx_shape_wf:
  o1_ctx_shape C ==> ctx_wf C /\ wf_invoke_targets C
Proof
  rw[o1_ctx_shape_def, wf_invoke_targets_def] >>
  gvs[EVERY_MEM, o1_fn_shape_def, fn_invoke_ok_def] >> metis_tac[]
QED

Theorem unit_labels_wf_namespace:
  unit_labels_wf u ==> ALL_DISTINCT (unit_label_namespace u)
Proof
  simp[unit_labels_wf_def]
QED

Theorem entry_fn_first_names:
  C'.ctx_entry = C.ctx_entry /\ ctx_fn_names C' = ctx_fn_names C /\
  entry_fn_first C ==> entry_fn_first C'
Proof
  Cases_on `C.ctx_functions` >> Cases_on `C'.ctx_functions` >>
  simp[entry_fn_first_def, ctx_fn_names_def] >> metis_tac[]
QED

Theorem namespace_filter_distinct:
  !fns. ALL_DISTINCT (FLAT (MAP fn_labels fns)) ==>
        ALL_DISTINCT (FLAT (MAP fn_labels (FILTER P fns)))
Proof
  Induct >> simp[] >> gen_tac >> strip_tac >>
  Cases_on `P h` >> gvs[ALL_DISTINCT_APPEND] >>
  gvs[MEM_FLAT, MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem entry_fn_first_filter:
  entry_fn_first C /\
  (!fn. MEM fn C.ctx_functions /\ C.ctx_entry = SOME fn.fn_name ==> P fn)
  ==> entry_fn_first (C with ctx_functions := FILTER P C.ctx_functions)
Proof
  rw[entry_fn_first_def] >> simp[] >>
  `P fn` by metis_tac[MEM] >> simp[] >> metis_tac[]
QED

Theorem source_member_shape:
  unit_wf u /\ o1_source_unit_ok u /\ unit_first_block_no_phi u /\
  MEM fn u.cu_context.ctx_functions ==>
  wf_function fn /\ fn_inst_wf fn /\ fn_shape_ok fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  fn_invoke_ok (ctx_fn_names u.cu_context) fn
Proof
  rw[unit_wf_def, venom_wf_def, o1_source_unit_ok_def, unit_first_block_no_phi_def,
     unit_shape_ok_def, EVERY_MEM, fn_invoke_ok_def] >>
  gvs[wf_invoke_targets_def] >> metis_tac[]
QED

Theorem source_entry_shape:
  unit_wf u /\ o1_source_unit_ok u /\ unit_entry_no_params u /\
  MEM fn u.cu_context.ctx_functions /\
  u.cu_context.ctx_entry = SOME fn.fn_name ==>
  entry_fn_no_return fn /\ entry_fn_no_params fn
Proof
  strip_tac >>
  `entry_fn_no_params fn` by metis_tac[unit_entry_no_params_def] >>
  `entry_fn_no_ret fn /\
   EVERY (\inst. raw_opcode_ok inst.inst_opcode) (fn_insts fn)` by
    (fs[o1_source_unit_ok_def, unit_shape_ok_def, entry_fn_first_def] >>
     drule unit_wf_distinct_fn_names >>
     simp[ctx_fn_names_def] >> strip_tac >>
     gvs[MEM_MAP, EVERY_MEM] >> metis_tac[]) >>
  simp[entry_fn_no_return_def] >>
  fs[contextCodegenRelTheory.entry_fn_no_ret_def, EVERY_MEM, fn_insts_def,
     fn_insts_blocks_MEM,
     raw_opcode_ok_def] >>
  metis_tac[]
QED

Theorem source_internal_shape:
  o1_source_unit_ok u /\ MEM fn u.cu_context.ctx_functions /\
  u.cu_context.ctx_entry <> SOME fn.fn_name ==>
  EVERY (\inst. ~MEM inst.inst_opcode [STOP; RETURN]) (fn_insts fn)
Proof
  rw[o1_source_unit_ok_def, internal_termination_ok_def,
     unit_shape_ok_def, entry_fn_first_def] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

(* ===== The label, PARAM and PHI facts the source shape implies ===== *)

Theorem bb_well_formed_terminator_last[local]:
  bb_well_formed bb /\ MEM inst bb.bb_instructions /\
  is_terminator inst.inst_opcode ==>
  inst = LAST bb.bb_instructions
Proof
  rw[bb_well_formed_def, MEM_EL] >>
  `n = PRE (LENGTH bb.bb_instructions)` by metis_tac[] >>
  simp[LAST_EL]
QED

(* Outside INVOKE and PHI, a label operand is a jump target or LowerDload's
   "code_end". *)
Theorem label_positions_ok_label[local]:
  label_positions_ok inst /\ MEM (Label l) inst.inst_operands /\
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> PHI ==>
  is_terminator inst.inst_opcode \/ l = "code_end"
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ`
  >- gvs[is_terminator_def] >>
  Cases_on `inst.inst_opcode = ADD`
  >- (gvs[label_positions_ok_def] >> every_case_tac >> gvs[EVERY_MEM] >>
      metis_tac[stackPlanTypesTheory.is_label_operand_def]) >>
  `EVERY (\op. ~is_label_operand op) inst.inst_operands` by
    (qpat_x_assum `label_positions_ok _` mp_tac >>
     simp[label_positions_ok_def] >> Cases_on `inst.inst_opcode` >> gvs[]) >>
  gvs[EVERY_MEM] >> res_tac >> fs[stackPlanTypesTheory.is_label_operand_def]
QED

Theorem source_fn_label_refs_ok[local]:
  wf_function fn /\ EVERY inst_shape_ok (fn_insts fn) /\
  EVERY (\inst. raw_opcode_ok inst.inst_opcode) (fn_insts fn) ==>
  fn_label_refs_ok fn
Proof
  rw[fn_label_refs_ok_def, EVERY_MEM] >>
  `label_positions_ok inst /\ inst.inst_opcode <> PHI` by
    (res_tac >> fs[inst_shape_ok_def, raw_opcode_ok_def]) >>
  drule_all label_positions_ok_label >> strip_tac
  >- (disj1_tac >>
      gvs[fn_insts_def, fn_insts_blocks_MEM, wf_function_def,
          fn_succs_closed_def] >>
      first_x_assum irule >> qexists_tac `bb` >> simp[] >>
      `inst = LAST bb.bb_instructions` by
        metis_tac[bb_well_formed_terminator_last] >>
      Cases_on `bb.bb_instructions` >> gvs[] >>
      simp[bb_succs_def, get_successors_def, MEM_MAP, MEM_FILTER,
           PULL_EXISTS] >>
      qexists_tac `Label l` >> simp[venomStateTheory.get_label_def]) >>
  simp[reserved_label_def]
QED

(* With no PHI, a block whose pseudos form a prefix and that starts with no
   parameter has no parameter at all. *)
Theorem pseudos_prefix_no_params[local]:
  pseudos_prefix bb /\
  EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions /\
  get_params bb.bb_instructions = [] ==>
  EVERY (\i. ~is_param_opcode i.inst_opcode) bb.bb_instructions
Proof
  rw[venomWfTheory.pseudos_prefix_def, EVERY_EL] >> CCONTR_TAC >> fs[] >>
  `is_pseudo (EL 0 bb.bb_instructions).inst_opcode` by
    (Cases_on `n` >> fs[]
     >- (Cases_on `(EL 0 bb.bb_instructions).inst_opcode` >>
         gvs[is_pseudo_def, is_param_opcode_def]) >>
     first_x_assum irule >> qexists_tac `SUC n'` >> simp[] >>
     Cases_on `(EL (SUC n') bb.bb_instructions).inst_opcode` >>
     gvs[is_pseudo_def, is_param_opcode_def]) >>
  `0 < LENGTH bb.bb_instructions` by simp[] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >>
  Cases_on `bb.bb_instructions` >> gvs[stackPlanGenTheory.get_params_def, AllCaseEqs()] >>
  Cases_on `h.inst_opcode` >> gvs[is_pseudo_def, is_param_opcode_def]
QED

Theorem o1_source_unit_extras:
  unit_wf u /\ o1_source_unit_ok u ==>
  unit_label_refs_ok u /\ unit_entry_no_params u /\ unit_first_block_no_phi u
Proof
  strip_tac >>
  `!fn. MEM fn u.cu_context.ctx_functions ==>
        wf_function fn /\ fn_shape_ok fn /\
        EVERY (\inst. raw_opcode_ok inst.inst_opcode) (fn_insts fn)` by
    gvs[unit_wf_def, venom_wf_def, o1_source_unit_ok_def, unit_shape_ok_def,
        EVERY_MEM] >>
  rpt conj_tac
  >- (simp[unit_label_refs_ok_def, EVERY_MEM] >> rpt strip_tac >>
      irule source_fn_label_refs_ok >> gvs[fn_shape_ok_def] >> metis_tac[])
  >- (simp[unit_entry_no_params_def] >> rpt strip_tac >>
      `fn = HD u.cu_context.ctx_functions` by
        (fs[o1_source_unit_ok_def, unit_shape_ok_def, entry_fn_first_def] >>
         drule unit_wf_distinct_fn_names >>
         gvs[ctx_fn_names_def] >> strip_tac >> gvs[MEM_MAP] >>
         metis_tac[]) >>
      first_x_assum drule >>
      fs[o1_source_unit_ok_def, unit_shape_ok_def] >>
      rw[fn_shape_ok_def, wf_function_def, fn_has_entry_def,
         entry_fn_no_params_def] >>
      Cases_on `fn.fn_blocks` >> gvs[fn_insts_def, fn_insts_blocks_def] >>
      gvs[fn_insts_blocks_MEM, EVERY_MEM, callLayoutDefsTheory.no_param_insts_def,
          venomWfTheory.fn_pseudos_prefix_def, raw_opcode_ok_def] >>
      `EVERY (\i. ~is_param_opcode i.inst_opcode) h.bb_instructions` by
        (irule pseudos_prefix_no_params >> gvs[EVERY_MEM] >>
         rpt strip_tac >> res_tac >> fs[]) >>
      gvs[EVERY_MEM] >> metis_tac[]) >>
  simp[unit_first_block_no_phi_def, EVERY_MEM, first_block_no_phi_def] >>
  rpt strip_tac >> first_x_assum drule >>
  rw[wf_function_def, fn_has_entry_def, fn_insts_def, EVERY_MEM,
     raw_opcode_ok_def] >>
  Cases_on `fn.fn_blocks` >> gvs[fn_insts_blocks_def] >> metis_tac[]
QED

Theorem entry_shape_from_members:
  entry_fn_first C /\ EVERY (o1_fn_shape C) C.ctx_functions ==>
  entry_fn_no_ret (HD C.ctx_functions) /\
  get_params (HD (HD C.ctx_functions).fn_blocks).bb_instructions = []
Proof
  rw[entry_fn_first_def] >> gvs[EVERY_DEF, o1_fn_shape_def]
  >- metis_tac[entry_fn_no_return_no_ret] >>
  irule entry_fn_no_params_get_params >> simp[] >>
  gvs[fn_shape_ok_def, fn_entry_label_def, entry_block_def] >>
  Cases_on `fn.fn_blocks` >> gvs[]
QED

Theorem chain_facts_zero:
  LENGTH chains = LENGTH u.cu_context.ctx_functions /\
  (!i. i < LENGTH chains ==> chain_facts rp passes u names chains i) ==>
  stage_ctx u.cu_context chains 0 = u.cu_context
Proof
  strip_tac >> irule stage_ctx_zero >> conj_tac
  >- (qx_gen_tac `i` >> disch_tac >> first_x_assum drule >>
      rewrite_tac[chain_facts_def] >> strip_tac >>
      drule fn_chain_length >> Cases_on `FST (EL i chains)` >> simp[]) >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[chain_facts_def]) >>
  simp[]
QED

Theorem o1_schedule_stages:
  EVERY (o1_step_contract rp) passes /\
  run_named_fn_schedules execute_configured_fn_pass rp passes names u s =
    SOME (u',s') /\
  o1_ctx_shape u.cu_context /\
  ALL_DISTINCT (unit_label_namespace u) /\ ALL_DISTINCT names /\
  (!n. MEM n names <=> MEM n (ctx_fn_names u.cu_context)) /\
  ir_supply_inst_ok s ==>
  unit_labels_wf u' /\ ir_supply_inst_ok s' /\
  ?stage.
    stage 0 = u.cu_context /\ stage (LENGTH passes) = u'.cu_context /\
    (!k. k <= LENGTH passes ==>
      o1_ctx_shape (stage k) /\
      (stage k).ctx_entry = u.cu_context.ctx_entry /\
      (stage k).ctx_global_reserved = u.cu_context.ctx_global_reserved /\
      ctx_fn_names (stage k) = ctx_fn_names u.cu_context) /\
    (!k. k < LENGTH passes ==>
      ctx_pass_stage rp (EL k passes) any_view (stage k) (stage (SUC k)) /\
      (callee_first names u.cu_context.ctx_functions ==>
       ctx_pass_stage rp (EL k passes) (walk_view rp (DROP (SUC k) passes))
         (stage k) (stage (SUC k))))
Proof
  strip_tac >> drule_all run_named_fn_schedules_decomp >> strip_tac >>
  `names <> []` by
    (drule o1_ctx_shape_wf >>
     gvs[ctx_wf_def, ctx_has_entry_def] >> metis_tac[MEM]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[] >>
  qexists_tac `stage_ctx u.cu_context chains` >>
  conj_tac >- (irule chain_facts_zero >> metis_tac[]) >>
  conj_tac >- simp[] >> conj_tac
  >- (rpt strip_tac >>
      drule_all chain_facts_stage_shape >>
      simp[stage_ctx_def]) >>
  qx_gen_tac `k` >> disch_tac >> drule_all chain_facts_stages >> simp[]
QED

Theorem mapped_pass_stage:
  o1_step_contract rp pass /\
  run_mapped_functions rp pass u s = SOME (u',s') /\
  o1_ctx_shape u.cu_context /\ ALL_DISTINCT (unit_label_namespace u) /\
  ir_supply_inst_ok s ==>
  unit_labels_wf u' /\ ir_supply_inst_ok s' /\ o1_ctx_shape u'.cu_context /\
  u'.cu_context.ctx_entry = u.cu_context.ctx_entry /\
  u'.cu_context.ctx_global_reserved = u.cu_context.ctx_global_reserved /\
  ctx_fn_names u'.cu_context = ctx_fn_names u.cu_context /\
  ctx_pass_stage rp pass any_view u.cu_context u'.cu_context
Proof
  strip_tac >>
  `ALL_DISTINCT (ctx_fn_names u.cu_context)` by
    (drule o1_ctx_shape_wf >> simp[ctx_wf_def, ctx_distinct_fn_names_def]) >>
  fs[run_mapped_functions_def] >>
  drule_at (Pos (el 2)) o1_schedule_stages >> simp[] >>
  strip_tac >> gvs[] >>
  first_x_assum (qspec_then `1` mp_tac) >> simp[]
QED

Theorem member_invoke_direct_call:
  ctx_wf C /\ MEM fn C.ctx_functions /\ MEM callee (fn_invoke_targets fn) ==>
  fn_directly_calls C fn.fn_name callee
Proof
  strip_tac >> simp[fn_directly_calls_scan] >> qexists_tac `fn` >>
  gvs[fn_invoke_targets_def] >>
  gvs[ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def] >>
  simp[lookup_function_member_iff]
QED

Theorem pruned_member_shape:
  fcg = fcg_analyze u.cu_context /\ o1_ctx_shape u.cu_context /\
  MEM fn (prune_unit_fcg_unreachable u fcg).cu_context.ctx_functions ==>
  o1_fn_shape (prune_unit_fcg_unreachable u fcg).cu_context fn
Proof
  strip_tac >>
  `ctx_wf u.cu_context /\ wf_invoke_targets u.cu_context` by
    metis_tac[o1_ctx_shape_wf] >>
  drule_all wf_invoke_targets_prune_unit_fcg_unreachable >>
  gvs[wf_invoke_targets_def, o1_ctx_shape_def, EVERY_MEM,
      MEM_prune_unit_fcg_unreachable_functions] >>
  `o1_fn_shape u.cu_context fn` by metis_tac[] >>
  gvs[o1_fn_shape_def, prune_unit_fcg_unreachable_fields, fn_invoke_ok_def] >>
  metis_tac[MEM_prune_unit_fcg_unreachable_functions]
QED

Theorem postorder_pruned_names:
  ctx_wf u.cu_context /\ wf_invoke_targets u.cu_context /\
  u.cu_context.ctx_entry = SOME entry ==>
  (!n. MEM n (fcg_postorder (fcg_analyze u.cu_context) entry) <=>
    MEM n (ctx_fn_names
      (prune_unit_fcg_unreachable u (fcg_analyze u.cu_context)).cu_context))
Proof
  strip_tac >> drule_all fcg_postorder_reachable_set >>
  simp[EXTENSION, ctx_fn_names_def, prune_fcg_unreachable_names, MEM_FILTER,
       GSYM fcg_is_reachable_def] >>
  metis_tac[fcg_analyze_reachable_in_context, ctx_fn_names_def]
QED

Theorem o1_pre_walk_runs:
  run_pipeline_stages rp o1_pipeline_spec.ps_pre_walk_stages u s = SOME (u',s') ==>
  ?mid t. run_mapped_functions rp (CFP_Simple VP_SimplifyCFG) u s = SOME (mid,t) /\
    run_mapped_functions rp (CFP_Simple VP_DretDesugar) mid t = SOME (u',s')
Proof
  simp[o1_pipeline_spec_def, run_pipeline_stages_def, run_pipeline_stage_def] >>
  simp[AllCaseEqs()] >> metis_tac[]
QED

Theorem source_entry_first:
  o1_source_unit_ok u ==> entry_fn_first u.cu_context
Proof
  simp[o1_source_unit_ok_def, unit_shape_ok_def]
QED

Theorem o1_driver_runs:
  run_venom_pipeline mem_ok calling_ok post_ok rp o1_pipeline_spec u = SOME out ==>
  unit_wf u /\ ALL_DISTINCT (unit_label_namespace u) /\
  ?pre t entry t'.
    run_pipeline_stages rp o1_pipeline_spec.ps_pre_walk_stages u (init_ir_supply u) =
      SOME (pre,t) /\
    pre.cu_context.ctx_entry = SOME entry /\
    reachable_fcg_acyclic pre.cu_context (fcg_analyze pre.cu_context) /\
    run_callee_first rp o1_fn_passes (fcg_postorder (fcg_analyze pre.cu_context) entry)
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)) t =
      SOME (out.po_unit,t')
Proof
  simp[run_venom_pipeline_def, o1_pipeline_spec_def,
       run_pipeline_stages_def, run_pipeline_stage_def, LET_THM] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  gvs[unit_wf_def, unit_labels_wf_def] >> metis_tac[]
QED
