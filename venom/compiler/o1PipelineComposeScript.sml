(*
 * The O1 pipeline from its per-pass contracts.
 *
 * run_venom_pipeline is two pre-walk schedules (SimplifyCFG, DretDesugar
 * over every function), the pruning of unreachable functions, and the
 * callee-first walk of o1_fn_passes.  Each schedule decomposes into stage
 * contexts (o1ScheduleDecomp); each consecutive pair is one contract
 * theorem's instance (o1PassContract); pruning is a context agreement
 * (ctxLookupAgree).  Composing them gives o1_pipeline_stage_facts: the
 * output context's shape, a forward simulation up to any well-formed set
 * of dead bytes (dead_wf) from every initial state that satisfies the raw
 * memory invariant, and the lowered memory
 * invariant of the output.  o1PipelineCorrect states S4 and S6 from it.
 *
 * The DFT gas contract chooses an input oracle for each output oracle.
 * Composition chooses these inputs backwards, then propagates invariants
 * forwards under the chosen source input's invariant guard.
 *)
Theory o1PipelineCompose
Ancestors
  o1ComposeSupport o1PassContract o1ContractTheorems o1ScheduleDecomp
  dftContractGas o1DftStageSim o1DftStageSsa
  o1FnScheduleDecompHelpers o1DretDesugarContract o1ContractSimplifyCfg
  ctxLookupAgree ptrDiscipline ptrDisciplineAgree unitMemInv
  unitTransformDefs unitShapeDefs venomPipelineDriver venomPipelineRunner
  venomPipelineRunnerProps venomPassDispatcherProps venomFnScheduleRunner venomPassSchedule
  venomPassDispatcher venomCompilerWf venomWf venomInst venomExecSemantics
  venomState stateEquivProps fcgDefs fcgPruning fcgPostorder
  fcgAnalysisProps fcgBridge contextCodegenRel venomMemDefs list rich_list

(* ===== Simulations compose ===== *)

Theorem ctx_sim_trans:
  dead_wf D /\ ctx_sim D C1 C2 s1 s2 /\ ctx_sim D C2 C3 s2 s3 ==>
  ctx_sim D C1 C3 s1 s3
Proof
  rw[ctx_sim_def] >> first_x_assum drule >> strip_tac >>
  `terminates (run_context fuel' C2 s2)` by
    metis_tac[dead_result_rel_terminates] >>
  first_x_assum drule >> strip_tac >>
  metis_tac[dead_result_rel_trans]
QED

Theorem guarded_ctx_sim_trans:
  dead_wf D /\
  (!b. o1_run_state_ok b ==>
    ?a. gas_variant a b /\
      (Inv A a ==> ctx_sim D A B a b /\ Mid B b)) /\
  (!c. o1_run_state_ok c ==>
    ?b. gas_variant b c /\
      (Mid B b ==> ctx_sim D B C b c /\ Post C c)) /\
  o1_run_state_ok c ==>
  ?a. gas_variant a c /\
    (Inv A a ==> ctx_sim D A C a c /\ Post C c)
Proof
  strip_tac >>
  qpat_x_assum `!c. _` (qspec_then `c` mp_tac) >>
  simp[] >> strip_tac >>
  `o1_run_state_ok b` by metis_tac[gas_variant_run_state_ok] >>
  qpat_x_assum `!b. _` (qspec_then `b` mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `a` >> conj_tac
  >- metis_tac[gas_variant_trans] >>
  strip_tac >> metis_tac[ctx_sim_trans]
QED

Theorem ctx_sim_run_context_eq:
  ctx_sim D C1 C2 s s /\
  (!fuel. run_context fuel C2 s = run_context fuel C3 s)
  ==> ctx_sim D C1 C3 s s
Proof
  simp[ctx_sim_def] >> metis_tac[]
QED

(* ===== The raw memory fact ignores the context ===== *)

(* raw_mem_ok is not range-wise (its revert-forward exemption reads the
   current block), but it does not read the context. *)
Theorem raw_mem_ok_ctx_free:
  raw_mem_ok ctx fn inst s ==> raw_mem_ok ctx' fn inst s
Proof
  simp[raw_mem_ok_def]
QED

Theorem dload_offset_ok_ctx_free:
  dload_offset_ok ctx fn inst s ==> dload_offset_ok ctx' fn inst s
Proof
  simp[lowerDloadDefsTheory.dload_offset_ok_def]
QED

(* Pruning drops functions, so it keeps the DLOAD headroom bound. *)
Theorem ctx_dload_count_prune:
  ctx_dload_count (prune_unit_fcg_unreachable unit fcg).cu_context <=
  ctx_dload_count unit.cu_context
Proof
  simp[prune_unit_fcg_unreachable_def,
       lowerDloadDefsTheory.ctx_dload_count_def] >>
  qspec_tac (`unit.cu_context.ctx_functions`, `fns`) >>
  Induct >> rw[]
QED

Theorem dload_headroom_ok_prune:
  dload_headroom_ok unit.cu_context fn inst s ==>
  dload_headroom_ok (prune_unit_fcg_unreachable unit fcg).cu_context fn inst s
Proof
  simp[lowerDloadDefsTheory.dload_headroom_ok_def] >>
  mp_tac ctx_dload_count_prune >> decide_tac
QED

Theorem o1_fn_passes_steps:
  o1_step_contracts_from rp 0 o1_fn_passes
Proof
  simp[o1_fn_passes_def, o1_step_contracts_from_def,
       o1_contract_make_ssa_1, o1_contract_lower_dload,
       o1_contract_concretize_mem_loc, o1_contract_fmp_lowering,
       o1_contract_make_ssa_2, o1_contract_simplify_cfg, o1_contract_sue,
       o1_contract_dft, o1_contract_cfg_normalization]
QED

Theorem o1_run_contracts_same_gas:
  k < LENGTH o1_fn_passes /\ k <> 7 ==> o1_run_contract rp D k
Proof
  strip_tac >> fs[o1_fn_passes_def] >>
  `k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/
   k = 8` by decide_tac >>
  gvs[o1_contract_make_ssa_1, o1_contract_lower_dload,
      o1_contract_concretize_mem_loc, o1_contract_fmp_lowering,
      o1_contract_make_ssa_2, o1_contract_simplify_cfg, o1_contract_sue,
      o1_contract_cfg_normalization]
QED

Theorem o1_run_contracts:
  k < LENGTH o1_fn_passes ==> o1_run_contract_gas rp D k
Proof
  strip_tac >>
  `o1_run_contract rp D k \/ o1_run_contract_gas rp D k` suffices_by
    metis_tac[o1_run_contract_def, o1_run_contract_gas_def,
              o1_stage_contract_imp_gas] >>
  fs[o1_fn_passes_def] >>
  `k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/
   k = 8` by decide_tac >>
  gvs[o1_contract_make_ssa_1, o1_contract_lower_dload,
      o1_contract_concretize_mem_loc, o1_contract_fmp_lowering,
      o1_contract_make_ssa_2, o1_contract_simplify_cfg, o1_contract_sue,
      o1_contract_cfg_normalization] >>
  disj2_tac >> mp_tac (Q.INST [`rpolicy` |-> `rp`] o1_contract_dft) >>
  simp[o1_run_contract_gas_def]
QED

(* ===== Source shape ===== *)

Theorem raw_opcode_ok_not_raw_fmp[local]:
  raw_opcode_ok op ==> ~is_raw_fmp_opcode op
Proof
  Cases_on `op` >> simp[raw_opcode_ok_def, is_raw_fmp_opcode_def]
QED

Theorem source_no_raw_fmp_ops:
  o1_source_unit_ok u /\ MEM fn u.cu_context.ctx_functions ==>
  no_raw_fmp_ops fn
Proof
  rw[o1_source_unit_ok_def, no_raw_fmp_ops_def, EVERY_MEM] >>
  metis_tac[raw_opcode_ok_not_raw_fmp]
QED

Theorem source_fmp_free:
  o1_source_unit_ok unit /\ unit_fmp_unsealed unit ==>
  fmp_free_ctx unit.cu_context
Proof
  rw[fmp_free_ctx_def, unit_fmp_unsealed_def, EVERY_MEM] >>
  metis_tac[source_no_raw_fmp_ops]
QED

Theorem fmp_free_ctx_prune:
  fmp_free_ctx unit.cu_context ==>
  fmp_free_ctx (prune_unit_fcg_unreachable unit fcg).cu_context
Proof
  rw[fmp_free_ctx_def, prune_unit_fcg_unreachable_def] >>
  irule EVERY_FILTER_IMP >> simp[]
QED

Theorem o1_source_unit_ok_ctx_shape:
  unit_wf unit /\ o1_source_unit_ok unit /\ unit_entry_no_params unit ==>
  o1_ctx_shape unit.cu_context
Proof
  strip_tac >>
  drule_all o1_source_unit_label_refs_no_phi >> strip_tac >>
  simp[o1_ctx_shape_def] >> conj_tac
  >- gvs[unit_wf_def, venom_wf_def] >>
  conj_tac
  >- gvs[unit_wf_def, venom_wf_def] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  drule_all source_member_shape >> strip_tac >>
  simp[o1_fn_shape_def] >> rpt conj_tac
  >- gvs[unit_label_refs_ok_def, EVERY_MEM]
  >- (rpt strip_tac >> drule_all source_no_raw_fmp_ops >>
      simp[no_raw_fmp_ops_def] >> qexists_tac `inst` >>
      simp[is_raw_fmp_opcode_def])
  >- metis_tac[source_entry_shape]
  >> strip_tac >> drule_all source_internal_shape >> simp[]
QED

(* The pre-walk's input invariant: the source has no PHI. *)
Theorem o1_source_pre_walk_inv:
  o1_source_unit_ok unit /\ unit_defs_reach_uses unit /\
  o1_src_inv D unit.cu_context vs ==>
  o1_pre_walk_inv D unit.cu_context vs
Proof
  rw[o1_pre_walk_inv_def, o1_source_unit_ok_def, unit_defs_reach_uses_def,
     raw_opcode_ok_def] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

(* ===== One pre-walk schedule ===== *)

(* A pass mapped over every function, taking one invariant to another. *)
Theorem o1_mapped_pass_sim:
  o1_step_contract rpolicy pass /\
  (!view. o1_stage_contract rpolicy D pass view no_pre stage_inv stage_inv') /\
  run_mapped_functions rpolicy pass unit s = SOME (unit', s') /\
  o1_ctx_shape unit.cu_context /\
  ALL_DISTINCT (unit_label_namespace unit) /\ ir_supply_inst_ok s ==>
  o1_ctx_shape unit'.cu_context /\ unit_labels_wf unit' /\
  ir_supply_inst_ok s' /\
  unit'.cu_context.ctx_entry = unit.cu_context.ctx_entry /\
  unit'.cu_context.ctx_global_reserved = unit.cu_context.ctx_global_reserved /\
  ctx_fn_names unit'.cu_context = ctx_fn_names unit.cu_context /\
  !vs. dead_wf D /\ o1_run_state_ok vs /\ stage_inv unit.cu_context vs ==>
       ctx_sim D unit.cu_context unit'.cu_context vs vs /\
       stage_inv' unit'.cu_context vs
Proof
  strip_tac >> drule_all mapped_pass_stage >> strip_tac >>
  simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspec_then `any_view` mp_tac) >>
  simp[o1_stage_contract_def, no_pre_def] >>
  disch_then drule_all >> simp[]
QED

Theorem o1_pre_walk_sim:
  run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit s =
    SOME (unit', s') /\
  o1_ctx_shape unit.cu_context /\
  ALL_DISTINCT (unit_label_namespace unit) /\ ir_supply_inst_ok s ==>
  o1_ctx_shape unit'.cu_context /\ unit_labels_wf unit' /\
  ir_supply_inst_ok s' /\
  unit'.cu_context.ctx_entry = unit.cu_context.ctx_entry /\
  unit'.cu_context.ctx_global_reserved = unit.cu_context.ctx_global_reserved /\
  ctx_fn_names unit'.cu_context = ctx_fn_names unit.cu_context /\
  !D vs. dead_wf D /\ o1_run_state_ok vs /\ o1_pre_walk_inv D unit.cu_context vs ==>
         ctx_sim D unit.cu_context unit'.cu_context vs vs /\
         o1_walk_src_inv D unit'.cu_context vs
Proof
  strip_tac >> drule o1_pre_walk_runs >> strip_tac >>
  `!D. o1_ctx_shape mid.cu_context /\ unit_labels_wf mid /\
       ir_supply_inst_ok t /\
       mid.cu_context.ctx_entry = unit.cu_context.ctx_entry /\
       mid.cu_context.ctx_global_reserved =
         unit.cu_context.ctx_global_reserved /\
       ctx_fn_names mid.cu_context = ctx_fn_names unit.cu_context /\
       !vs. dead_wf D /\ o1_run_state_ok vs /\
            o1_pre_walk_inv D unit.cu_context vs ==>
         ctx_sim D unit.cu_context mid.cu_context vs vs /\
         o1_walk_src_inv D mid.cu_context vs` by
    (gen_tac >> irule o1_mapped_pass_sim >>
     metis_tac[o1_contract_simplify_cfg_pre_walk]) >>
  first_assum (strip_assume_tac o Q.SPEC `ARB`) >>
  drule unit_labels_wf_namespace >> strip_tac >>
  `!D. o1_ctx_shape unit'.cu_context /\ unit_labels_wf unit' /\
       ir_supply_inst_ok s' /\
       unit'.cu_context.ctx_entry = mid.cu_context.ctx_entry /\
       unit'.cu_context.ctx_global_reserved =
         mid.cu_context.ctx_global_reserved /\
       ctx_fn_names unit'.cu_context = ctx_fn_names mid.cu_context /\
       !vs. dead_wf D /\ o1_run_state_ok vs /\
            o1_walk_src_inv D mid.cu_context vs ==>
         ctx_sim D mid.cu_context unit'.cu_context vs vs /\
         o1_walk_src_inv D unit'.cu_context vs` by
    (gen_tac >> irule o1_mapped_pass_sim >>
     metis_tac[o1_contract_dret_desugar_pre_walk]) >>
  first_assum (strip_assume_tac o Q.SPEC `ARB`) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  `ctx_sim D unit.cu_context mid.cu_context vs vs /\
   o1_walk_src_inv D mid.cu_context vs` by metis_tac[] >>
  `ctx_sim D mid.cu_context unit'.cu_context vs vs /\
   o1_walk_src_inv D unit'.cu_context vs` by metis_tac[] >>
  metis_tac[ctx_sim_trans]
QED

(* A per-function fact that a pass's runs keep holds of every function
   after a stage of it. *)
Theorem ctx_pass_stage_every:
  ctx_pass_stage rpolicy pass view C C' /\
  (!observed s f out.
     fn_pass_step rpolicy pass observed s f out /\ P f ==>
     P out.fpo_function) /\
  EVERY P C.ctx_functions ==>
  EVERY P C'.ctx_functions
Proof
  rw[ctx_pass_stage_def, EVERY_EL, LIST_REL_EL_EQN] >>
  `n < LENGTH C.ctx_functions` by gvs[] >>
  qpat_x_assum `!n. n < _ ==> ?observed s out. _`
    (qspec_then `n` strip_assume_tac) >>
  gvs[] >> metis_tac[]
QED

(* The walk's input is at row 0: SimplifyCFG's pre-walk run makes every
   function a MakeSSA input (the source has no PHI and definite
   assignment), both pre-walk runs keep the source's freedom from raw FMP
   operations and its unset FMP conventions, and DretDesugar is the
   identity. *)
Theorem o1_pre_walk_rows:
  run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit s =
    SOME (unit', s') /\
  o1_ctx_shape unit.cu_context /\
  ALL_DISTINCT (unit_label_namespace unit) /\ ir_supply_inst_ok s /\
  o1_source_unit_ok unit /\ unit_defs_reach_uses unit /\
  unit_fmp_unsealed unit ==>
  EVERY (o1_fn_row 0) unit'.cu_context.ctx_functions
Proof
  strip_tac >> drule o1_pre_walk_runs >> strip_tac >>
  mp_tac (Q.INST [`rp` |-> `rpolicy`, `pass` |-> `CFP_Simple VP_SimplifyCFG`,
                  `u` |-> `unit`, `u'` |-> `mid`, `s'` |-> `t`]
            mapped_pass_stage) >>
  impl_tac >- simp[o1_contract_simplify_cfg_pre_walk] >> strip_tac >>
  mp_tac (Q.INST [`rp` |-> `rpolicy`, `pass` |-> `CFP_Simple VP_DretDesugar`,
                  `u` |-> `mid`, `s` |-> `t`, `u'` |-> `unit'`]
            mapped_pass_stage) >>
  impl_tac
  >- simp[o1_contract_dret_desugar_pre_walk, unit_labels_wf_namespace] >>
  strip_tac >>
  `unit'.cu_context = mid.cu_context` by metis_tac[dret_desugar_stage_identity] >>
  `EVERY make_ssa_input_ok mid.cu_context.ctx_functions` by
    (`mid.cu_context.ctx_functions =
        MAP simplify_cfg_fn unit.cu_context.ctx_functions` by
       metis_tac[simplify_cfg_stage_functions] >>
     asm_rewrite_tac[EVERY_MAP] >> simp[EVERY_MEM] >> rpt strip_tac >>
     irule simplify_cfg_pre_walk_make_ssa_input_ok >>
     rpt conj_tac
     >- fs[unit_defs_reach_uses_def, EVERY_MEM]
     >- (fs[o1_source_unit_ok_def, EVERY_MEM] >> rpt strip_tac >>
         res_tac >> gvs[raw_opcode_ok_def]) >>
     qexists_tac `unit.cu_context` >> fs[o1_ctx_shape_def, EVERY_MEM]) >>
  `EVERY no_raw_fmp_ops mid.cu_context.ctx_functions` by
    (mp_tac (Q.INST [`C` |-> `unit.cu_context`, `C'` |-> `mid.cu_context`,
                     `pass` |-> `CFP_Simple VP_SimplifyCFG`,
                     `view` |-> `any_view`, `P` |-> `no_raw_fmp_ops`]
               ctx_pass_stage_every) >>
     impl_tac >- (
     rpt conj_tac
     >- first_assum ACCEPT_TAC
     >- (rpt strip_tac >>
         qpat_x_assum `fn_pass_step _ _ _ _ _ _`
           (strip_assume_tac o REWRITE_RULE [fn_pass_step_def]) >>
         drule_at (Pos last) execute_configured_fn_pass_o1_suffix_no_raw_fmp_ops >>
         simp[] >> metis_tac[]) >>
     simp[EVERY_MEM] >> metis_tac[source_no_raw_fmp_ops]) >>
     simp[]) >>
  `EVERY fmp_sig_no_param mid.cu_context.ctx_functions` by
    (mp_tac (Q.INST [`C` |-> `unit.cu_context`, `C'` |-> `mid.cu_context`,
                     `pass` |-> `CFP_Simple VP_SimplifyCFG`,
                     `view` |-> `any_view`, `P` |-> `fmp_sig_no_param`]
               ctx_pass_stage_every) >>
     impl_tac >- (
     rpt conj_tac
     >- first_assum ACCEPT_TAC
     >- (rpt strip_tac >> drule fn_pass_step_fmp_sig_no_param >>
         simp[fn_pass_tag_def] >> metis_tac[]) >>
     fs[unit_fmp_unsealed_def, EVERY_MEM, fmp_sig_no_param_def]) >>
     simp[]) >>
  fs[EVERY_MEM, o1_fn_row_def]
QED

(* ===== Pruning ===== *)

Theorem o1_ctx_shape_prune:
  fcg = fcg_analyze unit.cu_context /\ o1_ctx_shape unit.cu_context ==>
  o1_ctx_shape (prune_unit_fcg_unreachable unit fcg).cu_context /\
  (ALL_DISTINCT (unit_label_namespace unit) ==>
   ALL_DISTINCT (unit_label_namespace (prune_unit_fcg_unreachable unit fcg)))
Proof
  strip_tac >> conj_tac
  >- (simp[o1_ctx_shape_def] >> conj_tac
      >- metis_tac[ctx_wf_prune_unit_fcg_unreachable, o1_ctx_shape_wf] >>
      conj_tac
      >- (fs[o1_ctx_shape_def, ctx_inst_ids_distinct_ir_ids,
             prune_unit_fcg_unreachable_def] >>
          metis_tac[namespace_filter_distinct]) >>
      simp[EVERY_MEM] >> metis_tac[pruned_member_shape]) >>
  simp[unit_label_namespace_def, prune_unit_fcg_unreachable_def] >>
  metis_tac[namespace_filter_distinct]

QED

Theorem o1_prune_sim:
  fcg = fcg_analyze unit.cu_context /\ o1_ctx_shape unit.cu_context /\
  unit.cu_context.ctx_entry = SOME entry /\
  (!fn inst s. M unit.cu_context fn inst s ==>
               M (prune_unit_fcg_unreachable unit fcg).cu_context fn inst s) ==>
  (!fuel vs. run_context fuel unit.cu_context vs =
             run_context fuel (prune_unit_fcg_unreachable unit fcg).cu_context vs) /\
  !vs. mem_inv M unit.cu_context vs ==>
       mem_inv M (prune_unit_fcg_unreachable unit fcg).cu_context vs
Proof
  strip_tac >>
  `ctx_wf unit.cu_context /\ wf_invoke_targets unit.cu_context` by
    metis_tac[o1_ctx_shape_wf] >>
  drule_all prune_unit_ctx_agree >> strip_tac >>
  `fcg_is_reachable fcg entry` by metis_tac[fcg_analyze_entry_reachable] >>
  conj_tac
  >- (rpt gen_tac >> irule run_context_ctx_agree >>
      simp[prune_unit_fcg_unreachable_fields] >>
      qexists_tac `fcg_is_reachable fcg` >> gvs[]) >>
  rpt gen_tac >> strip_tac >> irule mem_inv_ctx_agree >>
  simp[prune_unit_fcg_unreachable_fields] >>
  qexists_tac `fcg_is_reachable fcg` >>
  qexists_tac `unit.cu_context` >>
  gvs[] >> metis_tac[]
QED

Theorem o1_prune_gas_events:
  fcg = fcg_analyze unit.cu_context /\ o1_ctx_shape unit.cu_context /\
  unit.cu_context.ctx_entry = SOME entry /\
  lookup_function entry unit.cu_context.ctx_functions = SOME fn ==>
  !fuel vs. gas_events_blocks fuel unit.cu_context fn vs =
    gas_events_blocks fuel (prune_unit_fcg_unreachable unit fcg).cu_context fn vs
Proof
  rpt strip_tac >>
  `ctx_wf unit.cu_context /\ wf_invoke_targets unit.cu_context` by
    metis_tac[o1_ctx_shape_wf] >>
  drule_all prune_unit_ctx_agree >> strip_tac >>
  `fcg_is_reachable fcg entry` by metis_tac[fcg_analyze_entry_reachable] >>
  `fn_calls_within (fcg_is_reachable fcg) fn` by metis_tac[ctx_agree_def] >>
  irule (cj 3 gas_events_defs_ctx_agree) >>
  qexists_tac `fcg_is_reachable fcg` >> simp[]
QED

(* Pruning keeps the source invariant: the pruned context's functions
   are among the source's, and its reachable frames are the source's. *)
Theorem o1_src_inv_prune:
  fcg = fcg_analyze unit.cu_context /\ o1_ctx_shape unit.cu_context /\
  unit.cu_context.ctx_entry = SOME entry /\ o1_src_inv D unit.cu_context vs ==>
  o1_src_inv D (prune_unit_fcg_unreachable unit fcg).cu_context vs
Proof
  strip_tac >>
  `ctx_wf unit.cu_context /\ wf_invoke_targets unit.cu_context` by
    metis_tac[o1_ctx_shape_wf] >>
  drule_all prune_unit_ctx_agree >> strip_tac >>
  `fcg_is_reachable fcg entry` by metis_tac[fcg_analyze_entry_reachable] >>
  `!fn. MEM fn (prune_unit_fcg_unreachable unit fcg).cu_context.ctx_functions ==>
        MEM fn unit.cu_context.ctx_functions` by
    simp[MEM_prune_unit_fcg_unreachable_functions] >>
  `mem_inv raw_mem_ok (prune_unit_fcg_unreachable unit fcg).cu_context vs` by
    (mp_tac (Q.INST [`M` |-> `raw_mem_ok`] o1_prune_sim) >>
     impl_tac >- (fs[] >> metis_tac[raw_mem_ok_ctx_free]) >>
     strip_tac >> pop_assum irule >> fs[o1_src_inv_def]) >>
  `mem_inv dload_offset_ok (prune_unit_fcg_unreachable unit fcg).cu_context vs` by
    (mp_tac (Q.INST [`M` |-> `dload_offset_ok`] o1_prune_sim) >>
     impl_tac >- (fs[] >> metis_tac[dload_offset_ok_ctx_free]) >>
     strip_tac >> pop_assum irule >> fs[o1_src_inv_def]) >>
  `mem_inv dload_headroom_ok (prune_unit_fcg_unreachable unit fcg).cu_context vs` by
    (mp_tac (Q.INST [`M` |-> `dload_headroom_ok`] o1_prune_sim) >>
     impl_tac >- (fs[] >> metis_tac[dload_headroom_ok_prune]) >>
     strip_tac >> pop_assum irule >> fs[o1_src_inv_def]) >>
  qpat_x_assum `fcg = _` kall_tac >>
  fs[o1_src_inv_def] >> rpt conj_tac
  >- fs[prune_unit_fcg_unreachable_fields]
  >- fs[EVERY_MEM]
  >- (fs[ctx_has_dalloca_def, EXISTS_MEM] >> metis_tac[])
  >- (qexists_tac `lo` >>
      simp[fixed_region_reserved_def, prune_unit_fcg_unreachable_fields] >>
      conj_tac >- fs[fixed_region_reserved_def] >>
      irule ptr_discipline_ctx_agree >>
      simp[prune_unit_fcg_unreachable_fields] >>
      qexistsl_tac [`fcg_is_reachable fcg`, `unit.cu_context`] >> gvs[])
  >- (irule taint_within_ctx_agree >>
      simp[prune_unit_fcg_unreachable_fields] >>
      qexistsl_tac [`fcg_is_reachable fcg`, `unit.cu_context`] >> gvs[])
  >> irule fmp_free_ctx_prune >> fs[]
QED

(* ===== The walk ===== *)

(* Pruning keeps a fact of every function. *)
Theorem o1_prune_every:
  EVERY P unit.cu_context.ctx_functions ==>
  EVERY P (prune_unit_fcg_unreachable unit fcg).cu_context.ctx_functions
Proof
  simp[prune_unit_fcg_unreachable_def, EVERY_FILTER_IMP]
QED

Theorem o1_walk_callee_first:
  fcg = fcg_analyze unit.cu_context /\ o1_ctx_shape unit.cu_context /\
  unit.cu_context.ctx_entry = SOME entry /\
  reachable_fcg_acyclic unit.cu_context fcg ==>
  ALL_DISTINCT (fcg_postorder fcg entry) /\
  (!n. MEM n (fcg_postorder fcg entry) <=>
       MEM n (ctx_fn_names (prune_unit_fcg_unreachable unit fcg).cu_context)) /\
  callee_first (fcg_postorder fcg entry)
    (prune_unit_fcg_unreachable unit fcg).cu_context.ctx_functions
Proof
  strip_tac >>
  `ctx_wf unit.cu_context /\ wf_invoke_targets unit.cu_context` by
    metis_tac[o1_ctx_shape_wf] >>
  conj_tac >- simp[fcg_postorder_all_distinct] >>
  conj_tac >- metis_tac[postorder_pruned_names] >>
  simp[callee_first_def, MEM_prune_unit_fcg_unreachable_functions] >>
  rpt gen_tac >> strip_tac >>
  drule_all member_invoke_direct_call >> strip_tac >>
  gvs[] >> simp[list_precedes_iff] >>
  metis_tac[fcg_postorder_callee_before_caller]
QED

(* The nine stage contexts of the walk, composed. *)
Theorem o1_walk_before_dft[local]:
  (!k. k < LENGTH o1_fn_passes ==>
       ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
         (stage k) (stage (SUC k))) /\
  (!k. k <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage k)) /\
  (!k. k <= LENGTH o1_fn_passes ==> EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  dead_wf D ==>
  !n vs. n < 7 /\ o1_run_state_ok vs /\ o1_inv D 0 (stage 0) vs ==>
    ctx_sim D (stage 0) (stage (SUC n)) vs vs /\
    o1_inv D (SUC n) (stage (SUC n)) vs
Proof
  strip_tac >>
  `!k vs. k < 7 /\ o1_run_state_ok vs /\ o1_inv D k (stage k) vs ==>
     ctx_sim D (stage k) (stage (SUC k)) vs vs /\
     o1_inv D (SUC k) (stage (SUC k)) vs` by
    (rpt gen_tac >> strip_tac >>
     `o1_run_contract rpolicy D k` by
       (irule o1_run_contracts_same_gas >> simp[o1_fn_passes_def]) >>
     fs[o1_run_contract_def, o1_stage_contract_def] >>
     qpat_x_assum `!C C' vs. _` irule >>
     simp[o1_pre_def, o1_fn_passes_def] >> metis_tac[]) >>
  Induct
  >- (rpt strip_tac >> metis_tac[]) >>
  rpt strip_tac >> `n < 7` by decide_tac >>
  `ctx_sim D (stage 0) (stage (SUC n)) vs vs /\
   o1_inv D (SUC n) (stage (SUC n)) vs` by metis_tac[] >>
  `ctx_sim D (stage (SUC n)) (stage (SUC (SUC n))) vs vs /\
   o1_inv D (SUC (SUC n)) (stage (SUC (SUC n))) vs` by metis_tac[] >>
  metis_tac[ctx_sim_trans]
QED

Theorem o1_walk_stages_sim:
  (!k. k < LENGTH o1_fn_passes ==>
       ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
         (stage k) (stage (SUC k))) /\
  (!k. k <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage k)) /\
  (!k. k <= LENGTH o1_fn_passes ==> EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  dead_wf D /\ o1_run_state_ok vs_out ==>
  ?vs_in. dft_gas_replay (stage 7) (stage 8) vs_in vs_out /\
    (o1_inv D 0 (stage 0) vs_in ==>
     ctx_sim D (stage 0) (stage (LENGTH o1_fn_passes)) vs_in vs_out /\
     o1_inv D (LENGTH o1_fn_passes) (stage (LENGTH o1_fn_passes)) vs_out)
Proof
  strip_tac >>
  `o1_pre 7 (stage 7) (stage 8) /\ o1_pre 8 (stage 8) (stage 9) /\
   o1_ctx_shape (stage 7) /\ o1_ctx_shape (stage 8) /\
   EVERY wf_ssa (stage 7).ctx_functions` by
    (fs[o1_pre_def, o1_fn_passes_def] >>
     qpat_x_assum `!k. k <= 9 ==> EVERY _ _` (qspec_then `7` mp_tac) >>
     simp[EVERY_MEM, o1_fn_row_def] >> metis_tac[]) >>
  `ctx_pass_stage rpolicy (CFP_Simple VP_DFT) (o1_walk_view rpolicy 7)
     (stage 7) (stage 8)` by
    (qpat_x_assum `!k. k < _ ==> ctx_pass_stage _ _ _ _ _`
       (qspec_then `7` mp_tac) >> simp[o1_fn_passes_def]) >>
  drule_all dft_stage_sim_gas >> strip_tac >>
  qexists_tac `vs` >> simp[] >> strip_tac >>
  `gas_variant vs vs_out` by metis_tac[dft_gas_replay_variant] >>
  `o1_run_state_ok vs` by metis_tac[gas_variant_run_state_ok] >>
  `ctx_sim D (stage 0) (stage 7) vs vs /\ o1_inv D 7 (stage 7) vs` by
    (mp_tac (Q.INST [`rpolicy` |-> `rpolicy`, `stage` |-> `stage`, `D` |-> `D`]
      o1_walk_before_dft) >> simp[] >> disch_then (qspecl_then [`6`, `vs`] mp_tac) >> simp[]) >>
  `o1_inv D 8 (stage 8) vs_out` by
    (simp[o1_inv_def, o1_ssa_inv_def] >> conj_tac
     >- (qpat_x_assum `o1_inv D 7 _ _`
           (strip_assume_tac o SIMP_RULE (srw_ss()) [o1_inv_def, o1_ssa_inv_def]) >>
         metis_tac[]) >>
     irule dft_stage_wf_ssa >> metis_tac[]) >>
  `o1_run_contract rpolicy D 8` by
    (irule o1_run_contracts_same_gas >> simp[o1_fn_passes_def]) >>
  `ctx_sim D (stage 8) (stage 9) vs_out vs_out /\
   o1_inv D 9 (stage 9) vs_out` by
    (fs[o1_run_contract_def, o1_stage_contract_def] >>
     qpat_x_assum `!C C' vs. _` irule >> simp[] >>
     qpat_x_assum `!k. k < _ ==> ctx_pass_stage _ _ _ _ _`
       (qspec_then `8` mp_tac) >> simp[o1_fn_passes_def]) >>
  simp[o1_fn_passes_def] >> metis_tac[ctx_sim_trans]
QED

Theorem o1_walk_sim:
  fcg = fcg_analyze unit.cu_context /\ o1_ctx_shape unit.cu_context /\
  unit.cu_context.ctx_entry = SOME entry /\
  reachable_fcg_acyclic unit.cu_context fcg /\
  ALL_DISTINCT (unit_label_namespace unit) /\
  run_callee_first rpolicy o1_fn_passes (fcg_postorder fcg entry)
    (prune_unit_fcg_unreachable unit fcg) s = SOME (unit', s') /\
  ir_supply_inst_ok s /\ EVERY (o1_fn_row 0) unit.cu_context.ctx_functions ==>
  o1_ctx_shape unit'.cu_context /\
  unit'.cu_context.ctx_entry = SOME entry /\
  ctx_fn_names unit'.cu_context =
    ctx_fn_names (prune_unit_fcg_unreachable unit fcg).cu_context /\
  ?stage.
  stage 0 = (prune_unit_fcg_unreachable unit fcg).cu_context /\
  stage (LENGTH o1_fn_passes) = unit'.cu_context /\
  (!k. k < LENGTH o1_fn_passes ==>
    ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
      (stage k) (stage (SUC k))) /\
  (!k. k <= LENGTH o1_fn_passes ==>
    o1_ctx_shape (stage k) /\
    EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  !D vs_out. dead_wf D /\ o1_run_state_ok vs_out ==>
    ?vs_in. dft_gas_replay (stage 7) (stage 8) vs_in vs_out /\
      (o1_walk_src_inv D (prune_unit_fcg_unreachable unit fcg).cu_context vs_in ==>
       ctx_sim D (prune_unit_fcg_unreachable unit fcg).cu_context
               unit'.cu_context vs_in vs_out /\
       o1_lowered_inv unit'.cu_context vs_out)
Proof
  strip_tac >> drule_all o1_ctx_shape_prune >> strip_tac >>
  drule_all o1_walk_callee_first >> strip_tac >>
  fs[run_callee_first_def] >>
  drule_at (Pos (el 3)) (Q.INST [`R` |-> `o1_fn_row`] o1_schedule_stages) >>
  impl_tac
  >- fs[o1_fn_passes_steps, o1_step_contracts_from_rows, o1_prune_every] >>
  strip_tac >>
  `o1_ctx_shape unit'.cu_context /\
   unit'.cu_context.ctx_entry = SOME entry /\
   ctx_fn_names unit'.cu_context =
     ctx_fn_names (prune_unit_fcg_unreachable unit fcg).cu_context` by
    (qpat_x_assum `!k. k <= _ ==> _` (qspec_then `LENGTH o1_fn_passes` mp_tac) >>
     gvs[prune_unit_fcg_unreachable_fields]) >>
  simp[] >> qexists_tac `stage` >> simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum drule >> simp[o1_walk_view_def]) >>
  rpt gen_tac >> strip_tac >>
  `?names. callee_first names (stage 0).ctx_functions` by
    (qexists_tac `fcg_postorder fcg entry` >> gvs[]) >>
  `(!C vs. o1_inv D 0 C vs <=>
           o1_walk_src_inv D C vs /\ ?names. callee_first names C.ctx_functions) /\
   o1_inv D (LENGTH o1_fn_passes) = o1_lowered_inv` by
    simp[o1_inv_def, o1_fn_passes_def] >>
  `?vi. dft_gas_replay (stage 7) (stage 8) vi vs_out /\
    (o1_inv D 0 (stage 0) vi ==>
     ctx_sim D (stage 0) (stage (LENGTH o1_fn_passes)) vi vs_out /\
     o1_inv D (LENGTH o1_fn_passes) (stage (LENGTH o1_fn_passes)) vs_out)` by
    (irule o1_walk_stages_sim >> fs[] >> qexists_tac `rpolicy` >>
     rpt strip_tac >> first_x_assum drule >> simp[o1_walk_view_def]) >>
  gvs[] >> metis_tac[]
QED

(* ===== The pipeline ===== *)

(* The witness fixes the compiler schedules and a certified O1 stage chain.
   Only DFT changes the list; its replay is bound to the output's events. *)
Definition o1_gas_replay_def:
  o1_gas_replay rp unit out vs_in vs_out <=>
    ?pre t entry t' stage.
      run_pipeline_stages rp o1_pipeline_spec.ps_pre_walk_stages unit
        (init_ir_supply unit) = SOME (pre,t) /\
      pre.cu_context.ctx_entry = SOME entry /\
      run_callee_first rp o1_fn_passes
        (fcg_postorder (fcg_analyze pre.cu_context) entry)
        (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)) t =
          SOME (out.po_unit,t') /\
      stage 0 = (prune_unit_fcg_unreachable pre
                  (fcg_analyze pre.cu_context)).cu_context /\
      stage (LENGTH o1_fn_passes) = out.po_unit.cu_context /\
      (!k. k < LENGTH o1_fn_passes ==>
        ctx_pass_stage rp (EL k o1_fn_passes) (o1_walk_view rp k)
          (stage k) (stage (SUC k))) /\
      (!k. k <= LENGTH o1_fn_passes ==>
        o1_ctx_shape (stage k) /\
        EVERY (o1_fn_row k) (stage k).ctx_functions) /\
      dft_gas_replay (stage 7) (stage 8) vs_in vs_out
End

Theorem o1_gas_replay_variant:
  o1_gas_replay rp unit out vs_in vs_out ==> gas_variant vs_in vs_out
Proof
  metis_tac[o1_gas_replay_def, dft_gas_replay_variant]
QED

Theorem o1_pipeline_stage_facts:
  run_venom_pipeline mem_ok calling_ok post_ok rpolicy o1_pipeline_spec unit =
    SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit ==>
  o1_ctx_shape out.po_unit.cu_context /\
  entry_fn_first out.po_unit.cu_context /\
  !D vs_out. dead_wf D /\ o1_run_state_ok vs_out ==>
    ?vs_in. o1_gas_replay rpolicy unit out vs_in vs_out /\
      (o1_pre_walk_inv D unit.cu_context vs_in ==>
       ctx_sim D unit.cu_context out.po_unit.cu_context vs_in vs_out /\
       o1_lowered_inv out.po_unit.cu_context vs_out)
Proof
  strip_tac >> drule o1_driver_runs >> strip_tac >>
  `o1_ctx_shape unit.cu_context` by metis_tac[o1_source_unit_ok_ctx_shape] >>
  `ir_supply_inst_ok (init_ir_supply unit)`
    by simp[irSupplyTheory.init_ir_supply_inst_ok] >>
  drule_all o1_pre_walk_rows >> strip_tac >>
  drule_all o1_pre_walk_sim >> strip_tac >>
  drule_at (Pos (el 6)) o1_walk_sim >> impl_tac
  >- (gvs[] >> metis_tac[unit_labels_wf_namespace]) >> strip_tac >>
  simp[] >> conj_tac
  >- (`entry_fn_first pre.cu_context` by
        metis_tac[source_entry_first, entry_fn_first_names] >>
      `entry_fn_first
         (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context` by
        (simp[prune_unit_fcg_unreachable_def] >>
         irule entry_fn_first_filter >> simp[] >>
         metis_tac[fcg_analyze_entry_reachable, o1_ctx_shape_wf]) >>
      irule entry_fn_first_names >>
      qexists_tac `(prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context` >>
      gvs[prune_unit_fcg_unreachable_fields]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!D vs_out. _` (qspecl_then [`D`, `vs_out`] mp_tac) >>
  simp[] >> disch_then (qx_choose_then `vs` strip_assume_tac) >>
  qexists_tac `vs` >> conj_tac
  >- (rewrite_tac[o1_gas_replay_def] >>
      qexistsl_tac [`pre`, `t`, `entry`, `t'`, `stage`] >> simp[] >> metis_tac[]) >>
  strip_tac >>
  `o1_run_state_ok vs` by
    metis_tac[gas_variant_run_state_ok, dft_gas_replay_variant] >>
  `ctx_sim D unit.cu_context pre.cu_context vs vs /\
   o1_walk_src_inv D pre.cu_context vs` by metis_tac[] >>
  `(!fuel vs. run_context fuel pre.cu_context vs =
      run_context fuel (prune_unit_fcg_unreachable pre
        (fcg_analyze pre.cu_context)).cu_context vs) /\
   !vs. mem_inv raw_mem_ok pre.cu_context vs ==>
     mem_inv raw_mem_ok (prune_unit_fcg_unreachable pre
       (fcg_analyze pre.cu_context)).cu_context vs` by
    (irule o1_prune_sim >> metis_tac[raw_mem_ok_ctx_free]) >>
  `o1_walk_src_inv D (prune_unit_fcg_unreachable pre
                        (fcg_analyze pre.cu_context)).cu_context vs` by
    (qpat_x_assum `o1_walk_src_inv D pre.cu_context vs` mp_tac >>
     rewrite_tac[o1_walk_src_inv_def] >> strip_tac >> conj_tac
     >- (irule o1_src_inv_prune >> metis_tac[])
     >> conj_tac >> irule o1_prune_every >> first_assum ACCEPT_TAC) >>
  `ctx_sim D unit.cu_context
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context vs vs` by
    (irule ctx_sim_run_context_eq >> qexists_tac `pre.cu_context` >> simp[]) >>
  metis_tac[ctx_sim_trans]
QED

Theorem o1_ctx_shape_unit_shape_ok:
  o1_ctx_shape unit.cu_context /\ entry_fn_first unit.cu_context ==>
  unit_shape_ok unit
Proof
  strip_tac >>
  `EVERY (o1_fn_shape unit.cu_context) unit.cu_context.ctx_functions` by
    gvs[o1_ctx_shape_def] >>
  drule_all entry_shape_from_members >>
  simp[unit_shape_ok_def] >>
  gvs[EVERY_MEM, o1_fn_shape_def]
QED
