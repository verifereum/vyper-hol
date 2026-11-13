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
  o1FnScheduleDecompHelpers o1DretDesugarContract o1ContractSimplifyCfg
  ctxLookupAgree ptrDiscipline ptrDisciplineAgree unitMemInv
  unitTransformDefs unitShapeDefs venomPipelineDriver venomPipelineRunner
  venomPipelineRunnerProps venomPassDispatcherProps venomFnScheduleRunner venomPassSchedule
  venomPassDispatcher venomCompilerWf venomWf venomInst venomExecSemantics
  venomState stateEquivProps fcgDefs fcgPruning fcgPostorder
  fcgAnalysisProps fcgBridge contextCodegenRel venomMemDefs list rich_list

(* Exact observable agreement supplies the same input for every mask. *)

Theorem storage_agree_except_mono[local]:
  X SUBSET Y /\ storage_agree_except X st1 st2 ==>
  storage_agree_except Y st1 st2
Proof
  rw[storage_agree_except_def, word_agree_except_def, key_taint_def,
     pred_setTheory.SUBSET_DEF] >>
  metis_tac[]
QED

Theorem accounts_agree_from_empty[local]:
  accounts_agree_except
    <| d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {} |> a1 a2 ==>
  accounts_agree_except D a1 a2
Proof
  simp[accounts_agree_except_def] >>
  metis_tac[storage_agree_except_mono, pred_setTheory.EMPTY_SUBSET]
QED

Theorem transient_agree_except_empty[local]:
  transient_agree_except
    <| d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {} |> t1 t2 ==>
  transient_agree_except D t1 t2
Proof
  simp[transient_agree_except_def] >>
  metis_tac[storage_agree_except_mono, pred_setTheory.EMPTY_SUBSET]
QED

Theorem imms_agree_except_empty[local]:
  imms_agree_except
    <| d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {} |> i1 i2 ==>
  imms_agree_except D i1 i2
Proof
  simp[imms_agree_except_def, word_agree_except_def] >> metis_tac[]
QED

Theorem request_agree_except_empty[local]:
  request_agree_except
    <| d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {} |> r1 r2 ==>
  request_agree_except D r1 r2
Proof
  simp[request_agree_except_def] >>
  metis_tac[accounts_agree_from_empty, transient_agree_except_empty]
QED

Theorem dead_result_rel_empty[local]:
  dead_result_rel
    <| d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {} |> r1 r2 ==>
  dead_result_rel D r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >> simp[dead_result_rel_def] >>
  rpt strip_tac
  >- metis_tac[accounts_agree_from_empty]
  >- metis_tac[transient_agree_except_empty]
  >- metis_tac[imms_agree_except_empty] >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >>
  match_mp_tac LIST_REL_mono >> simp[request_agree_except_empty]
QED

Theorem ctx_sim_empty[local]:
  ctx_sim
    <| d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {} |> ctx ctx' s s' ==>
  ctx_sim D ctx ctx' s s'
Proof
  simp[ctx_sim_def] >> metis_tac[dead_result_rel_empty]
QED

Theorem o1_stage_contract_gas_all_dead[local]:
  o1_stage_contract_gas rp
    <| d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {} |> pass view pre Inv Inv' /\
  ctx_pass_stage rp pass view C C' /\ pre C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vo ==>
  ?vi. gas_variant vi vo /\
    !D. dead_wf D ==>
      (Inv C vi ==> ctx_sim D C C' vi vo /\ Inv' C' vo)
Proof
  rw[o1_stage_contract_gas_def, dead_wf_def] >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `vs` >> metis_tac[ctx_sim_empty]
QED

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
      (Inv A a ==> ctx_sim_fuel f D A B a b /\ Mid B b)) /\
  (!c. o1_run_state_ok c ==>
    ?b. gas_variant b c /\
      (Mid B b ==> ctx_sim_fuel g D B C b c /\ Post C c)) /\
  o1_run_state_ok c ==>
  ?a. gas_variant a c /\
    (Inv A a ==> ctx_sim_fuel (g o f) D A C a c /\ Post C c)
Proof
  strip_tac >>
  qpat_x_assum `!c. _` (qspec_then `c` mp_tac) >>
  simp[] >> strip_tac >>
  `o1_run_state_ok b` by metis_tac[gas_variant_run_state_ok] >>
  qpat_x_assum `!b. _` (qspec_then `b` mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `a` >> conj_tac
  >- metis_tac[gas_variant_trans] >>
  strip_tac >> metis_tac[ctx_sim_fuel_trans]
QED

Theorem guarded_ctx_sim_trans_all_dead[local]:
  (!b. o1_run_state_ok b ==>
    ?a. gas_variant a b /\
      !D. dead_wf D ==> (Inv D A a ==> ctx_sim D A B a b /\ Mid D B b)) /\
  (!c. o1_run_state_ok c ==>
    ?b. gas_variant b c /\
      !D. dead_wf D ==> (Mid D B b ==> ctx_sim D B C b c /\ Post D C c)) /\
  o1_run_state_ok c ==>
  ?a. gas_variant a c /\
    !D. dead_wf D ==> (Inv D A a ==> ctx_sim D A C a c /\ Post D C c)
Proof
  strip_tac >>
  qpat_x_assum `!c. _` (qspec_then `c` mp_tac) >>
  simp[] >> strip_tac >>
  `o1_run_state_ok b` by metis_tac[gas_variant_run_state_ok] >>
  qpat_x_assum `!b. _` (qspec_then `b` mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `a` >> conj_tac
  >- metis_tac[gas_variant_trans] >>
  rpt strip_tac >> metis_tac[ctx_sim_trans]
QED

Theorem ctx_sim_run_context_eq:
  ctx_sim_fuel f D C1 C2 s s /\
  (!fuel. run_context fuel C2 s = run_context fuel C3 s)
  ==> ctx_sim_fuel f D C1 C3 s s
Proof
  rw[ctx_sim_fuel_def] >> metis_tac[]
QED

(* Every pass of the walk before CFGNormalization keeps the fuel. *)
Theorem pass_fuel_walk_I:
  n < 8 ==> pass_fuel (EL n o1_fn_passes) C = I
Proof
  strip_tac >>
  `n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7` by
    decide_tac >>
  gvs[o1_fn_passes_def, pass_fuel_def]
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

Theorem o1_run_contracts_all_dead[local]:
  k < LENGTH o1_fn_passes /\
  ctx_pass_stage rp (EL k o1_fn_passes) (o1_walk_view rp k) C C' /\
  o1_ctx_shape C /\ o1_pre k C C' /\ o1_run_state_ok vo ==>
  ?vi. gas_variant vi vo /\
    !D. dead_wf D ==>
      (o1_inv D k C vi ==> ctx_sim D C C' vi vo /\ o1_inv D (SUC k) C' vo)
Proof
  strip_tac >>
  Cases_on `k = 7`
  >- (gvs[o1_inv_def] >>
      irule o1_stage_contract_gas_all_dead >>
      mp_tac (Q.INST [`rpolicy` |-> `rp`,
        `D` |-> `<| d_stor := K (K {}); d_trans := K (K {});
                    d_imm := K {}; d_ret := K {} |>`] o1_contract_dft) >>
      simp[o1_run_contract_gas_def, o1_inv_def] >> metis_tac[]) >>
  qexists_tac `vo` >> simp[gas_variant_refl] >>
  `!D. o1_run_contract rp D k` by
    (gen_tac >> fs[o1_fn_passes_def] >>
     `k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 8`
       by decide_tac >>
     gvs[o1_contract_make_ssa_1, o1_contract_lower_dload,
         o1_contract_concretize_mem_loc, o1_contract_fmp_lowering,
         o1_contract_make_ssa_2, o1_contract_simplify_cfg, o1_contract_sue,
         o1_contract_cfg_normalization]) >>
  gvs[o1_run_contract_def, o1_stage_contract_def] >> metis_tac[]
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
       ctx_sim_fuel (pass_fuel pass unit'.cu_context) D
         unit.cu_context unit'.cu_context vs vs /\
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
         ctx_sim_fuel I D unit.cu_context unit'.cu_context vs vs /\
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
         ctx_sim_fuel (pass_fuel (CFP_Simple VP_SimplifyCFG) mid.cu_context) D
           unit.cu_context mid.cu_context vs vs /\
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
         ctx_sim_fuel (pass_fuel (CFP_Simple VP_DretDesugar) unit'.cu_context) D
           mid.cu_context unit'.cu_context vs vs /\
         o1_walk_src_inv D unit'.cu_context vs` by
    (gen_tac >> irule o1_mapped_pass_sim >>
     metis_tac[o1_contract_dret_desugar_pre_walk]) >>
  first_assum (strip_assume_tac o Q.SPEC `ARB`) >>
  fs[pass_fuel_def] >> rpt gen_tac >> strip_tac >>
  `ctx_sim_fuel I D unit.cu_context mid.cu_context vs vs /\
   o1_walk_src_inv D mid.cu_context vs` by metis_tac[] >>
  `ctx_sim_fuel I D mid.cu_context unit'.cu_context vs vs /\
   o1_walk_src_inv D unit'.cu_context vs` by metis_tac[] >>
  `ctx_sim_fuel (I o I) D unit.cu_context unit'.cu_context vs vs` by
    (irule ctx_sim_fuel_trans >> metis_tac[]) >>
  fs[combinTheory.I_o_ID]
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
Theorem o1_walk_stages_sim_all_dead:
  (!k. k < LENGTH o1_fn_passes ==>
       ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
         (stage k) (stage (SUC k))) /\
  (!k. k <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage k)) /\
  (!k. k <= LENGTH o1_fn_passes ==> EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  o1_run_state_ok vs_out ==>
  ?vs_in. gas_variant vs_in vs_out /\
    !D. dead_wf D ==> (o1_inv D 0 (stage 0) vs_in ==>
     ctx_sim D (stage 0) (stage (LENGTH o1_fn_passes)) vs_in vs_out /\
     o1_inv D (LENGTH o1_fn_passes) (stage (LENGTH o1_fn_passes)) vs_out)
Proof
  strip_tac >>
  `!k vs. k < LENGTH o1_fn_passes /\ o1_run_state_ok vs ==>
    ?vi. gas_variant vi vs /\
      !D. dead_wf D ==> (o1_inv D k (stage k) vi ==>
       ctx_sim D (stage k) (stage (SUC k)) vi vs /\
       o1_inv D (SUC k) (stage (SUC k)) vs)` by
    (rpt gen_tac >> strip_tac >> irule o1_run_contracts_all_dead >>
     simp[o1_pre_def] >> qexists_tac `rpolicy` >> simp[]) >>
  `LENGTH o1_fn_passes = 9` by simp[o1_fn_passes_def] >> gvs[] >>
  `!n. n < 9 ==> !vo. o1_run_state_ok vo ==>
    ?vi. gas_variant vi vo /\
      !D. dead_wf D ==> (o1_inv D 0 (stage 0) vi ==>
       ctx_sim D (stage 0) (stage (SUC n)) vi vo /\
       o1_inv D (SUC n) (stage (SUC n)) vo)` by
    (Induct
     >- (rpt strip_tac >> first_x_assum irule >> simp[]) >>
     rpt strip_tac >>
     ho_match_mp_tac (Q.INST
       [`B` |-> `stage (SUC n)`, `Mid` |-> `\D. o1_inv D (SUC n)`]
       guarded_ctx_sim_trans_all_dead) >> simp[]) >>
  first_x_assum (qspec_then `8` mp_tac) >> simp[]
QED

(* The nine stage contexts of the walk, composed. *)
Theorem o1_walk_stages_sim:
  (!k. k < LENGTH o1_fn_passes ==>
       ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
         (stage k) (stage (SUC k))) /\
  (!k. k <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage k)) /\
  (!k. k <= LENGTH o1_fn_passes ==> EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  dead_wf D /\ o1_run_state_ok vs_out ==>
  ?vs_in. gas_variant vs_in vs_out /\
    (o1_inv D 0 (stage 0) vs_in ==>
     ctx_sim_fuel (cfg_norm_fuel (stage (LENGTH o1_fn_passes))) D
       (stage 0) (stage (LENGTH o1_fn_passes)) vs_in vs_out /\
     o1_inv D (LENGTH o1_fn_passes) (stage (LENGTH o1_fn_passes)) vs_out)
Proof
  strip_tac >>
  `!k vs. k < LENGTH o1_fn_passes /\ o1_run_state_ok vs ==>
    ?vi. gas_variant vi vs /\
      (o1_inv D k (stage k) vi ==>
       ctx_sim_fuel (pass_fuel (EL k o1_fn_passes) (stage (SUC k))) D
         (stage k) (stage (SUC k)) vi vs /\
       o1_inv D (SUC k) (stage (SUC k)) vs)` by
    (rpt gen_tac >> strip_tac >>
     `o1_run_contract_gas rpolicy D k` by simp[o1_run_contracts] >>
     fs[o1_run_contract_gas_def, o1_stage_contract_gas_def, o1_pre_def] >>
     `k <= LENGTH o1_fn_passes /\ SUC k <= LENGTH o1_fn_passes` by simp[] >>
     `EVERY (o1_fn_row k) (stage k).ctx_functions /\
      EVERY (o1_fn_row (SUC k)) (stage (SUC k)).ctx_functions` by simp[] >>
     first_x_assum (qspecl_then [`stage k`, `stage (SUC k)`, `vs`] mp_tac) >>
     simp[]) >>
  `LENGTH o1_fn_passes = 9` by simp[o1_fn_passes_def] >>
  gvs[] >>
  `!n. n < 9 ==> !vo. o1_run_state_ok vo ==>
    ?vi. gas_variant vi vo /\
      (o1_inv D 0 (stage 0) vi ==>
       ctx_sim_fuel (pass_fuel (EL n o1_fn_passes) (stage (SUC n))) D
         (stage 0) (stage (SUC n)) vi vo /\
       o1_inv D (SUC n) (stage (SUC n)) vo)` by
    (Induct
     >- (rpt strip_tac >> first_x_assum irule >> simp[]) >>
     rpt strip_tac >>
     `?vi. gas_variant vi vo /\
        (o1_inv D 0 (stage 0) vi ==>
         ctx_sim_fuel (pass_fuel (EL (SUC n) o1_fn_passes) (stage (SUC (SUC n))) o
                       pass_fuel (EL n o1_fn_passes) (stage (SUC n))) D
           (stage 0) (stage (SUC (SUC n))) vi vo /\
         o1_inv D (SUC (SUC n)) (stage (SUC (SUC n))) vo)` suffices_by
       (`pass_fuel (EL n o1_fn_passes) (stage (SUC n)) = I` by
          simp[pass_fuel_walk_I] >>
        simp[combinTheory.I_o_ID]) >>
     irule guarded_ctx_sim_trans >> simp[] >>
     qexistsl_tac [`stage (SUC n)`, `o1_inv D (SUC n)`] >>
     simp[]) >>
  first_x_assum (qspec_then `8` mp_tac) >>
  simp[o1_fn_passes_def, pass_fuel_def]
QED

Theorem o1_walk_sim_all_dead:
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
  !vs_out. o1_run_state_ok vs_out ==>
    ?vs_in. gas_variant vs_in vs_out /\
      !D. dead_wf D ==> (o1_walk_src_inv D (prune_unit_fcg_unreachable unit fcg).cu_context vs_in ==>
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
  `?names. callee_first names (stage 0).ctx_functions` by
    (qexists_tac `fcg_postorder fcg entry` >> gvs[]) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  `(!D C vs. o1_inv D 0 C vs <=>
           o1_walk_src_inv D C vs /\ ?names. callee_first names C.ctx_functions) /\
   (!D. o1_inv D (LENGTH o1_fn_passes) = o1_lowered_inv)` by
    simp[o1_inv_def, o1_fn_passes_def] >>
  `?vi. gas_variant vi vs_out /\
    !D. dead_wf D ==> (o1_inv D 0 (stage 0) vi ==>
     ctx_sim D (stage 0) (stage (LENGTH o1_fn_passes)) vi vs_out /\
     o1_inv D (LENGTH o1_fn_passes) (stage (LENGTH o1_fn_passes)) vs_out)` by
    (irule o1_walk_stages_sim_all_dead >> fs[] >> qexists_tac `rpolicy` >>
     rpt strip_tac >> first_x_assum drule >> simp[o1_walk_view_def]) >>
  qexists_tac `vi` >> gvs[] >> metis_tac[]
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
  !D vs_out. dead_wf D /\ o1_run_state_ok vs_out ==>
    ?vs_in. gas_variant vs_in vs_out /\
      (o1_walk_src_inv D (prune_unit_fcg_unreachable unit fcg).cu_context vs_in ==>
       ctx_sim_fuel (cfg_norm_fuel unit'.cu_context) D
         (prune_unit_fcg_unreachable unit fcg).cu_context
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
  simp[] >> rpt gen_tac >> strip_tac >>
  `?names. callee_first names (stage 0).ctx_functions` by
    (qexists_tac `fcg_postorder fcg entry` >> gvs[]) >>
  `(!C vs. o1_inv D 0 C vs <=>
           o1_walk_src_inv D C vs /\ ?names. callee_first names C.ctx_functions) /\
   o1_inv D (LENGTH o1_fn_passes) = o1_lowered_inv` by
    simp[o1_inv_def, o1_fn_passes_def] >>
  `?vi. gas_variant vi vs_out /\
    (o1_inv D 0 (stage 0) vi ==>
     ctx_sim_fuel (cfg_norm_fuel (stage (LENGTH o1_fn_passes))) D
       (stage 0) (stage (LENGTH o1_fn_passes)) vi vs_out /\
     o1_inv D (LENGTH o1_fn_passes) (stage (LENGTH o1_fn_passes)) vs_out)` by
    (irule o1_walk_stages_sim >> fs[] >> qexists_tac `rpolicy` >>
     rpt strip_tac >> first_x_assum drule >> simp[o1_walk_view_def]) >>
  gvs[] >> metis_tac[]
QED

(* ===== The pipeline ===== *)

Theorem o1_pipeline_stage_facts_all_dead:
  run_venom_pipeline mem_ok calling_ok post_ok rpolicy o1_pipeline_spec unit =
    SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit ==>
  o1_ctx_shape out.po_unit.cu_context /\
  entry_fn_first out.po_unit.cu_context /\
  !vs_out. o1_run_state_ok vs_out ==>
    ?vs_in. gas_variant vs_in vs_out /\
      !D. dead_wf D ==> (o1_pre_walk_inv D unit.cu_context vs_in ==>
       ctx_sim D unit.cu_context out.po_unit.cu_context vs_in vs_out /\
       o1_lowered_inv out.po_unit.cu_context vs_out)
Proof
  strip_tac >> drule o1_driver_runs >> strip_tac >>
  `o1_ctx_shape unit.cu_context` by metis_tac[o1_source_unit_ok_ctx_shape] >>
  `ir_supply_inst_ok (init_ir_supply unit)`
    by simp[irSupplyTheory.init_ir_supply_inst_ok] >>
  drule_all o1_pre_walk_rows >> strip_tac >>
  drule_all o1_pre_walk_sim >> strip_tac >>
  drule_at (Pos (el 6)) o1_walk_sim_all_dead >> impl_tac
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
  qpat_x_assum `!vs_out. _` (qspec_then `vs_out` mp_tac) >>
  simp[] >> disch_then (qx_choose_then `vs` strip_assume_tac) >>
  qexists_tac `vs` >> simp[] >> rpt strip_tac >>
  `o1_run_state_ok vs` by metis_tac[gas_variant_run_state_ok] >>
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

(* ===== The pipeline ===== *)

Theorem o1_pipeline_stage_facts:
  run_venom_pipeline mem_ok calling_ok post_ok rpolicy o1_pipeline_spec unit =
    SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit ==>
  o1_ctx_shape out.po_unit.cu_context /\
  entry_fn_first out.po_unit.cu_context /\
  !D vs_out. dead_wf D /\ o1_run_state_ok vs_out ==>
    ?vs_in. gas_variant vs_in vs_out /\
      (o1_pre_walk_inv D unit.cu_context vs_in ==>
       ctx_sim_fuel (cfg_norm_fuel out.po_unit.cu_context) D
         unit.cu_context out.po_unit.cu_context vs_in vs_out /\
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
  qexists_tac `vs` >> simp[] >> strip_tac >>
  `o1_run_state_ok vs` by metis_tac[gas_variant_run_state_ok] >>
  `ctx_sim_fuel I D unit.cu_context pre.cu_context vs vs /\
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
  `ctx_sim_fuel I D unit.cu_context
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context vs vs` by
    (irule ctx_sim_run_context_eq >> qexists_tac `pre.cu_context` >> simp[]) >>
  `ctx_sim_fuel (cfg_norm_fuel out.po_unit.cu_context o I) D unit.cu_context
     out.po_unit.cu_context vs vs_out` by
    (irule ctx_sim_fuel_trans >> metis_tac[]) >>
  fs[combinTheory.I_o_ID]
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
