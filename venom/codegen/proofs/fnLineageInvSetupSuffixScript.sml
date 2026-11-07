Theory fnLineageInvSetupSuffix
Ancestors fnLineageInvWeakSuffix fnLineageInvWeakStep fnLineageInvBoundary fnLineageInvOrdinarySuffix
  fnLineageInvSingletonSetup fnLineageInvSupport planWfMarked
  fnPlanLineageInventory stackPlanGen venomExecProps venomExecProofs
  codegenReadyCompute livenessTransferProofs list rich_list pred_set finite_map

Theorem analyzed_exact_suffix_replay:
 !fn bb dfg cfg spillbase p j ps ops qs r.
 codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
 j+p <= LENGTH bb.bb_instructions /\
 EVERY (\inst. inst.inst_opcode <> PHI /\ ~is_param_opcode inst.inst_opcode)
   (DROP (j+p) bb.bb_instructions) /\
 lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label (j+p)))) ps /\
 (?m core. lineage_core m core ps /\ residual_budget_wf spillbase [] (ps with ps_stack := core)) /\
 generate_block_insts_plan (liveness_analyze fn) dfg cfg fn bb.bb_label F p
   (LENGTH bb.bb_instructions) j (DROP (j+p) bb.bb_instructions) ps = SOME (ops,qs)
 ==>
 (?n tail. lineage_core n tail qs /\ EVERY is_var_operand tail /\
   residual_budget_wf spillbase [] (qs with ps_stack := tail) /\
   set tail SUBSET set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions)))) /\
 (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions)) ==>
   MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) /\
 (j+p < LENGTH bb.bb_instructions /\
   (LAST bb.bb_instructions).inst_opcode <> NOP /\
   (LAST bb.bb_instructions).inst_opcode <> OFFSET ==>
   lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions)))) qs) /\
 generate_block_insts_plan (liveness_analyze fn) dfg cfg fn bb.bb_label F p
   (LENGTH bb.bb_instructions) j (DROP (j+p) bb.bb_instructions)
   (ps with ps_stack := REPLICATE r dead_stack_marker ++ ps.ps_stack) =
 SOME (ops,qs with ps_stack := REPLICATE r dead_stack_marker ++ qs.ps_stack)
Proof
 rpt gen_tac >> strip_tac >>
 drule_all lineage_inventory_canonical_budget >> strip_tac >>
 irule analyzed_weak_suffix_replay >> simp[] >>
 conj_tac
 >- (drule lineage_inventory_live_membership >> simp[]) >>
 conj_tac
 >- (qexistsl_tac [`n`,`tail`] >> simp[] >> ASM_SET_TAC[]) >>
 irule analyzed_inventory_suffix_outputs_fresh >> simp[] >>
 gvs[EVERY_MEM] >> qexists_tac `fn` >> simp[]
QED

Theorem analyzed_active_singleton_suffix_replay:
 !fn pred succ pb sb ps spillbase cops start dfg cfg ops qs r.
 codegen_ready_fn fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
 lookup_block pred fn.fn_blocks = SOME pb /\
 lookup_block succ fn.fn_blocks = SOME sb /\
 MEM succ (cfg_succs_of (cfg_analyze fn) pred) /\
 cfg_preds_of (cfg_analyze fn) succ = [pred] /\
 1 < LENGTH (cfg_succs_of (cfg_analyze fn) pred) /\
 lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) pred
   (LENGTH pb.bb_instructions)))) ps /\
 generated_plan_state_wf_marked spillbase ps /\
 clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn sb ps = (cops,start) /\
 EVERY (\inst. inst.inst_opcode <> PHI /\ ~is_param_opcode inst.inst_opcode)
   sb.bb_instructions /\
 generate_block_insts_plan (liveness_analyze fn) dfg cfg fn sb.bb_label F 0
   (LENGTH sb.bb_instructions) 0 sb.bb_instructions start = SOME (ops,qs)
 ==>
 (?n tail. lineage_core n tail qs /\ EVERY is_var_operand tail /\
   residual_budget_wf spillbase [] (qs with ps_stack := tail) /\
   set tail SUBSET set (MAP Var (live_vars_at (liveness_analyze fn) sb.bb_label (LENGTH sb.bb_instructions)))) /\
 (!v. MEM v (live_vars_at (liveness_analyze fn) sb.bb_label (LENGTH sb.bb_instructions)) ==>
   MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) /\
 (0 < LENGTH sb.bb_instructions /\
   (LAST sb.bb_instructions).inst_opcode <> NOP /\
   (LAST sb.bb_instructions).inst_opcode <> OFFSET ==>
   lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) sb.bb_label (LENGTH sb.bb_instructions)))) qs) /\
 generate_block_insts_plan (liveness_analyze fn) dfg cfg fn sb.bb_label F 0
   (LENGTH sb.bb_instructions) 0 sb.bb_instructions
   (start with ps_stack := REPLICATE r dead_stack_marker ++ start.ps_stack) =
 SOME (ops,qs with ps_stack := REPLICATE r dead_stack_marker ++ qs.ps_stack)
Proof
 rpt gen_tac >> strip_tac >>
 `sb.bb_label = succ` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
 `wf_function fn` by gvs[codegen_ready_fn_def] >>
 `MEM sb fn.fn_blocks` by metis_tac[livenessTransferProofsTheory.lookup_block_mem] >>
 `fn_reachable fn sb.bb_label` by
   (metis_tac[codegenReadyComputeTheory.fn_reachable_cfg_analyze,
      codegenReadyComputeTheory.fn_cfg_edge_cfg_analyze,
      venomExecProofsTheory.fn_reachable_step]) >>
 drule_all analyzed_singleton_setup_active_resources >> strip_tac >>
 drule_all analyzed_active_cleanup_outputs_fresh >> disch_tac >>
 drule_all clean_stack_plan_spilled >> disch_tac >>
 `residual_budget_wf spillbase [] (start with ps_stack := core)` by simp[] >>
 drule_at (Pat `lineage_inventory _ start`) lineage_inventory_canonical_budget >>
 disch_then drule >> disch_then drule >> strip_tac >>
 irule (SRULE [] (Q.INST [`p` |-> `0`, `j` |-> `0`]
   (SPEC_ALL analyzed_weak_suffix_replay))) >> simp[] >>
 conj_tac
 >- (rpt strip_tac >>
     `Var v IN set tail UNION FDOM start.ps_spilled` by
       (qpat_x_assum `set tail UNION _ = _` (fn th => rewrite_tac[th]) >>
        simp[MEM_MAP]) >>
     gvs[lineage_core_def, MEM_APPEND]) >>
 conj_tac
 >- (qexistsl_tac [`n`,`tail`] >> simp[] >>
     drule residual_budget_wf_empty_inventory >> simp[] >> strip_tac >> ASM_SET_TAC[]) >>
 gvs[EVERY_FLAT, EVERY_MAP, combinTheory.o_DEF]
QED
