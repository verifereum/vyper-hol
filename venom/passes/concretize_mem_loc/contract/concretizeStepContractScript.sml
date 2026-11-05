(*
 * ConcretizeMemLoc's step contract: the structural half of its O1 pass
 * contract, at its walk position (run 2).
 *
 * TOP-LEVEL:
 *   concretize_step_contract_at
 *)
Theory concretizeStepContract
Ancestors
  o1PassContract concretizeMemLocDefs venomPassDispatcher concretizeStepShape
  concretizeStepStructure unitShapeDefs venomInst venomWf passSharedDefs
  passSimulationDefs irSupply dretDesugarDefs list venomFnScheduleRunnerProps
  concretizeStageShape venomPassSchedule

Theorem concretize_blocks_copy_phi:
  f.fn_blocks = g.fn_blocks ==>
  (copy_phi_var origin f x <=> copy_phi_var origin g x)
Proof
  strip_tac >> eq_tac >> strip_tac >> drule copy_phi_var_mono >>
  disch_then irule >> simp[fn_insts_def]
QED

Theorem concretize_blocks_reachable_insts:
  f.fn_blocks = g.fn_blocks ==>
  fn_insts (reachable_fn f) = fn_insts (reachable_fn g)
Proof
  strip_tac >>
  `fn_cfg_edge f = fn_cfg_edge g` by simp[FUN_EQ_THM, fn_cfg_edge_def] >>
  `fn_reachable f = fn_reachable g` by
    simp[FUN_EQ_THM, fn_reachable_def, fn_entry_label_def, entry_block_def] >>
  `reachable_preds f = reachable_preds g` by
    simp[FUN_EQ_THM, reachable_preds_def] >>
  `reachable_inst f = reachable_inst g` by
    simp[FUN_EQ_THM, reachable_inst_def] >>
  simp[fn_insts_def, reachable_fn_def]
QED

Theorem concretize_blocks_o1_shape:
  f.fn_blocks = g.fn_blocks /\ f.fn_name = g.fn_name ==>
  (o1_fn_shape ctx f <=> o1_fn_shape ctx g)
Proof
  strip_tac >>
  `fn_insts f = fn_insts g` by simp[fn_insts_def] >>
  `!origin x. copy_phi_var origin f x <=> copy_phi_var origin g x` by
    metis_tac[concretize_blocks_copy_phi] >>
  `fn_insts (reachable_fn f) = fn_insts (reachable_fn g)` by
    metis_tac[concretize_blocks_reachable_insts] >>
  `!origin x. copy_phi_var origin (reachable_fn f) x <=>
              copy_phi_var origin (reachable_fn g) x` by
    (rpt gen_tac >> eq_tac >> strip_tac >> drule copy_phi_var_mono >>
     disch_then irule >> simp[]) >>
  simp[o1_fn_shape_def, wf_function_def, fn_labels_def, fn_has_entry_def,
       fn_succs_closed_def, fn_inst_ids_distinct_def, fn_inst_wf_def,
       fn_shape_ok_def, fn_entry_label_def, entry_block_def,
       opaque_use_ok_def, retpc_shape_ok_def, retpc_var_def, gas_var_def,
       call_checks_ok_def, first_block_no_preds_def, first_block_no_phi_def,
       fn_invoke_ok_def, fn_label_refs_ok_def, no_dret_def,
       entry_fn_no_return_def, entry_fn_no_params_def]
QED

Theorem concretize_context_layout_contract:
  o1_fn_shape ctx fn ==>
  o1_fn_shape ctx (apply_context_concretize_layout ctx layout fn) /\
  fresh_names_ok s fn (apply_context_concretize_layout ctx layout fn) /\
  EVERY (\i. i.inst_opcode <> ALLOCA)
    (fn_insts (apply_context_concretize_layout ctx layout fn))
Proof
  strip_tac >>
  `o1_fn_shape ctx (concretize_function_with_positions layout.cl_positions fn)` by
    simp[concretize_positions_o1_fn_shape] >>
  `fn_inst_wf fn` by fs[o1_fn_shape_def] >>
  `fresh_names_ok s fn (concretize_function_with_positions layout.cl_positions fn)` by
    simp[concretize_positions_fresh_names] >>
  `EVERY (\i. i.inst_opcode <> ALLOCA)
     (fn_insts (concretize_function_with_positions layout.cl_positions fn))` by
    simp[concretize_positions_no_alloca] >>
  qmatch_goalsub_abbrev_tac `o1_fn_shape ctx out` >>
  qabbrev_tac `rewritten = concretize_function_with_positions layout.cl_positions fn` >>
  `out.fn_blocks = rewritten.fn_blocks /\ out.fn_name = rewritten.fn_name` by
    simp[Abbr `out`, Abbr `rewritten`, apply_context_concretize_layout_def,
         apply_concretize_layout_def] >>
  conj_tac >- metis_tac[concretize_blocks_o1_shape] >>
  fs[fresh_names_ok_def, fn_labels_def, fn_ir_inst_ids_def, fn_insts_def]
QED

Theorem concretize_context_success_contract:
  o1_fn_shape ctx fn /\
  concretize_function_fuel_in_context fuel ctx reserved fn = SOME out ==>
  o1_fn_shape ctx out /\ fresh_names_ok s fn out /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts out)
Proof
  simp[concretize_function_fuel_in_context_def] >>
  IF_CASES_TAC
  >- (IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
      simp[fresh_names_ok_def] >>
      fs[fn_has_alloca_def, EXISTS_MEM, EVERY_MEM] >>
      metis_tac[is_alloca_op_def]) >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  simp[concretize_context_layout_contract]
QED

(* Why it holds (intuition, not a prescribed proof).

   concretize_function_fuel_in_context either returns fn itself (a
   function with a static layout and no ALLOCA) or
   apply_context_concretize_layout ctx layout fn, which maps each
   instruction through concretize_inst_with_positions: ALLOCA becomes
   ASSIGN [Lit pos] with the same outputs and inst_id, every other
   instruction is kept, and only metadata (fn_eom, fn_mems_used,
   fn_forced_alloc_positions) changes.  So labels, blocks, terminators,
   INVOKE operands, PHIs and each CALL's success check (call_checks_ok)
   are unchanged; fresh_names_ok holds because labels and ids are fn's;
   the label map is []; and the output has no ALLOCA (row 3).  A function
   with a static layout is returned as it is, and the rewrite keeps the
   blocks' shape and adds no FMP operation, so the output is still a
   MakeSSA input without raw FMP operations; the FMP convention is kept. *)
Theorem concretize_step_contract_at:
  o1_step_contract_at 2 rpolicy (CFP_Simple VP_ConcretizeMemLoc)
Proof
  simp[o1_step_contract_at_def, o1_fn_row_def] >> rpt strip_tac >>
  `o1_fn_shape observed.cu_context fn` by
    (fs[fn_pass_step_def, o1_ctx_shape_def, EVERY_MEM] >>
     drule lookup_unique_function_member >> strip_tac >> metis_tac[]) >>
  `wf_function fn /\ fn_inst_wf fn` by fs[o1_fn_shape_def] >>
  `make_ssa_input_ok out.fpo_function` by
    metis_tac[concretize_step_make_ssa_input_ok] >>
  `no_raw_fmp_ops out.fpo_function` by metis_tac[concretize_step_no_raw_fmp] >>
  `fmp_sig_no_param out.fpo_function` by
    (drule fn_pass_step_fmp_sig_no_param >>
     simp[fn_pass_tag_def] >> metis_tac[]) >>
  qpat_x_assum `fn_pass_step _ _ _ _ _ _` mp_tac >>
  simp[fn_pass_step_def, execute_configured_fn_pass_concretize, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  simp[label_map_sources_ok_def] >>
  drule_all concretize_context_success_contract >> simp[]
QED

