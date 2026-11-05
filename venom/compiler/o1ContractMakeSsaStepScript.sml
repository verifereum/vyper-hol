(*
 * MakeSSA's step contract, for both of its O1 runs: the output keeps the
 * O1 function shape, its fresh names and instruction ids come from the
 * supply, it maps no labels, the supply stays ok, and it adds no ALLOCA
 * (the only function row).
 *)
Theory o1ContractMakeSsaStep
Ancestors
  o1PassContract makeSsaCurrentDefs venomPassSchedule irSupply
  o1MakeSsaRows o1MakeSsaStructuralShape o1MakeSsaRetpcShape
  o1MakeSsaOpaqueShape o1MakeSsaCalls venomPassDispatcher
  venomFnScheduleRunnerProps fmpStepBridge unitShapeDefs venomWf venomInst
  o1ContractMakeSsaPtrOk o1MakeSsaFormats o1MakeSsaCfg makeSsaCurrentProps
  venomFnScheduleRunner

(* MakeSSA keeps the O1 function shape; the main lemma of the step contract. *)
Theorem make_ssa_current_fn_o1_shape:
  make_ssa_input_ok fn /\ o1_fn_shape ctx fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (g,s') ==> o1_fn_shape ctx g
Proof
  strip_tac >>
  fs[o1_fn_shape_def, fn_shape_ok_def] >>
  `ALL_DISTINCT (MAP basic_block_bb_label fn.fn_blocks)` by
    (pure_once_rewrite_tac[GSYM bb_label_eta] >> fs[wf_function_def, fn_labels_def]) >>
  `g.fn_name = fn.fn_name` by metis_tac[mssa_fields] >>
  simp[o1_fn_shape_def, fn_shape_ok_def] >> rpt conj_tac
  >- metis_tac[make_ssa_current_fn_wf_function]
  >- metis_tac[make_ssa_current_fn_inst_wf]
  >- metis_tac[make_ssa_current_fn_entry_name]
  >- metis_tac[make_ssa_current_fn_opaque_use_ok]
  >- metis_tac[make_ssa_current_fn_retpc_shape_ok]
  >- metis_tac[make_ssa_current_fn_reserved_labels]
  >- metis_tac[make_ssa_current_fn_instruction_shapes]
  >- metis_tac[make_ssa_current_fn_call_checks_ok]
  >- metis_tac[make_ssa_current_fn_first_block_no_preds]
  >- metis_tac[make_ssa_current_fn_first_block_no_phi]
  >- metis_tac[make_ssa_current_fn_invoke_ok]
  >- metis_tac[make_ssa_current_fn_label_refs_ok]
  >- metis_tac[make_ssa_current_fn_no_dret]
  >- metis_tac[make_ssa_current_fn_dalloca_exclusions]
  >- metis_tac[make_ssa_current_fn_entry_no_return, make_ssa_current_fn_entry_no_params]
  >> strip_tac >>
  irule (SRULE[] make_ssa_current_fn_nonentry_termination) >> metis_tac[]
QED

Theorem make_ssa_step_contract_at:
  k = 0 \/ k = 4 ==> o1_step_contract_at k rpolicy (CFP_Simple VP_MakeSSA)
Proof
  strip_tac >> rewrite_tac[o1_step_contract_at_def] >> rpt gen_tac >> strip_tac >>
  `o1_fn_row (SUC k) out.fpo_function` by
    (irule make_ssa_step_rows >> metis_tac[]) >>
  `MEM fn observed.cu_context.ctx_functions` by
    (fs[fn_pass_step_def] >> drule lookup_unique_function_member >> simp[]) >>
  `o1_fn_shape observed.cu_context fn` by
    fs[o1_ctx_shape_def, listTheory.EVERY_MEM] >>
  `ir_supply_covers_fn s fn` by
    (irule ir_supply_covers_unit_member >> qexists `observed` >> fs[fn_pass_step_def]) >>
  `make_ssa_input_ok fn` by fs[o1_fn_row_def] >>
  `make_ssa_current_fn s fn = (out.fpo_function,out.fpo_supply) /\
   out.fpo_label_map = []` by
    (gvs[fn_pass_step_def, AllCaseEqs()] >> simp[]) >>
  `o1_fn_shape observed.cu_context out.fpo_function` by
    (irule make_ssa_current_fn_o1_shape >> metis_tac[]) >>
  fs[o1_fn_shape_def] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  `ALL_DISTINCT (fn_ir_inst_ids fn)` by
    (pure_rewrite_tac[fn_ir_inst_ids_def, lambdify block_ir_inst_ids_def] >>
     fs[wf_function_def, fn_inst_ids_distinct_def]) >>
  `EVERY (\id. MEM id s.irs_used_inst_ids) (fn_ir_inst_ids fn) /\
   ssa_vars_covered s (fn_ir_vars fn)` by
    fs[ir_supply_covers_fn_def, list_subset_def, ssa_vars_covered_def, listTheory.EVERY_MEM] >>
  drule_all make_ssa_current_fn_supply_ok >> strip_tac >>
  drule make_ssa_current_fn_labels >> strip_tac >>
  gvs[fresh_names_ok_def, label_map_sources_ok_def, ssa_ids_supply_ok_def,
      fn_labels_def] >> metis_tac[]
QED
