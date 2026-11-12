Theory o1LabelFlowSourceSsaStep
Ancestors
  o1LabelFlowSourceSsaLabels o1LabelFlowSourceBoundary
  o1ContractMakeSsaPtrOk
  o1FnScheduleDecompHelpers fmpStepBridge venomFnScheduleRunnerProps
  venomPassDispatcher o1PassContract unitShapeDefs list

(* CFP_Simple VP_MakeSSA is the first entry of o1_pipeline_spec.ps_fn_passes.
   Supply instruction validity is a runner input, not implied by fn_pass_step. *)
Theorem first_make_ssa_step_seed_free_flow:
  fn_pass_step rpolicy (CFP_Simple VP_MakeSSA) observed s f out /\
  o1_ctx_shape observed.cu_context /\ o1_fn_row 0 f /\
  ir_supply_inst_ok s /\
  (!i. MEM i (fn_insts f) ==> ~MEM (Label "code_end") i.inst_operands) /\
  (!i. MEM i (fn_insts f) ==>
    i.inst_opcode <> CODESIZE /\
    (i.inst_opcode = CODECOPY ==>
      ?dst sz. i.inst_operands = [dst; Label "runtime_begin"; sz])) ==>
  (!i. MEM i (fn_insts out.fpo_function) ==>
    ~MEM (Label "code_end") i.inst_operands) /\
  (!i. MEM i (fn_insts out.fpo_function) ==>
    i.inst_opcode <> CODESIZE /\
    (i.inst_opcode = CODECOPY ==>
      ?dst sz. i.inst_operands = [dst; Label "runtime_begin"; sz]))
Proof
  strip_tac >>
  `MEM f observed.cu_context.ctx_functions` by
    (gvs[fn_pass_step_def] >>
     metis_tac[lookup_unique_function_member]) >>
  `o1_fn_shape observed.cu_context f` by
    (gvs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `ir_supply_covers_fn s f` by
    (irule ir_supply_covers_unit_member >>
     qexists_tac `observed` >> gvs[fn_pass_step_def]) >>
  `~MEM "code_end" (fn_labels f)` by
    (metis_tac[o1_fn_shape_labels_not_reserved, reserved_label_def]) >>
  `make_ssa_input_ok f /\ fn_inst_wf f /\ wf_function f /\
   first_block_no_preds f /\ first_block_no_phi f` by
    gvs[o1_fn_shape_def, o1_fn_row_def] >>
  Cases_on `make_ssa_current_fn s f` >>
  `out.fpo_function = q` by
    gvs[fn_pass_step_def, execute_configured_fn_pass_make_ssa] >>
  conj_tac
  >- metis_tac[make_ssa_current_fn_label_operand_absent] >>
  drule_all mssa_origin >> strip_tac >>
  `!j. MEM j (fn_insts q) ==>
    MEM j.inst_opcode [PHI; ASSIGN; NOP] \/
    ?i. MEM i (fn_insts f) /\ j.inst_opcode = i.inst_opcode /\
      MAP (\op. case op of Var u => Var (orig u) | _ => op)
        j.inst_operands = i.inst_operands` by
    (rpt strip_tac >> first_x_assum drule >>
     simp[mssa_inst_origin_def] >> metis_tac[]) >>
  gvs[] >>
  ho_match_mp_tac seed_free_flow_origin_transport >>
  simp[]
QED
