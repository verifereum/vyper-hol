Theory o1LabelFlowDftPreservation
Ancestors
  o1LabelFlowDftSeed o1LabelFlowLateDft codegenSymRel dftWf
  unitLabelMapIdentity list o1DftStep o1PassContract unitShapeDefs
  venomPassDispatcher venomFnScheduleRunnerProps

Theorem dft_fn_instruction_retained_or_flipped:
  wf_ssa f /\ wf_function f /\ fn_pseudos_prefix f /\
  MEM i (fn_insts f) ==>
  ?j. MEM j (fn_insts (dft_fn f)) /\
      (j = i \/ (is_flippable i.inst_opcode /\ j = flip_operands i))
Proof
  strip_tac >>
  drule_all dftScheduleOrderTheory.dft_fn_block_rel >> strip_tac >>
  gvs[fn_insts_MEM] >>
  drule_all LIST_REL_MEM_IMP >> strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[wf_fn_block_inst_ids_distinct] >>
  drule_all dftSsaPreserveTheory.dft_block_rel_member >> strip_tac >>
  metis_tac[]
QED

Theorem dft_fn_seed_retained:
  wf_ssa f /\ wf_function f /\ fn_pseudos_prefix f /\
  EVERY label_positions_ok (fn_insts (dft_fn f)) /\
  MEM i (fn_insts f) /\ i.inst_opcode = ADD /\
  i.inst_operands = [op; Label "code_end"] ==>
  MEM i (fn_insts (dft_fn f))
Proof
  strip_tac >> drule_all dft_fn_instruction_retained_or_flipped >>
  strip_tac >> gvs[] >>
  metis_tac[EVERY_MEM, flipped_code_end_seed_invalid]
QED

Theorem dft_fn_assign_retained:
  wf_ssa f /\ wf_function f /\ fn_pseudos_prefix f /\
  MEM i (fn_insts f) /\ i.inst_opcode = ASSIGN ==>
  MEM i (fn_insts (dft_fn f))
Proof
  strip_tac >> drule_all dft_fn_instruction_retained_or_flipped >>
  strip_tac >> gvs[] >>
  metis_tac[o1LabelFlowLateDftTheory.flip_operands_flow_opcodes, MEM]
QED

Theorem dft_code_end_var_forward:
  !f x. code_end_var f x ==>
  wf_ssa f /\ wf_function f /\ fn_pseudos_prefix f /\
  EVERY label_positions_ok (fn_insts (dft_fn f)) ==>
  code_end_var (dft_fn f) x
Proof
  Induct_on `code_end_var` >> rpt strip_tac
  >- (drule_all dft_fn_seed_retained >>
      metis_tac[code_end_var_rules]) >>
  drule_all dft_fn_assign_retained >> metis_tac[code_end_var_rules]
QED

Theorem dft_label_flow_ok:
  wf_ssa f /\ wf_function f /\ fn_pseudos_prefix f /\
  o1_fn_shape ctx f /\ EVERY label_positions_ok (fn_insts f) /\
  EVERY label_positions_ok (fn_insts (dft_fn f)) /\
  label_flow_ok (ctx with ctx_functions := [f]) ==>
  label_flow_ok (ctx with ctx_functions := [dft_fn f])
Proof
  strip_tac >> simp[label_flow_ok_def] >> gen_tac >> strip_tac >>
  `?j. MEM j (fn_insts f) /\
       (inst = j \/ (inst = flip_operands j /\ is_flippable j.inst_opcode))` by
    metis_tac[o1DftStepTheory.dft_shape_instruction_source] >>
  pop_assum strip_assume_tac >>
  `j.inst_opcode <> CODESIZE /\
   (!x. MEM (Var x) j.inst_operands /\ code_end_var f x ==>
     (j.inst_opcode = ASSIGN /\ j.inst_operands = [Var x]) \/
     (j.inst_opcode = CODECOPY /\ ?dst sz.
       j.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) /\
   (j.inst_opcode = CODECOPY ==> ?dst src sz.
     j.inst_operands = [dst; src; sz] /\
     (src = Label "runtime_begin" \/ ?x. src = Var x /\ code_end_var f x))` by
    (gvs[label_flow_ok_def] >> metis_tac[]) >>
  gvs[]
  >- (conj_tac
      >- (rpt strip_tac >>
          `code_end_var f x` by metis_tac[dft_code_end_var_reflect] >>
          metis_tac[]) >>
      strip_tac >> gvs[] >> metis_tac[dft_code_end_var_forward]) >>
  drule flip_operands_flow_opcodes >> simp[] >> strip_tac >>
  simp[] >> gen_tac >> spose_not_then strip_assume_tac >>
  `code_end_var f x` by metis_tac[dft_code_end_var_reflect] >>
  `MEM (Var x) j.inst_operands` by
    metis_tac[dftShapeTheory.flip_operands_operand_mem] >>
  metis_tac[]
QED

Theorem dft_row7_label_flow_ok:
  fn_pass_step rpolicy (CFP_Simple VP_DFT) observed s f out /\
  o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
  o1_fn_row 7 f /\
  label_flow_ok (observed.cu_context with ctx_functions := [f]) ==>
  label_flow_ok
    (observed.cu_context with ctx_functions := [out.fpo_function])
Proof
  strip_tac >>
  `wf_ssa f /\ fn_pseudos_prefix f` by gvs[o1_fn_row_def] >>
  drule_all dft_step_contract_ssa >> strip_tac >>
  `MEM f observed.cu_context.ctx_functions` by
    metis_tac[fn_pass_step_def, lookup_unique_function_member] >>
  `o1_fn_shape observed.cu_context f` by
    gvs[o1_ctx_shape_def, EVERY_MEM] >>
  `out.fpo_function = dft_fn f` by
    gvs[fn_pass_step_def, execute_configured_fn_pass_def] >>
  `wf_function f /\ EVERY label_positions_ok (fn_insts f) /\
   EVERY label_positions_ok (fn_insts out.fpo_function)` by
    (fs[o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM, inst_shape_ok_def] >>
     metis_tac[]) >>
  gvs[] >> irule dft_label_flow_ok >> simp[]
QED
