Theory o1LabelFlowOwnDft
Ancestors
  o1LabelFlowLateDft codegenSymOwnRel o1DftStep dftShape o1PassContract
  unitShapeDefs venomPassDispatcher venomFnScheduleRunnerProps list

Theorem dft_row7_code_end_uses:
  fn_pass_step rp (CFP_Simple VP_DFT) observed s f out /\
  o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
  o1_fn_row 7 f /\
  (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\
     code_end_var f x ==>
     (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
     (i.inst_opcode = CODECOPY /\ ?dst sz.
       i.inst_operands = [dst; Var x; sz] /\
       dst <> Var x /\ sz <> Var x)) ==>
  !i x. MEM i (fn_insts out.fpo_function) /\
    MEM (Var x) i.inst_operands /\ code_end_var out.fpo_function x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz.
      i.inst_operands = [dst; Var x; sz] /\
      dst <> Var x /\ sz <> Var x)
Proof
  strip_tac >>
  `MEM f observed.cu_context.ctx_functions` by
    metis_tac[fn_pass_step_def, lookup_unique_function_member] >>
  `o1_fn_shape observed.cu_context f` by
    gvs[o1_ctx_shape_def, EVERY_MEM] >>
  `out.fpo_function = dft_fn f` by
    gvs[fn_pass_step_def, execute_configured_fn_pass_def] >>
  `EVERY label_positions_ok (fn_insts f)` by
    (fs[o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM, inst_shape_ok_def] >>
     metis_tac[]) >>
  rpt strip_tac >>
  `code_end_var f x` by metis_tac[dft_code_end_var_reflect] >>
  `?j. MEM j (fn_insts f) /\
    (i = j \/ (i = flip_operands j /\ is_flippable j.inst_opcode))` by
    metis_tac[dft_shape_instruction_source] >>
  pop_assum strip_assume_tac >> gvs[] >>
  `MEM (Var x) j.inst_operands` by
    metis_tac[flip_operands_operand_mem] >>
  drule flip_operands_flow_opcodes >> simp[] >> metis_tac[]
QED
