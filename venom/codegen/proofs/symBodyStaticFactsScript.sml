(* Shared body-level label and operand facts.  The old owner exposes
   exact-statement corollaries of these kernels. *)
Theory symBodyStaticFacts
Ancestors
  fnBlockBody fnBlockBodySteps fnPlanLineageEntryProduction
  codegenSymRel asmSymBridge asmSymSem frameRel contextCodegenRel
  codegenRel unitShapeDefs venomExecSemantics venomState venomInst

Theorem codegen_sym_code_end_label_kernel:
  codegen_assembly rpolicy unit = SOME prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) ==>
  sym_data_label prog env "code_end"
Proof
  simp[codegenTheory.codegen_assembly_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> simp[sym_data_label_def]
QED

Theorem data_segment_asm_header_kernel:
  !segs ds. MEM ds segs ==>
    MEM (AsmDataHeader ds.ds_label) (data_segment_asm segs)
Proof
  Induct >> simp[asmIRTheory.data_segment_asm_def,
                 asmIRTheory.data_section_asm_def] >>
  metis_tac[asmIRTheory.data_segment_asm_def]
QED

Theorem codegen_sym_runtime_begin_label_kernel:
  codegen_assembly rpolicy unit = SOME prog /\
  sym_unit_static_ok unit /\ MEM fn unit.cu_context.ctx_functions /\
  MEM inst (fn_insts fn) /\ MEM (Label "runtime_begin") inst.inst_operands /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) ==>
  sym_data_label prog env "runtime_begin"
Proof
  rpt strip_tac >>
  `EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment` by
    metis_tac[sym_unit_static_ok_def] >>
  gvs[listTheory.EXISTS_MEM] >>
  `MEM (AsmDataHeader "runtime_begin") (data_segment_asm unit.cu_data_segment)` by
    metis_tac[data_segment_asm_header_kernel] >>
  gvs[codegenTheory.codegen_assembly_def, AllCaseEqs()] >>
  simp[sym_data_label_def]
QED

Theorem placed_nonentry_sym_code_label_kernel:
  !bb fn liveness dfg cfg ps ops ps' prog pc initial_fmp.
  bb <> HD fn.fn_blocks /\
  generate_block_plan liveness dfg cfg fn bb ps = SOME (ops, ps') /\
  asm_block_at prog pc (execute_plan initial_fmp ops) ==>
  MEM (AsmLabel bb.bb_label) prog
Proof
  rpt strip_tac >>
  drule_all fnPlanLineageEntryProductionTheory.generate_block_plan_nonentry >>
  strip_tac >> gvs[] >>
  irule spillWordBoundsTheory.asm_block_at_member >>
  goal_assum (drule_at Any) >>
  simp[planExecTheory.execute_plan_def, planExecTheory.exec_stack_op_def]
QED

Theorem placed_revert_sym_code_label_kernel:
  asm_block_at prog pc (execute_plan initial_fmp revert_postamble) ==>
  MEM (AsmLabel "revert") prog
Proof
  strip_tac >> irule spillWordBoundsTheory.asm_block_at_member >>
  goal_assum (drule_at Any) >>
  simp[stackPlanGenTheory.revert_postamble_def,
       planExecTheory.execute_plan_def, planExecTheory.exec_stack_op_def]
QED

Theorem invoke_operands_wf_shape_kernel:
  !inst. invoke_operands_wf inst ==>
    ?nm args. inst.inst_operands = Label nm :: args
Proof
  gen_tac >> namedCases_on `inst.inst_operands` ["", "op ops"]
  >- simp[stackPlanGenTheory.invoke_operands_wf_def] >>
  Cases_on `op` >> simp[stackPlanGenTheory.invoke_operands_wf_def]
QED

Theorem jmp_wf_operands_kernel:
  inst_wf inst /\ inst.inst_opcode = JMP ==>
  ?target. inst.inst_operands = [Label target] /\ inst.inst_outputs = [] /\
    is_terminator inst.inst_opcode /\ MEM target (get_successors inst)
Proof
  simp[venomWfTheory.inst_wf_def, is_terminator_def] >>
  rpt strip_tac >> gvs[get_successors_def, get_label_def, is_terminator_def]
QED

Theorem jnz_wf_operands_kernel:
  inst_wf inst /\ inst_shape_ok inst /\ inst.inst_opcode = JNZ ==>
  ?c l1 l2. inst.inst_operands = [c; Label l1; Label l2] /\
    inst.inst_outputs = [] /\ ~is_label_operand c /\
    is_terminator inst.inst_opcode /\ MEM c (compute_operands inst) /\
    MEM l1 (get_successors inst) /\ MEM l2 (get_successors inst)
Proof
  simp[venomWfTheory.inst_wf_def, inst_shape_ok_def,
       label_positions_ok_def, is_terminator_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `c` >>
  gvs[stackPlanGenTheory.compute_operands_def, asmIRTheory.get_non_label_operands_def,
      get_successors_def, get_label_def, stackPlanTypesTheory.is_label_operand_def,
      is_terminator_def]
QED

Theorem jnz_condition_frame_view_kernel:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = JNZ /\ inst.inst_operands = [c; Label l1; Label l2] ==>
  eval_operand c vs = eval_operand c (frame_view fn ra vs)
Proof
  strip_tac >> irule eval_operand_frame_view_vs >> rpt strip_tac >>
  `MEM (Var x) inst.inst_operands` by gvs[] >>
  drule_all opaque_use_ok_retpc_use >> simp[retpc_use_ok_def]
QED

Theorem sym_body_inst_bounds_reloc_kernel:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst ==>
  LENGTH (compute_operands inst) <= 16 /\
  (inst.inst_opcode = LOG ==>
    ?tc args. inst.inst_operands = Lit tc :: args /\ w2n tc <= 4)
Proof
  strip_tac >> drule body_inv_facts_reloc >> strip_tac >>
  drule_all body_inv_inst_reloc >> strip_tac >>
  conj_tac >- (drule_all body_operands_le_16 >> simp[]) >>
  strip_tac >> irule log_case_topics >>
  drule_all body_log_topics >> simp[]
QED
