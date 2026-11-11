(* Instruction decoding and initial callee PHIs, without executing INVOKE. *)
Theory bodyIntCallFamCallIntEntryLanding
Ancestors
  bodyIntCallCompletedModes bodyIntCallCompilerBoundary intCallCallee
  fragGasFocus fragExec venomExecSemantics venomInst
  bodySim loweringShapeSource ctorDeployShape supportedProgram supportedNames
  loweringShapeProps unitShapeDefs list

Theorem intcall_body_raw_instructions:
  !tops ctx ce cx.
    body_inv tops ctx ce cx ==>
    !fn inst. MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) ==>
      raw_opcode_ok inst.inst_opcode
Proof
  rpt gen_tac >> simp[body_inv_def] >> strip_tac >>
  `ALL_DISTINCT (supported_function_names tops)` by
    gvs[supported_program_def, supported_declaration_names_def] >>
  `o1_source_unit_ok unit` by
    (Cases_on `cx.in_deploy` >> gvs[] >>
     metis_tac[supported_program_runtime_bodies_shape_ok,
       supported_names_internal_names_distinct,
       lower_vyper_deploy_unit_source_unit_ok,
       lower_vyper_runtime_unit_source_unit_ok_shape]) >>
  gvs[o1_source_unit_ok_def, EVERY_MEM] >> metis_tac[]
QED

Theorem intcall_decoded_entry:
  !ctx func t bb inst lbl ops argv callee setup first.
    ~t.vs_halted /\
    lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx = SOME inst /\
    inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (lbl,ops) /\
    lookup_function lbl ctx.ctx_functions = SOME callee /\
    eval_operands ops t = SOME argv /\
    setup_callee callee argv t = SOME setup /\
    lookup_block setup.vs_current_bb callee.fn_blocks = SOME first /\
    phi_prefix_length first.bb_instructions = 0 ==>
    gas_invoke_entry (ctx,func) t callee setup
Proof
  rpt gen_tac >> strip_tac >>
  drule setup_callee_frontier >> strip_tac >>
  simp[gas_invoke_entry_def] >>
  qexists_tac `setup` >>
  simp[eval_phis_no_phi]
QED

Theorem intcall_body_block_no_phi:
  !tops ctx ce cx fn lbl bb.
    body_inv tops ctx ce cx /\ MEM fn ctx.ctx_functions /\
    lookup_block lbl fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  rpt gen_tac >> strip_tac >>
  `!inst. MEM inst bb.bb_instructions ==> raw_opcode_ok inst.inst_opcode` by
    metis_tac[intcall_body_raw_instructions, lookup_block_fn_insts] >>
  Cases_on `bb.bb_instructions` >> simp[phi_prefix_length_def] >>
  fs[raw_opcode_ok_def]
QED

Theorem intcall_body_decoded_entry:
  !tops ctx ce cx func t bb inst lbl ops argv callee setup.
    body_inv tops ctx ce cx /\ MEM callee ctx.ctx_functions /\
    ~t.vs_halted /\
    lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx = SOME inst /\
    inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (lbl,ops) /\
    lookup_function lbl ctx.ctx_functions = SOME callee /\
    eval_operands ops t = SOME argv /\
    setup_callee callee argv t = SOME setup ==>
    gas_invoke_entry (ctx,func) t callee setup
Proof
  rpt gen_tac >> strip_tac >>
  drule setup_callee_frontier >> strip_tac >>
  `lookup_block setup.vs_current_bb callee.fn_blocks =
     SOME (HD callee.fn_blocks)` by
    (Cases_on `callee.fn_blocks` >>
     gvs[setup_callee_def, lookup_block_def, FIND_def, INDEX_FIND_def]) >>
  `phi_prefix_length (HD callee.fn_blocks).bb_instructions = 0` by
    metis_tac[intcall_body_block_no_phi] >>
  irule intcall_decoded_entry >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED
