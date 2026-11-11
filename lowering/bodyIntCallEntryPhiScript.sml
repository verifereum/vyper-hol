(* PHI-free entry prefix of the actual internal-function compiler. *)
Theory bodyIntCallEntryPhi
Ancestors
  bodyIntCallActualEntryFields intCallCallee emitHelperProps compileEnv
  context moduleLowering fragExec venomExecSemantics venomInst rich_list list
Libs
  monadsyntax

Theorem internal_entry_no_phi:
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,rpc,imm),st1) /\ st0.cs_current_insts = [] ==>
  st1.cs_current_insts <> [] /\
  EVERY (\i. i.inst_opcode <> PHI) st1.cs_current_insts
Proof
  simp[compile_internal_function_entry_def, compile_internal_entry_prefix_def,
       comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  dxrule compile_internal_param_decls_shape >> strip_tac >>
  dxrule intCallCalleeTheory.materialize_internal_params_shape >> strip_tac >>
  Cases_on `has_rb` >> Cases_on `rt` >> Cases_on `ce.ce_returns_count > 0` >>
  Cases_on `ctor /\ imm_len > 0` >>
  gvs[emitHelperTheory.emit_op_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def,
      compile_alloc_buffer_def, compile_fixed_region_with_id_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[emitHelperTheory.emit_op_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def] >>
  simp[EVERY_GENLIST, mk_inst_def] >>
  gvs[EVERY_MEM] >> rpt strip_tac >>
  qpat_x_assum `!i. MEM i new ==> _` (qspec_then `i` mp_tac) >>
  simp[]
QED

Theorem internal_entry_phi_boundary:
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,rpc,imm),st1) /\ st0.cs_current_insts = [] /\
  fn_has_code st0 st1 func /\
  lookup_block st0.cs_current_bb func.fn_blocks = SOME bb ==>
  phi_prefix_length bb.bb_instructions = 0 /\
  !s. eval_phis s bb.bb_instructions = OK s
Proof
  strip_tac >> drule_all internal_entry_no_phi >> strip_tac >>
  drule compile_internal_entry_shape >> strip_tac >>
  `isPREFIX st1.cs_current_insts bb.bb_instructions` by
    (fs[fn_has_code_def] >> gvs[]) >>
  Cases_on `st1.cs_current_insts` >> gvs[] >>
  Cases_on `bb.bb_instructions` >>
  gvs[phi_prefix_length_def, eval_phis_def]
QED

Theorem internal_entry_phi_landing:
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,rpc,imm),st1) /\ st0.cs_current_insts = [] /\
  fn_has_code st0 st1 func /\
  setup_callee func args caller = SOME setup /\
  st0.cs_current_bb = (HD func.fn_blocks).bb_label /\
  lookup_block setup.vs_current_bb func.fn_blocks = SOME bb /\
  eval_phis setup bb.bb_instructions = OK phi_state /\
  entered = phi_state with vs_inst_idx := phi_prefix_length bb.bb_instructions ==>
  entered = setup
Proof
  strip_tac >> drule intCallCalleeTheory.setup_callee_frontier >> strip_tac >>
  `lookup_block st0.cs_current_bb func.fn_blocks = SOME bb` by gvs[] >>
  drule_all internal_entry_phi_boundary >> strip_tac >> gvs[] >>
  simp[venomStateTheory.venom_state_component_equality]
QED
