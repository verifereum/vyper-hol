Theory createResultTail
Ancestors
  builtinCreate emitHelper context compileEnv exprLoweringProps
  externalEntryShape loweringShapeRules emitHelperProps
  fragExec fragGasOrigin createSizeEdgePC venomInst venomState venomExecSemantics
  list rich_list pair arithmetic relation createMarkedPath

Theorem create_result_check_layout_distinct:
  compile_check_create_result created T sd = (result,sb) /\
  fn_has_code sd sb func ==>
  ?cb fb fail j.
    sb.cs_current_insts = [] /\ fail <> sb.cs_current_bb /\
    lookup_block sd.cs_current_bb func.fn_blocks = SOME cb /\
    cb.bb_instructions = sd.cs_current_insts ++ [j] /\
    j.inst_opcode = JNZ /\
    j.inst_operands = [created; Label sb.cs_current_bb; Label fail] /\
    lookup_block fail func.fn_blocks = SOME fb /\
    MAP (\i. i.inst_opcode) fb.bb_instructions =
      [RETURNDATASIZE;ALLOCA;RETURNDATACOPY;REVERT]
Proof
  simp[compile_check_create_result_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_label_def, emit_inst_def, new_block_def,
       emit_op_def, emit_void_def, compile_alloc_buffer_def, fresh_id_def,
       fresh_var_def, emit_def] >>
  strip_tac >> gvs[fn_has_code_def, emitted_blocks_def, mk_inst_def] >>
  qpat_x_assum `!bb. _` mp_tac >>
  `SUC (SUC (LENGTH sd.cs_blocks)) - (LENGTH sd.cs_blocks + 2) = 0`
    by decide_tac >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >> strip_tac >>
  rpt (goal_assum $ drule_at Any) >> simp[] >>
  strip_tac >> drule fresh_label_output_inj >> simp[]
QED

Theorem create_result_check_layout:
  compile_check_create_result created T sd = (result,sb) /\
  fn_has_code sd sb func ==>
  ?cb fb fail j.
    sb.cs_current_insts = [] /\
    lookup_block sd.cs_current_bb func.fn_blocks = SOME cb /\
    cb.bb_instructions = sd.cs_current_insts ++ [j] /\
    j.inst_opcode = JNZ /\
    j.inst_operands = [created; Label sb.cs_current_bb; Label fail] /\
    lookup_block fail func.fn_blocks = SOME fb /\
    MAP (\i. i.inst_opcode) fb.bb_instructions =
      [RETURNDATASIZE;ALLOCA;RETURNDATACOPY;REVERT]
Proof
  metis_tac[create_result_check_layout_distinct]
QED

Theorem create_result_tail_branch:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode = JNZ /\ i.inst_operands = [created;Label yes;Label no] /\
  (!b. MEM b func.fn_blocks ==> phi_prefix_length b.bb_instructions = 0) /\
  gas_origin_edge F explicit ctx func s ms (OK t) ==>
  t.vs_inst_idx = 0 /\ (t.vs_current_bb = yes \/ t.vs_current_bb = no)
Proof
  strip_tac >>
  `step_inst_base i s =
    case eval_operand created s of
      NONE => Error "undefined condition"
    | SOME w => if w <> 0w then OK (jump_to yes s) else OK (jump_to no s)` by
      simp[step_inst_base_def] >>
  drule_all create_ok_edge_pc >>
  simp[is_terminator_def] >> strip_tac >>
  gvs[jump_to_def, AllCaseEqs()] >> metis_tac[venomExecProofsTheory.lookup_block_MEM]
QED

Theorem create_result_tail_revert:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\ i.inst_opcode = REVERT ==>
  ~gas_origin_edge F explicit ctx func s ms (OK t)
Proof
  strip_tac >> strip_tac >> drule_all create_ok_edge_pc >>
  simp[is_terminator_def] >> gen_tac >> disch_tac >>
  drule_at (Pos last) venomExecProofsTheory.step_inst_base_ok_terminator_jump >>
  simp[is_terminator_def]
QED

Theorem create_result_tail_fail_step:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  MAP (\i. i.inst_opcode) bb.bb_instructions =
    [RETURNDATASIZE;ALLOCA;RETURNDATACOPY;REVERT] /\
  s.vs_inst_idx < 4 /\
  gas_origin_edge F explicit ctx func s ms (OK t) ==>
  t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx < 4
Proof
  strip_tac >>
  `LENGTH bb.bb_instructions = 4` by
    (qpat_x_assum `MAP _ _ = _` (mp_tac o AP_TERM ``LENGTH : opcode list -> num``) >> simp[]) >>
  `get_instruction bb s.vs_inst_idx = SOME (EL s.vs_inst_idx bb.bb_instructions)` by
    simp[get_instruction_def] >>
  `EL s.vs_inst_idx (MAP (\i. i.inst_opcode) bb.bb_instructions) =
    (EL s.vs_inst_idx bb.bb_instructions).inst_opcode` by simp[EL_MAP] >>
  qabbrev_tac `i = EL s.vs_inst_idx bb.bb_instructions` >>
  Cases_on `s.vs_inst_idx = 3`
  >- (`i.inst_opcode = REVERT` by gvs[] >> metis_tac[create_result_tail_revert]) >>
  `~is_terminator i.inst_opcode` by
    (`s.vs_inst_idx = 0 \/ s.vs_inst_idx = 1 \/ s.vs_inst_idx = 2` by decide_tac >>
     gvs[is_terminator_def]) >>
  drule_all create_ok_edge_pc >> simp[] >> strip_tac >> simp[]
QED

Theorem create_result_tail_dispatch_code:
  cs_extends sa sc /\ emit_op opc ops sc = (created,sd) /\
  compile_check_create_result created rof sd = (result,sb) /\
  fn_has_code sa sb func ==>
  sd.cs_current_bb = sc.cs_current_bb /\
  LENGTH sd.cs_current_insts = SUC (LENGTH sc.cs_current_insts) /\
  fn_has_code sd sb func /\
  ?cb i. lookup_block sc.cs_current_bb func.fn_blocks = SOME cb /\
    get_instruction cb (LENGTH sc.cs_current_insts) = SOME i /\ i.inst_opcode = opc
Proof
  strip_tac >>
  `cs_extends sc sd` by metis_tac[ci_mono_def, ci_mono_emit_op, SND] >>
  `cs_extends sd sb` by
    metis_tac[externalEntryShapeTheory.compile_check_create_result_labels, SND] >>
  `fn_has_code sc sd func /\ fn_has_code sd sb func` by
    metis_tac[fn_has_code_mid, cs_extends_trans, cs_extends_refl] >>
  drule loweringShapeRulesTheory.emit_op_facts >> strip_tac >> simp[ADD1] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[venomInstTheory.mk_inst_def]
QED

Theorem create_result_marked_invariant:
  RTC (create_marked_edge E) (u,left) (v,right) /\ P u /\
  (!x ms y. P x /\ E x ms y ==> P y) ==> P v
Proof
  strip_tac >>
  `!x y. RTC (create_marked_edge E) x y ==> P (FST x) ==> P (FST y)`
    suffices_by (disch_then (qspecl_then [`(u,left)`,`(v,right)`] mp_tac) >> simp[]) >>
  ho_match_mp_tac RTC_INDUCT >>
  simp[FORALL_PROD, create_marked_edge_def] >> metis_tac[]
QED
