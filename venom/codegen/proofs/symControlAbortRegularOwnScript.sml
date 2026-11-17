(* Regular terminal aborts, parameterized by the bridge code predicate. *)
Theory symControlAbortRegularOwn
Ancestors
  symControlTerminalPrepareOwn symControlTerminalSafetyOwn symFrameControlFacts codegenSymRel codegenSymOwnRel
  asmSymBridge[qualified,ignore_grammar] asmSymOwnCode asmSplice asmSem asmSymSem
  frameRel codegenRel contextCodegenRel unitShapeDefs stackPlanGen stackPlanTypes planExec
  venomExecSemantics venomInst venomState frameViewFacts genFrameSim emitSim
  fnFrameDeepAbort genBlockSim fnFrameBoundaryInvoke dfgDefs

val regular_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val regular_bridge_result_tm = let
  val body = lhs (concl asmSymBridgeTheory.asm_sym_step_rel_core_canonical)
  val rel = ``asm_sym_rel p env``
  val r = mk_var ("R", type_of rel)
  val body = subst [rel |-> r] body
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars body) of
      [v] => v | _ => raise Fail ("missing result parameter " ^ n)
in list_mk_abs ([r, named "sr", named "cr"], body) end;
val _ = Parse.temp_overload_on ("bridge_core", regular_bridge_core_tm);
val _ = Parse.temp_overload_on ("bridge_result", regular_bridge_result_tm);
val _ = Parse.temp_overload_on ("terminal_transfer", ``\lo code_ok p env own allow_own.
  !cs ss ai cr.
    bridge_core lo code_ok cs ss /\ asm_block_at p cs.as_pc [ai] /\
    asm_step lo (build_offset_to_pc p) ai cs = cr /\
    (!e. (if allow_own then sym_step_own p env own ai ss
          else sym_step p env ai ss) <> SymBad e) /\
    ((?s. cr = AsmHalt s) \/ (?s. cr = AsmRevert s) \/ (?s. cr = AsmFault s)) ==>
    bridge_result (bridge_core lo code_ok)
      (if allow_own then sym_step_own p env own ai ss else sym_step p env ai ss) cr``);

Theorem regular_abort_operand_order:
  MEM inst.inst_opcode [REVERT; INVALID; CREATE; CREATE2; RETURNDATACOPY] /\
  inst_wf inst ==>
  compute_operands inst = REVERSE inst.inst_operands
Proof
  simp[listTheory.MEM] >> strip_tac >>
  gvs[compute_operands_def, python_stack_operands_def,
      ir_specific_operand_order_def, venomWfTheory.inst_wf_def,
      listTheory.LENGTH_EQ_NUM_compute] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  rename1 `LENGTH t` >> Cases_on `t` >> gvs[]
QED

Theorem regular_abort_source_arguments:
  MEM inst.inst_opcode [REVERT; INVALID; CREATE; CREATE2; RETURNDATACOPY] /\
  inst_wf inst /\ inst.inst_opcode <> INVALID /\
  step_inst fuel ctx inst vs = Abort a vs' ==>
  ?args. eval_operands inst.inst_operands vs = SOME args
Proof
  Cases_on `vs.vs_call_ctx.cc_static /\ MEM inst.inst_opcode [CREATE; CREATE2]`
  >- (strip_tac >>
      qpat_x_assum `vs.vs_call_ctx.cc_static /\ _` strip_assume_tac >>
      `MEM inst.inst_opcode [SSTORE; TSTORE; SELFDESTRUCT; CALL; CREATE; CREATE2]` by
        gvs[listTheory.MEM] >>
      drule_all step_inst_static_abort >> metis_tac[]) >>
  simp[listTheory.MEM] >> strip_tac >> gvs[]
  >- (drule_all genBlockSimTheory.step_inst_revert_abort >>
      strip_tac >> simp[eval_operands_def])
  >- (drule_all genBlockSimTheory.step_inst_create_abort >>
      strip_tac >> simp[eval_operands_def])
  >- (drule_all genBlockSimTheory.step_inst_create2_abort >>
      strip_tac >> simp[eval_operands_def])
  >> drule_all genBlockSimTheory.step_inst_returndatacopy_abort >>
     strip_tac >> simp[eval_operands_def]
QED

Theorem regular_abort_prepared_step:
  MEM inst.inst_opcode [REVERT; CREATE; CREATE2; RETURNDATACOPY] /\
  inst_wf inst /\
  step_inst fuel ctx inst vs = Abort a vs' /\
  eval_operands inst.inst_operands vs = SOME args /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  cs.as_stack = args ++ tail /\ cs.as_call_ctx = vs.vs_call_ctx /\
  venom_asm_terminal_rel vs cs ==>
  LENGTH args = asm_op_arity name /\
  ((?out. asm_step lo o2pc (AsmOp name) cs = AsmRevert out) \/
   (?out. asm_step lo o2pc (AsmOp name) cs = AsmFault out))
Proof
  Cases_on `vs.vs_call_ctx.cc_static /\ MEM inst.inst_opcode [CREATE; CREATE2]`
  >- (strip_tac >>
      gvs[listTheory.MEM, asmIRTheory.venom_to_evm_name_def,
          venomWfTheory.inst_wf_def, listTheory.LENGTH_EQ_NUM_compute,
          eval_operands_def, AllCaseEqs(), asm_op_arity_def, asm_op_arity_table_def,
          venom_asm_terminal_rel_def, asm_step_def, asm_step_op_def,
          asm_step_arith_def, asm_step_compare_def, asm_step_bitwise_def,
          asm_step_memory_def, asm_step_control_def, asm_step_extcall_def,
          asm_exec_create_def, asm_exec_create2_def]) >>
  simp[listTheory.MEM] >> strip_tac >> gvs[]
  >- (drule_all genBlockSimTheory.step_inst_revert_abort >> strip_tac >>
      gvs[eval_operands_def, asmIRTheory.venom_to_evm_name_def,
          asm_op_arity_def, asm_op_arity_table_def,
          stackOpAsmSimTheory.asm_step_revert, asm_revert_op_def])
  >- (drule_all genBlockSimTheory.step_inst_create_abort >> strip_tac >>
      gvs[eval_operands_def, asmIRTheory.venom_to_evm_name_def,
          asm_op_arity_def, asm_op_arity_table_def, asm_step_def, asm_step_op_def,
          asm_step_arith_def, asm_step_compare_def, asm_step_bitwise_def,
          asm_step_memory_def, asm_step_control_def, asm_step_extcall_def,
          asm_exec_create_def])
  >- (drule_all genBlockSimTheory.step_inst_create2_abort >> strip_tac >>
      gvs[eval_operands_def, asmIRTheory.venom_to_evm_name_def,
          asm_op_arity_def, asm_op_arity_table_def, asm_step_def, asm_step_op_def,
          asm_step_arith_def, asm_step_compare_def, asm_step_bitwise_def,
          asm_step_memory_def, asm_step_control_def, asm_step_extcall_def,
          asm_exec_create2_def])
  >> drule_all genBlockSimTheory.step_inst_returndatacopy_abort >> strip_tac >>
     gvs[eval_operands_def, asmIRTheory.venom_to_evm_name_def,
         asm_op_arity_def, asm_op_arity_table_def, asm_step_def, asm_step_op_def,
         asm_step_arith_def, asm_step_compare_def, asm_step_bitwise_def,
         asm_step_memory_def, asm_step_control_def, asm_step_extcall_def,
         asm_step_copy_def, asm_returndatacopy_def, venom_asm_terminal_rel_def]
QED

Theorem sym_invalid_prepared_terminal_mode_conditional:
  terminal_transfer lo code_ok prog env own allow_own /\
  asm_static_wf prog /\ bridge_core lo code_ok cs ss /\
  asm_block_at prog cs.as_pc [AsmOp "INVALID"] ==>
  sym_terminal (sym_steps_mode allow_own prog env own 1 ss)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule sym_terminal_opcode_transfer_mode_conditional >>
  conj_tac >- asm_rewrite_tac[] >>
  qexistsl [`[]`, `code_ok`, `AsmFault (cs with as_returndata := [])`, `cs`,
             `lo`, `"INVALID"`, `ss.sym_stack`] >>
  gvs[asm_op_arity_def, asm_op_arity_table_def, asm_op_mem_reads_def,
      asmSemTheory.log_table_def, mem_labels_hit_def,
      stackOpAsmSimTheory.asm_step_invalid] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  qexists `m` >> simp[]
QED

Theorem sym_regular_abort_prepared_terminal_mode_conditional:
  !cp.
  terminal_transfer lo code_ok prog env own allow_own /\
  MEM inst.inst_opcode [REVERT; CREATE; CREATE2; RETURNDATACOPY] /\
  inst_wf inst /\ step_inst fuel ctx inst vs = Abort a vs' /\
  eval_operands inst.inst_operands vs = SOME args /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  cs.as_stack = args ++ tail /\ cs.as_call_ctx = vs.vs_call_ctx /\
  venom_asm_terminal_rel vs cs /\ ss.sym_stack = MAP Val args ++ suffix /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) /\
  source_memory_reads_disjoint cp inst vs /\
  asm_static_wf prog /\ bridge_core lo code_ok cs ss /\
  asm_block_at prog cs.as_pc [AsmOp name] ==>
  sym_terminal (sym_steps_mode allow_own prog env own 1 ss)
Proof
  gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM inst.inst_opcode [STOP; RETURN; SELFDESTRUCT; REVERT; INVALID;
      CREATE; CREATE2; RETURNDATACOPY] /\
   MEM name ["STOP"; "RETURN"; "REVERT"; "INVALID"; "SELFDESTRUCT";
      "CREATE"; "CREATE2"; "RETURNDATACOPY"]` by
    gvs[listTheory.MEM, asmIRTheory.venom_to_evm_name_def] >>
  drule_all terminal_source_memory_reads_safe >> strip_tac >>
  drule_all regular_abort_prepared_step >>
  disch_then (qspecl_then [`build_offset_to_pc prog`, `lo`] strip_assume_tac) >>
  irule sym_terminal_opcode_transfer_mode_conditional >>
  (conj_tac >- asm_rewrite_tac[]) >>
  goal_assum (drule_at (Pat `asm_step _ _ _ _ = _`)) >>
  qexistsl [`args`, `code_ok`, `suffix`] >>
  asm_rewrite_tac[] >> simp[]
QED

Theorem sym_regular_abort_arranged_terminal_mode_conditional:
  !cp.
  terminal_transfer lo code_ok prog env own allow_own /\
  MEM inst.inst_opcode [REVERT; INVALID; CREATE; CREATE2; RETURNDATACOPY] /\
  inst_wf inst /\ step_inst fuel ctx inst vs = Abort a vs' /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\ opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  label_positions_ok inst /\
  EVERY (\op. op <> dead_stack_marker) (compute_operands inst) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  arranged.ps_stack = tail ++ compute_operands inst /\
  venom_asm_rel lo arranged (frame_view fn ra vs with vs_memory := m) mid /\
  venom_asm_terminal_rel vs (mid with as_stack := mid.as_stack ++ rest) /\
  bridge_core lo code_ok (mid with as_stack := mid.as_stack ++ rest) ss /\
  sym_kinds_ok cp fn ret srest arranged ss /\
  source_memory_reads_disjoint cp inst vs /\ asm_static_wf prog /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  asm_block_at prog mid.as_pc [AsmOp name] ==>
  sym_terminal (sym_steps_mode allow_own prog env own 1 ss)
Proof
  gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `sym_kinds_ok cplan fn ret srest arranged ss` >>
  Cases_on `inst.inst_opcode = INVALID`
  >- (irule sym_invalid_prepared_terminal_mode_conditional >>
      (conj_tac >- asm_rewrite_tac[]) >>
      qexistsl [`code_ok`, `mid with as_stack := mid.as_stack ++ rest`, `lo`] >>
      gvs[asmIRTheory.venom_to_evm_name_def] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
      goal_assum (drule_at (Pat `LENGTH _ = LENGTH mid.as_memory`)) >> simp[]) >>
  drule_all regular_abort_source_arguments >> strip_tac >>
  `compute_operands inst = REVERSE inst.inst_operands` by
    metis_tac[regular_abort_operand_order] >>
  `MEM inst.inst_opcode [STOP; RETURN; SELFDESTRUCT; REVERT; ASSERT;
      ASSERT_UNREACHABLE; INVALID; CREATE; CREATE2; RETURNDATACOPY] /\
   eval_operands (REVERSE (compute_operands inst)) vs = SOME args` by
    gvs[listTheory.MEM] >>
  drule_all terminal_arranged_word_stack_mode >> strip_tac >>
  `MEM inst.inst_opcode [REVERT; CREATE; CREATE2; RETURNDATACOPY] /\
   (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cplan b)` by
    ((conj_tac >- metis_tac[listTheory.MEM]) >> fs[sym_kinds_ok_def]) >>
  `mid.as_call_ctx = vs.vs_call_ctx` by fs[venom_asm_rel_def, frame_view_def] >>
  irule sym_regular_abort_prepared_terminal_mode_conditional >>
  (conj_tac >- asm_rewrite_tac[]) >>
  goal_assum (drule_at (Pat `source_memory_reads_disjoint _ _ _`)) >>
  goal_assum (drule_at (Pat `step_inst _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `venom_asm_terminal_rel _ _`)) >>
  qexistsl [`args`, `code_ok`, `lo`, `name`, `suffix`,
    `DROP (LENGTH (compute_operands inst)) (mid.as_stack ++ rest)`] >>
  simp[IgnAsm `mid.as_stack ++ rest = _`] >>
  conj_tac >- (qpat_x_assum `terminal_transfer _ _ _ _ _ _` mp_tac >> simp[]) >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  qpat_x_assum `mid.as_stack ++ rest = _` mp_tac >> simp[]
QED

Theorem sym_abort_regular_terminal_exists_mode_kernel:
  !fuel ctx cp lo o2pc prog lv dfg cfg fn inst nl halting term label
   base ps vs st ops final r ra rest mem0 env ret srest labs0 ss a vs'.
  terminal_transfer lo code_ok prog env own allow_own /\
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  o2pc = build_offset_to_pc prog /\
  MEM inst.inst_opcode [REVERT; INVALID; CREATE; CREATE2; RETURNDATACOPY] /\
  source_memory_reads_disjoint cp inst vs /\
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\ inst_wf inst /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked base ps /\ codegen_ready_fn fn /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs st /\
  generate_inst_plan lv dfg cfg fn inst nl halting term label ps = SOME (ops,final) /\
  asm_block_at prog st.as_pc (execute_plan cp.cp_initial_fmp ops) /\
  dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ asm_static_wf prog /\
  bridge_core lo code_ok st ss /\ sym_kinds_ok cp fn ret srest ps ss /\
  (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
    FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
  (fn_has_retpc fn ==> MEM (AsmLabel ret) prog) /\
  step_inst fuel ctx inst vs = Abort a vs' ==>
  ?m. sym_terminal (sym_steps_mode allow_own prog env own m ss)
Proof
  rpt gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  rename1 `fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st` >>
  `?name. venom_to_evm_name inst.inst_opcode = SOME name` by
    gvs[listTheory.MEM, asmIRTheory.venom_to_evm_name_def] >>
  `inst.inst_opcode <> INVOKE /\ ~is_commutative inst.inst_opcode /\
   generate_regular_inst_plan lv dfg cfg fn inst nl halting term label ps = (ops,final)` by
    gvs[listTheory.MEM, venomEffectsTheory.is_commutative_def, generate_inst_plan_def,
        is_pre_codegen_opcode_def, is_param_opcode_def,
        is_unlowered_fmp_opcode_def, is_raw_fmp_opcode_def,
        is_unlowered_internal_call_opcode_def] >>
  `ssa_form fn` by fs[codegen_ready_fn_def] >>
  drule_all sym_regular_abort_frame_prefix_deep_mode_conditional >>
  disch_then (qx_choose_then `pre` (qx_choose_then `arranged`
    (qx_choose_then `mid` (qx_choose_then `ss_mid` assume_tac)))) >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `label_positions_ok inst` by
    (fs[fn_shape_ok_def, listTheory.EVERY_MEM, inst_shape_ok_def] >> metis_tac[]) >>
  `EVERY (\op. op <> dead_stack_marker) (compute_operands inst)` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `sym_terminal (sym_steps_mode allow_own prog env own 1 ss_mid)` by
    (drule_all sym_regular_abort_arranged_terminal_mode_conditional >> simp[]) >>
  qexists `LENGTH (execute_plan cplan.cp_initial_fmp pre) + 1` >>
  simp[sym_steps_mode_add]
QED
