(* Halt suffixes at supplied offsets, shared by both symbolic modes. *)
Theory symControlHaltOwn
Ancestors
  symControlTerminalSafetyOwn asmSymBridge[qualified,ignore_grammar]
  codegenSymRel codegenSymOwnRel fnFrameTerminalHalt fnFrameTerminalPrep
  genBlockSim asmSymOwnCode asmSplice frameRel contextCodegenRel
  unitShapeDefs stackPlanGen stackPlanTypes planExec asmSem asmSymSem
  venomExecSemantics venomInst venomState frameViewFacts genFrameSim emitSim

val halt_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val halt_bridge_result_tm = let
  val body = lhs (concl asmSymBridgeTheory.asm_sym_step_rel_core_canonical)
  val rel = ``asm_sym_rel p env``
  val r = mk_var ("R", type_of rel)
  val body = subst [rel |-> r] body
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars body) of
      [v] => v | _ => raise Fail ("missing result parameter " ^ n)
in list_mk_abs ([r, named "sr", named "cr"], body) end;
val _ = Parse.temp_overload_on ("bridge_core", halt_bridge_core_tm);
val _ = Parse.temp_overload_on ("bridge_result", halt_bridge_result_tm);

Theorem terminal_return_prepared_step:
  !cp.
  inst.inst_opcode = RETURN /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  asm_block_at prog mid.as_pc [AsmOp name] /\
  context_memory_rel cp vs.vs_memory mid.as_memory /\
  source_memory_reads_disjoint cp inst vs /\
  venom_asm_terminal_rel vs mid /\
  (!values. eval_operands (REVERSE (compute_operands inst)) vs = SOME values ==>
    mid.as_stack = values ++ DROP (LENGTH (compute_operands inst)) mid.as_stack) /\
  step_inst fuel ctx inst vs = Halt vs' ==>
  ?out. asm_steps lo o2pc prog 1 mid = AsmHalt out /\
    venom_asm_terminal_rel vs' out
Proof
  gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `step_inst _ _ _ _ = Halt _` mp_tac >>
  simp[Once step_inst_def, step_inst_base_def, AllCaseEqs()] >> strip_tac >>
  `inst.inst_operands = [off_op; sz_op]` by metis_tac[] >>
  `name = "RETURN" /\ mid.as_stack = off :: sz :: DROP 2 mid.as_stack` by
    gvs[asmIRTheory.venom_to_evm_name_def, compute_operands_def,
        python_stack_operands_def, ir_specific_operand_order_def, eval_operands_def] >>
  `MEM (w2n off, w2n sz) (source_memory_read_ranges inst vs)` by
    simp[source_memory_read_ranges_def, memory_range_of_operands_def] >>
  drule_all fnFrameTerminalPrepTheory.context_source_payload_agree >> disch_tac >>
  metis_tac[fnFrameTerminalHaltTheory.terminal_return_payload_step]
QED

Theorem terminal_selfdestruct_prepared_step:
  inst.inst_opcode = SELFDESTRUCT /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  asm_block_at prog mid.as_pc [AsmOp name] /\
  venom_asm_terminal_rel vs mid /\ mid.as_call_ctx = vs.vs_call_ctx /\
  (!values. eval_operands (REVERSE (compute_operands inst)) vs = SOME values ==>
    mid.as_stack = values ++ DROP (LENGTH (compute_operands inst)) mid.as_stack) /\
  step_inst fuel ctx inst vs = Halt vs' ==>
  ?out. asm_steps lo o2pc prog 1 mid = AsmHalt out /\
    venom_asm_terminal_rel vs' out
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `step_inst _ _ _ _ = Halt _` mp_tac >>
  simp[Once step_inst_def, step_inst_base_def, AllCaseEqs()] >> strip_tac
  >~ [`eval_operands _ _ = NONE`] >- gvs[eval_operands_def] >>
  `name = "SELFDESTRUCT" /\ mid.as_stack = addr :: DROP 1 mid.as_stack` by
    gvs[asmIRTheory.venom_to_evm_name_def, compute_operands_def,
        python_stack_operands_def, ir_specific_operand_order_def, eval_operands_def] >>
  qpat_x_assum `name = _` SUBST_ALL_TAC >>
  metis_tac[SIMP_RULE bool_ss [COND_RATOR, combinTheory.I_THM]
              fnFrameTerminalHaltTheory.terminal_selfdestruct_rel_step]
QED

Theorem terminal_halt_prepared_step:
  !cp.
  (inst.inst_opcode = STOP \/ inst.inst_opcode = RETURN \/
   inst.inst_opcode = SELFDESTRUCT) /\ inst_wf inst /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  asm_block_at prog mid.as_pc [AsmOp name] /\
  context_memory_rel cp vs.vs_memory mid.as_memory /\
  source_memory_reads_disjoint cp inst vs /\
  venom_asm_terminal_rel vs mid /\ mid.as_call_ctx = vs.vs_call_ctx /\
  (!values. eval_operands (REVERSE (compute_operands inst)) vs = SOME values ==>
    mid.as_stack = values ++ DROP (LENGTH (compute_operands inst)) mid.as_stack) /\
  step_inst fuel ctx inst vs = Halt vs' ==>
  ?out. asm_steps lo o2pc prog 1 mid = AsmHalt out /\
    venom_asm_terminal_rel vs' out
Proof
  gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `_ \/ _ \/ _` strip_assume_tac
  >- (gvs[Once step_inst_def, step_inst_base_def, asmIRTheory.venom_to_evm_name_def] >>
      metis_tac[genBlockSimTheory.terminal_stop_step])
  >- metis_tac[terminal_return_prepared_step]
  >> metis_tac[terminal_selfdestruct_prepared_step]
QED

Theorem terminal_halt_operand_values:
  (inst.inst_opcode = RETURN \/ inst.inst_opcode = SELFDESTRUCT) /\ inst_wf inst /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  step_inst fuel ctx inst vs = Halt vs' ==>
  ?args. eval_operands inst.inst_operands vs = SOME args /\
    eval_operands (REVERSE (compute_operands inst)) vs = SOME args /\
    LENGTH args = asm_op_arity name
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `_ \/ _` strip_assume_tac >>
  fs[venomWfTheory.inst_wf_def, asmIRTheory.venom_to_evm_name_def] >>
  gvs[listTheory.LENGTH_EQ_NUM_compute, compute_operands_def,
      python_stack_operands_def, ir_specific_operand_order_def] >>
  qpat_x_assum `step_inst _ _ _ _ = Halt _` mp_tac >>
  (simp[Once step_inst_def] >>
  simp[step_inst_base_opcode_eqs, AllCaseEqs(), eval_operands_def,
       asm_op_arity_def, asm_op_arity_table_def]) >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem sym_halt_prepared_step_mode_conditional:
  !cp.
  (!cs ss ai cr.
    bridge_core lo code_ok cs ss /\ asm_block_at prog cs.as_pc [ai] /\
    asm_step lo (build_offset_to_pc prog) ai cs = cr /\
    (!e. (if allow_own then sym_step_own prog env own ai ss
          else sym_step prog env ai ss) <> SymBad e) /\
    ((?s. cr = AsmHalt s) \/ (?s. cr = AsmRevert s) \/ (?s. cr = AsmFault s)) ==>
    bridge_result (bridge_core lo code_ok)
      (if allow_own then sym_step_own prog env own ai ss else sym_step prog env ai ss) cr) /\
  (inst.inst_opcode = STOP \/ inst.inst_opcode = RETURN \/
   inst.inst_opcode = SELFDESTRUCT) /\ inst_wf inst /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  asm_static_wf prog /\ bridge_core lo code_ok mid ss_mid /\
  asm_block_at prog mid.as_pc [AsmOp name] /\
  (!values. eval_operands (REVERSE (compute_operands inst)) vs = SOME values ==>
    ?suffix. ss_mid.sym_stack = MAP Val values ++ suffix) /\
  (!b. b IN FDOM ss_mid.sym_mem_labels ==> context_spill_byte cp b) /\
  source_memory_reads_disjoint cp inst vs /\
  step_inst fuel ctx inst vs = Halt vs' /\
  asm_steps lo (build_offset_to_pc prog) prog 1 mid = AsmHalt out ==>
  sym_terminal (sym_steps_mode allow_own prog env own 1 ss_mid)
Proof
  gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `asm_step lo (build_offset_to_pc prog) (AsmOp name) mid = AsmHalt out` by
    (qpat_x_assum `asm_steps _ _ _ 1 _ = _` mp_tac >>
     pure_rewrite_tac[arithmeticTheory.ONE, asm_steps_def] >>
     gvs[asm_block_at_def, AllCaseEqs()]) >>
  Cases_on `inst.inst_opcode = STOP`
  >- (`name = "STOP"` by gvs[asmIRTheory.venom_to_evm_name_def] >>
      qpat_x_assum `name = _` SUBST_ALL_TAC >>
      irule sym_terminal_opcode_transfer_mode_conditional >>
      conj_tac >- simp[] >>
      qexistsl [`[]`, `code_ok`, `AsmHalt out`, `mid`, `lo`, `"STOP"`, `ss_mid.sym_stack`] >>
      asm_rewrite_tac[] >>
      simp[asm_op_arity_def, asm_op_arity_table_def,
           asm_op_mem_reads_def, log_table_def, mem_labels_hit_def]) >>
  drule_at (Pat `step_inst _ _ _ _ = Halt _`) terminal_halt_operand_values >>
  disch_then (qspec_then `name` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `MEM inst.inst_opcode [STOP; RETURN; SELFDESTRUCT; REVERT; INVALID;
    CREATE; CREATE2; RETURNDATACOPY]` by (simp[] >> metis_tac[]) >>
  drule_all terminal_source_memory_reads_safe >> disch_tac >>
  `MEM name ["STOP"; "RETURN"; "REVERT"; "INVALID"; "SELFDESTRUCT";
    "CREATE"; "CREATE2"; "RETURNDATACOPY"]` by
    gvs[asmIRTheory.venom_to_evm_name_def] >>
  `?tail. ss_mid.sym_stack = MAP Val args ++ tail` by metis_tac[] >>
  irule sym_terminal_opcode_transfer_mode_conditional >>
  conj_tac >- simp[] >>
  qexistsl [`args`, `code_ok`, `AsmHalt out`, `mid`, `lo`, `name`, `tail`] >>
  asm_rewrite_tac[] >> simp[]
QED
