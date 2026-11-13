(*
 * gen_inst_frame_sim_deep: genFrameSim's gen_inst_frame_sim for an instruction whose step is OK, with
 * operands at any stack depth, repeated dead_stack_marker slots
 * (generated_plan_state_wf_marked) and only an address bound on the
 * plan's spill and restore offsets.  fnFrameDeep collects it with the
 * other instruction frame lemmas the block induction composes.
 *
 * TOP-LEVEL:
 *   gen_inst_frame_sim_deep
 *)

Theory fnFrameDeepInst
Ancestors
  deepInstSim asmFrame deepResidualSim fnPlanPrefix genFrameSim frameRel contextCodegenRel
  codegenRel blockSimHelpers unitShapeDefs genBlockSim mixedPrefixSim
  stackPlanGen stackPlanTypes planExec asmSem venomExecSemantics venomState
  venomInst fcgDefs livenessDefs dfgDefs cfgDefs

Theorem frame_inst_local_setup:
  !ctx cp lo fn ra rest mem0 ps vs ast r final inst fuel vs'.
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs ast /\
  MEM r cp.cp_regions /\ r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  inst.inst_opcode <> INVOKE /\ ~is_param_opcode inst.inst_opcode /\
  ~is_terminator inst.inst_opcode /\ codegen_ready_fn fn /\ opaque_use_ok fn /\
  MEM inst (fn_insts fn) /\ source_memory_reads_disjoint cp inst vs /\
  context_source_memory_writes_disjoint cp inst vs /\
  step_inst fuel ctx inst vs = OK vs' ==>
  ?top m'. ast.as_stack = top ++ rest /\
    venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := ast.as_memory)
      (ast with as_stack := top) /\
    step_inst fuel ctx inst (frame_view fn ra vs with vs_memory := ast.as_memory) =
      OK (frame_view fn ra vs' with vs_memory := m') /\
    (!i. read_byte i ast.as_memory = read_byte i vs.vs_memory ==>
      read_byte i m' = read_byte i vs'.vs_memory) /\
    (!i. context_spill_byte cp i ==> read_byte i m' = read_byte i ast.as_memory) /\
    inst_memory_safe final.ps_alloc inst
      (frame_view fn ra vs with vs_memory := ast.as_memory)
      (frame_view fn ra vs' with vs_memory := m') /\
    EVERY (\(off,len). len = 0 \/ off + len <= final.ps_alloc.sa_spill_base \/
      final.ps_alloc.sa_next_offset <= off)
      (source_memory_read_ranges inst (frame_view fn ra vs with vs_memory := ast.as_memory))
Proof
  rpt gen_tac >> strip_tac >> rename1 `MEM r cplan.cp_regions` >>
  qpat_assum `fn_frame_inv _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [fn_frame_inv_def]) >>
  `venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := ast.as_memory)
    (ast with as_stack := top)` by
    (drule context_venom_asm_rel_local >> simp[]) >>
  `context_memory_rel cplan vs.vs_memory ast.as_memory` by
    fs[context_venom_asm_rel_def, frame_view_def] >>
  `?m'. step_inst fuel ctx inst
      (frame_view fn ra vs with vs_memory := ast.as_memory) =
      OK (frame_view fn ra vs' with vs_memory := m') /\
    (!i. read_byte i ast.as_memory = read_byte i vs.vs_memory ==>
      read_byte i m' = read_byte i vs'.vs_memory) /\
    (!i. context_spill_byte cplan i ==> read_byte i m' = read_byte i ast.as_memory) /\
    inst_memory_safe final.ps_alloc inst
      (frame_view fn ra vs with vs_memory := ast.as_memory)
      (frame_view fn ra vs' with vs_memory := m')` by
    (irule frame_view_safe_step >> goal_assum (drule_at Any) >>
     simp[] >> qexists_tac `r` >> simp[]) >>
  qexistsl_tac [`top`, `m'`] >> simp[] >>
  simp[source_read_ranges_frame_view] >>
  irule (SRULE [arithmeticTheory.ADD_COMM] context_reads_local) >>
  qexistsl_tac [`cplan`, `r`] >> simp[]
QED

Theorem frame_inst_local_lift:
  !ctx cp lo fn ra rest mem0 ps vs ast r final inst fuel vs' top o2pc prog n out m'.
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs ast /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst vs = OK vs' /\
  ast.as_stack = top ++ rest /\
  asm_steps lo o2pc prog n (ast with as_stack := top) = AsmOK out /\
  venom_asm_rel lo final (frame_view fn ra vs' with vs_memory := m') out /\
  (!i. read_byte i ast.as_memory = read_byte i vs.vs_memory ==>
    read_byte i m' = read_byte i vs'.vs_memory) /\
  (!i. context_spill_byte cp i ==> read_byte i m' = read_byte i ast.as_memory) ==>
  asm_steps lo o2pc prog n ast =
    AsmOK (out with as_stack := out.as_stack ++ rest) /\
  fn_frame_inv ctx cp lo fn ra rest mem0 final vs'
    (out with as_stack := out.as_stack ++ rest)
Proof
  rpt gen_tac >> strip_tac >> rename1 `MEM r cplan.cp_regions` >>
  `~vs'.vs_halted` by
    (`step_inst_base inst vs = OK vs'` by
       (qpat_x_assum `step_inst fuel ctx inst vs = OK vs'` mp_tac >>
        simp[step_inst_non_invoke]) >>
     drule venomInstProofs1Theory.step_inst_base_preserves_all >>
     gvs[fn_frame_inv_def]) >>
  `n2w cplan.cp_initial_fmp = vs'.vs_initial_fmp` by
    (qpat_assum `step_inst fuel ctx inst vs = OK vs'`
       (mp_then Any mp_tac step_inst_non_invoke_preserves_initial_fmp) >>
     fs[fn_frame_inv_def]) >>
  conj_tac
  >- (`ast with as_stack := top ++ rest = ast` by
        simp[asmSemTheory.asm_state_component_equality] >>
      pop_assum (SUBST1_TAC o GSYM) >> irule asm_steps_frame >> simp[]) >>
  irule frame_local_result >> simp[] >> conj_tac
  >- (qexists_tac `r` >> simp[]) >>
  qexistsl_tac [`ast`, `m'`, `ps`, `vs`] >> simp[]
QED

(* gen_inst_frame_sim with any-depth ownership, generated_plan_state_wf_marked and an
   address bound on spill and restore offsets. *)
Theorem gen_inst_frame_sim_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\
    (* GAS is excluded: context_venom_asm_rel leaves GAS readings unrelated
       to Venom's GAS value.  The function-level proof handles GAS, as it
       does INVOKE. *)
    inst.inst_opcode <> GAS /\
    (* inst_wf doesn't fix the operand count of the read-only opcodes. *)
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    (* The context-level memory obligations (codegen_memory_obligations). *)
    source_memory_reads_disjoint cp inst vs /\
    context_source_memory_writes_disjoint cp inst vs /\
    (* Return-PC variables are only copied (unit_shape_ok's fn_shape_ok). *)
    opaque_use_ok fn /\
    ~is_param_opcode inst.inst_opcode /\
    (* The invariant's region clause for the output planner state. *)
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    ~is_terminator inst.inst_opcode /\
    (* Dischargeable at block level from codegen_ready_fn + MEM bb/inst *)
    inst_wf inst /\
    (* The EVM has LOG0 to LOG4 only; inst_wf allows larger topic counts. *)
    (inst.inst_opcode = LOG ==>
     ?tc args. inst.inst_operands = Lit tc :: args /\ w2n tc <= 4) /\
    (* ASSERT's failure branch pushes the shared revert label. *)
    (inst.inst_opcode = ASSERT ==> IS_SOME (FLOOKUP lo "revert")) /\
    (* EVM compatibility: DUP depth limit. Dischargeable from evm_compatible
       (LOG tc <= 4, INVOKE args bounded by fn arity). Pipeline obligation. *)
    LENGTH (compute_operands inst) <= 16 /\
    (* Stack depth after input emission >= operand count.
       Dischargeable from plan_state invariant (stack tracks emitted inputs). *)
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (* Every variable input must be owned by the planner: each is either
       on the stack at any depth or available from the spill map.
       generated_plan_state_wf_marked is structural and does not imply ownership. *)
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (* Label resolution: all label operands in label_offsets.
       Pipeline obligation from compute_label_offsets over full program. *)
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (* Labels defined in the instruction's own code resolve to their own
       positions (labels are unique in prog). *)
    (!lbl i. i < LENGTH (execute_plan cp.cp_initial_fmp ops) /\
             EL i (execute_plan cp.cp_initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (* Cross-layer operand evaluation agreement.  In particular, Label
       operands must agree between vs_labels and generated label offsets. *)
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op (frame_view fn ra vs) =
          operand_val (frame_view fn ra vs) lo op) /\
    (* DFG alias soundness: planner-equivalent operands denote the same
       runtime word under the current value state and label environment.
       This is an explicit pipeline obligation for alias-only reorder steps. *)
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val (frame_view fn ra vs) lo op =
             operand_val (frame_view fn ra vs) lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    (* SSA freshness: output variables not yet in plan state.
       Dischargeable from ssa_form + plan_state invariant
       (plan tracks defined vars, SSA ensures no redefinition). *)
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T)
                inst.inst_outputs) /\
    (* PHI soundness: stack-found phi var evaluates to resolved phi value.
       Dischargeable from block entry invariant: predecessor placed the
       resolved PHI value at the expected stack position. *)
    (!dist prev val_op.
       inst.inst_opcode = PHI /\
       stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
         ps.ps_stack = SOME dist /\
       vs.vs_prev_bb = SOME prev /\
       resolve_phi prev inst.inst_operands = SOME val_op ==>
       operand_val (frame_view fn ra vs) lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op (frame_view fn ra vs)) /\
    (* Spill well-formedness for prefix ops.
       Dischargeable: provable from generate_inst_plan output
       (plan generator produces spill-well-formed prefixes). *)
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    (* Restored spill offsets fit a PUSH (from assembly_target_safe at the
       program level). *)
    (!off. MEM (SORestore off) ops ==> off < dimword (:256)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        fn_frame_inv ctx cp lo fn ra rest mem0 ps' vs' as' /\
        as'.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >> rename1 `MEM r cplan.cp_regions` >>
  gen_tac >> strip_tac >>
  drule_all frame_inst_local_setup >> strip_tac >>
  `n2w cplan.cp_initial_fmp = vs.vs_initial_fmp` by
    fs[fn_frame_inv_def] >>
  `~MEM inst.inst_opcode [JMP; JNZ; DJMP]` by
    (simp[] >> rpt conj_tac >> strip_tac >> gvs[is_terminator_def]) >>
  fs[] >>
  drule_all
    (SRULE [venomMemPropsTheory.eval_operand_with_memory, operand_val_memory_update,
      frame_view_control_fields, arithmeticTheory.ADD_COMM]
    (Q.INST [`initial_fmp` |-> `cplan.cp_initial_fmp`,
       `vs` |-> `frame_view fn ra vs with vs_memory := as.as_memory`,
       `as` |-> `as with as_stack := top`] (SPEC_ALL gen_inst_ok_sim_marked))) >>
  strip_tac >> rename1 `venom_asm_rel _ ps' _ out` >>
  qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  qpat_x_assum `o2pc = _` SUBST_ALL_TAC >>
  drule_all frame_inst_local_lift >> strip_tac >>
  qexistsl_tac [`n`, `out with as_stack := out.as_stack ++ rest`] >>
  simp[]
QED

(* Count-aligned companion; the shape premise restricts only the local dispatcher. *)
Theorem gen_inst_frame_sim_deep_count:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    source_memory_reads_disjoint cp inst vs /\
    context_source_memory_writes_disjoint cp inst vs /\
    opaque_use_ok fn /\ ~is_param_opcode inst.inst_opcode /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\ codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\ ~is_terminator inst.inst_opcode /\
    inst_wf inst /\ fn_shape_ok fn /\
    (inst.inst_opcode = LOG ==>
     ?tc args. inst.inst_operands = Lit tc :: args /\ w2n tc <= 4) /\
    (inst.inst_opcode = ASSERT ==> IS_SOME (FLOOKUP lo "revert")) /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (!lbl i. i < LENGTH (execute_plan cp.cp_initial_fmp ops) /\
             EL i (execute_plan cp.cp_initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op (frame_view fn ra vs) =
          operand_val (frame_view fn ra vs) lo op) /\
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val (frame_view fn ra vs) lo op =
             operand_val (frame_view fn ra vs) lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T)
                inst.inst_outputs) /\
    (!dist prev val_op.
       inst.inst_opcode = PHI /\
       stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
         ps.ps_stack = SOME dist /\
       vs.vs_prev_bb = SOME prev /\
       resolve_phi prev inst.inst_operands = SOME val_op ==>
       operand_val (frame_view fn ra vs) lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op (frame_view fn ra vs)) /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    (!off. MEM (SORestore off) ops ==> off < dimword (:256)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        fn_frame_inv ctx cp lo fn ra rest mem0 ps' vs' as' /\
        as'.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp ops) /\
        n = LENGTH (execute_plan cp.cp_initial_fmp ops) -
          (if inst.inst_opcode = ASSERT_UNREACHABLE then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >> rename1 `MEM r cplan.cp_regions` >>
  gen_tac >> strip_tac >>
  drule_all frame_inst_local_setup >> strip_tac >>
  `n2w cplan.cp_initial_fmp = vs.vs_initial_fmp` by
    fs[fn_frame_inv_def] >>
  `~MEM inst.inst_opcode [JMP; JNZ; DJMP]` by
    (simp[] >> rpt conj_tac >> strip_tac >> gvs[is_terminator_def]) >>
  fs[] >>
  drule_all
    (SRULE [venomMemPropsTheory.eval_operand_with_memory, operand_val_memory_update,
      frame_view_control_fields, arithmeticTheory.ADD_COMM]
    (Q.INST [`initial_fmp` |-> `cplan.cp_initial_fmp`,
       `vs` |-> `frame_view fn ra vs with vs_memory := as.as_memory`,
       `as` |-> `as with as_stack := top`] (SPEC_ALL gen_inst_ok_sim_marked_count))) >>
  strip_tac >> rename1 `venom_asm_rel _ ps' _ out` >>
  qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  qpat_x_assum `o2pc = _` SUBST_ALL_TAC >>
  drule_all frame_inst_local_lift >> strip_tac >>
  simp[]
QED
