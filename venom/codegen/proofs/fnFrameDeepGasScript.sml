(*
 * gas_inst_frame_sim_owned_deep: gasFrameSim's gas_inst_frame_sim_owned for GAS, with
 * operands at any stack depth, repeated dead_stack_marker slots
 * (generated_plan_state_wf_marked) and only an address bound on the
 * plan's spill and restore offsets.  fnFrameDeep collects it with the
 * other instruction frame lemmas the block induction composes.
 *
 * TOP-LEVEL:
 *   gas_inst_frame_sim_owned_deep
 *)

Theory fnFrameDeepGas
Ancestors
  deepResidualSim fnPlanPrefix gasFrameSim genFrameSim frameRel contextCodegenRel
  codegenRel blockSimHelpers unitShapeDefs genBlockSim mixedPrefixSim
  stackPlanGen stackPlanTypes planExec asmSem venomExecSemantics venomState
  venomInst fcgDefs livenessDefs dfgDefs cfgDefs doSwapSim regularPostfixSim
  instSimHelpers stackOpSim planWf list rich_list spillPlanSim

(* gasFrameSim's gas_plan_local_sim with the spill-alloc layout and an
   address bound on the plan's spill and restore offsets in place of
   generated_plan_state_wf and prefix_spill_wf: the live output's swap
   needs no distinct stack. *)
Theorem gas_plan_local_sim_numeric[local]:
  inst.inst_opcode = GAS /\ inst.inst_operands = [] /\ inst.inst_outputs = [out] /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  generate_inst_plan liveness dfg cfg fn inst live is_halting next_term bb ps =
    SOME (ops,ps') /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  EVERY (\op. case op of Var x => x <> out | _ => T) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
     case op of Var x => x <> out | _ => T) /\
  venom_asm_rel lo ps vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
    venom_asm_rel lo ps'
      (update_var out (HD (vs.vs_gas_readings ++ [0w]))
        (vs with vs_gas_readings := TL vs.vs_gas_readings)) st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >>
  drule_all gas_plan_shape >> disch_then assume_tac >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[] >>
  Cases_on `MEM out live` >> simp[]
  >- suspend "live" >>
  Cases_on `is_halting` >> simp[]
  >- suspend "retained" >>
  suspend "pop"
QED

Resume gas_plan_local_sim_numeric[live]:
  Cases_on `optimistic_swap_plan dfg inst live next_term
    (ps with ps_stack := SNOC (Var out) ps.ps_stack)` >>
  rename1 `optimistic_swap_plan _ _ _ _ _ = (tail, ps9)` >>
  simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `!ps next_liveness next_is_term liveness is_halting fn dfg cfg bb_label. _` kall_tac >>
  `!xs. execute_plan initial_fmp (SOEmit "GAS" :: xs) =
       AsmOp "GAS" :: execute_plan initial_fmp xs` by
    simp[execute_plan_def, exec_stack_op_def] >>
  `asm_block_at prog st.as_pc [AsmOp "GAS"]` by
    (fs[asm_block_at_cons] >> simp[asm_block_at_cons, asm_block_at_def]) >>
  drule_all gas_emit_steps >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  `asm_block_at prog st'.as_pc (execute_plan initial_fmp tail)` by
    fs[asm_block_at_cons] >>
  qabbrev_tac `vs1 = update_var out (HD (vs.vs_gas_readings ++ [0w]))
    (vs with vs_gas_readings := TL vs.vs_gas_readings)` >>
  qabbrev_tac `psp = ps with ps_stack := SNOC (Var out) ps.ps_stack` >>
  `spill_alloc_layout_wf psp.ps_alloc psp.ps_spilled` by
    simp[Abbr `psp`] >>
  `?st''. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp tail)) st' =
            AsmOK st'' /\
          venom_asm_rel lo ps9 vs1 st'' /\
          st''.as_pc = st'.as_pc + LENGTH (execute_plan initial_fmp tail)` by
    (drule gas_optimistic_cases >> strip_tac
     >- (gvs[] >> qexists_tac `st'` >> simp[execute_plan_def, asm_steps_def]) >>
     `dist < LENGTH psp.ps_stack` by metis_tac[stack_get_depth_bound] >>
     drule_all do_swap_venom_asm_rel_numeric >>
     disch_then (qspec_then `o2pc` strip_assume_tac) >>
     qexists_tac `st''` >> simp[]) >>
  qexists_tac `st''` >>
  conj_tac
  >- (`SUC (LENGTH (execute_plan initial_fmp tail)) =
        1 + LENGTH (execute_plan initial_fmp tail)` by simp[] >>
      asm_rewrite_tac[LENGTH] >> irule asm_steps_compose_ok >>
      goal_assum (drule_at Any) >> simp[]) >>
  simp[] >> irule venom_asm_rel_release_dead_spills >> simp[]
QED
Resume gas_plan_local_sim_numeric[retained]:
  strip_tac >> gvs[] >>
  `execute_plan initial_fmp [SOEmit "GAS"] = [AsmOp "GAS"]` by
    simp[execute_plan_def, exec_stack_op_def] >>
  gvs[] >> drule_all gas_emit_steps >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists_tac `st'` >> simp[] >>
  irule venom_asm_rel_release_dead_spills >> simp[]
QED
Resume gas_plan_local_sim_numeric[pop]:
  strip_tac >> gvs[] >>
  `execute_plan initial_fmp [SOEmit "GAS"; SOPop 1] =
    [AsmOp "GAS"; AsmOp "POP"]` by
    (simp[execute_plan_def, exec_stack_op_def] >>
     once_rewrite_tac[arithmeticTheory.ONE] >> simp[REPLICATE]) >>
  gvs[] >>
  `st.as_gas_readings = vs.vs_gas_readings` by fs[venom_asm_rel_def] >>
  drule gas_readings_relation >>
  disch_then (qspec_then `TL vs.vs_gas_readings` assume_tac) >>
  drule_all venom_asm_rel_update_var >>
  disch_then (qspec_then `HD (vs.vs_gas_readings ++ [0w])` assume_tac) >>
  qexists_tac `st with <|as_pc := st.as_pc + 2;
                        as_gas_readings := TL vs.vs_gas_readings|>` >>
  simp[] >> conj_tac
  >- (fs[asm_block_at_def] >>
      `EL st.as_pc prog = AsmOp "GAS"` by
        (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
      `EL (st.as_pc + 1) prog = AsmOp "POP"` by
        (first_x_assum (qspec_then `1` mp_tac) >> simp[EL]) >>
      `2 = SUC 1` by decide_tac >>
      qpat_x_assum `2 = SUC 1` (fn th => once_rewrite_tac[th]) >>
      simp[Once asm_steps_def] >>
      simp[gas_asm_step, asm_gas_def, asm_push_val_def, asm_next_def] >>
      Cases_on `vs.vs_gas_readings` >> simp[] >>
      once_rewrite_tac[arithmeticTheory.ONE] >>
      simp[Once asm_steps_def] >>
      simp[asm_step_def, asm_step_op_def, asm_step_arith_def,
           asm_step_compare_def, asm_step_bitwise_def, asm_step_memory_def,
           asm_pop_def, asm_next_def, asm_steps_def] >>
      simp[asm_state_component_equality]) >>
  irule venom_asm_rel_release_dead_spills >>
  fs[venom_asm_rel_def, plan_stack_rel_def, plan_spill_rel_def]
QED
Finalise gas_plan_local_sim_numeric

(* gas_inst_frame_sim_owned with any-depth ownership, generated_plan_state_wf_marked and an
   address bound on spill and restore offsets. *)
Theorem gas_inst_frame_sim_owned_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode = GAS /\
    (* inst_wf doesn't fix the operand count of the read-only opcodes. *)
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    (* The context-level memory obligations (codegen_memory_obligations). *)
    source_memory_reads_disjoint cp inst vs /\
    context_source_memory_writes_disjoint cp inst vs /\
    (* Return-PC variables are only copied (unit_shape_ok's fn_shape_ok). *)
    opaque_use_ok fn /\ retpc_shape_ok fn /\
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
     ?tc rest. inst.inst_operands = Lit tc :: rest /\ w2n tc <= 4) /\
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
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
          context_spill_step_safe cp vs vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        fn_frame_inv ctx cp lo fn ra rest mem0 ps' vs' as' /\
        as'.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  rename1 `MEM r cplan.cp_regions` >>
  drule_all gas_source_shape >> strip_tac >>
  drule_all gas_step_frame_view >> strip_tac >>
  drule_all gas_step_result >> strip_tac >>
  `vs'.vs_halted = vs.vs_halted /\
   vs'.vs_initial_fmp = vs.vs_initial_fmp /\
   vs'.vs_memory = vs.vs_memory` by simp[update_var_def] >>
  `spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    fs[generated_plan_state_wf_marked_def] >>
  qexists_tac `LENGTH (execute_plan cplan.cp_initial_fmp ops)` >>
  irule gas_frame_lift >>
  reverse conj_tac
  >- (conj_tac >- (qexists_tac `r` >> simp[]) >>
      qexistsl_tac [`ps`, `vs`] >> simp[]) >>
  qx_gen_tac `top` >> strip_tac >>
  `context_venom_asm_rel cplan lo ps (frame_view fn ra vs)
     (as with as_stack := top)` by
    (fs[fn_frame_inv_def] >> gvs[]) >>
  drule gas_context_local >> strip_tac >>
  `~retpc_var fn out` by
    (irule gas_output_non_retpc >> simp[] >> metis_tac[MEM]) >>
  `frame_view fn ra vs' with vs_memory := as.as_memory =
    update_var out (HD ((frame_view fn ra vs with vs_memory := as.as_memory).vs_gas_readings ++ [0w]))
      ((frame_view fn ra vs with vs_memory := as.as_memory)
        with vs_gas_readings := TL (frame_view fn ra vs with vs_memory := as.as_memory).vs_gas_readings)` by
    (simp[gas_frame_view_update, gas_frame_view_readings] >>
     simp[frame_view_def, update_var_def]) >>
  `EVERY (\op. case op of Var x => x <> out | _ => T) ps.ps_stack /\
   (!op. op IN FDOM ps.ps_spilled ==>
      case op of Var x => x <> out | _ => T)` by fs[] >>
  `asm_block_at prog (as with as_stack := top).as_pc
     (execute_plan cplan.cp_initial_fmp ops)` by simp[] >>
  drule_all gas_plan_local_sim_numeric >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists_tac `st'` >> gvs[]
QED
