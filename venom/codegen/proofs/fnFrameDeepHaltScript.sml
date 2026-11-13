(*
 * gen_inst_halt_frame_sim_deep: fnFrameTerminal's gen_inst_halt_frame_sim for an instruction whose step Halts, with
 * operands at any stack depth, repeated dead_stack_marker slots
 * (generated_plan_state_wf_marked) and only an address bound on the
 * plan's spill and restore offsets.  fnFrameDeep collects it with the
 * other instruction frame lemmas the block induction composes.
 *
 * TOP-LEVEL:
 *   gen_inst_halt_frame_sim_deep
 *)

Theory fnFrameDeepHalt
Ancestors
  deepResidualBudget deepResidualSim fnPlanPrefix fnFrameTerminal genFrameSim frameRel contextCodegenRel
  codegenRel blockSimHelpers unitShapeDefs genBlockSim mixedPrefixSim
  stackPlanGen stackPlanTypes planExec asmSem venomExecSemantics venomState
  venomInst fcgDefs livenessDefs dfgDefs cfgDefs
  fnFrameTerminalPrep fnFrameTerminalHalt asmIR opcodeClass generatedPrefixSim
  preparedPrefixSim emitSim stackPlanOps allocMono frameViewFacts frameViewMemory
  list venomWf finite_map planWf stackModel asmFrame venomEffects stackOpSim
  reorderSim regularMemorySim stackOpAsmSim

(* fnFrameTerminalHalt$frame_terminal_prefix_setup with any-depth
   ownership, generated_plan_state_wf_marked and an address bound on the
   plan's spill and restore offsets: the prefix runs to the terminal
   opcode with its operands on top of the stack. *)
Theorem frame_terminal_prefix_setup_marked:
  !ctx cp lo o2pc prog liveness dfg cfg fn inst nl halting term label
    base ps vs st ops final r ra rest mem0.
  (inst.inst_opcode = STOP \/ inst.inst_opcode = RETURN \/
    inst.inst_opcode = SELFDESTRUCT) /\ inst_wf inst /\
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  MEM r cp.cp_regions /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked base ps /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)) /\
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
  generate_inst_plan liveness dfg cfg fn inst nl halting term label ps = SOME (ops,final) /\
  asm_block_at prog st.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
  ?n mid name.
    asm_steps lo o2pc prog n st = AsmOK mid /\
    asm_block_at prog mid.as_pc [AsmOp name] /\
    venom_to_evm_name inst.inst_opcode = SOME name /\
    context_memory_rel cp vs.vs_memory mid.as_memory /\
    venom_asm_terminal_rel vs mid /\
    mid.as_call_ctx = vs.vs_call_ctx /\
    (!values. eval_operands (REVERSE (compute_operands inst)) vs = SOME values ==>
      mid.as_stack = values ++ DROP (LENGTH (compute_operands inst)) mid.as_stack)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `?name. venom_to_evm_name inst.inst_opcode = SOME name /\
    inst.inst_outputs = [] /\ ~is_commutative inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    generate_regular_inst_plan liveness dfg cfg fn inst nl halting term label ps =
      (ops,final)` by
    (gvs[generate_inst_plan_def, is_pre_codegen_opcode_def, is_param_opcode_def,
        inst_wf_def, venom_to_evm_name_def, is_commutative_def, compute_operands_def]) >>
  drule_all output_free_regular_plan >> strip_tac >>
  drule fn_frame_inv_local_state >> strip_tac >>
  suspend "local_run"
QED

Resume frame_terminal_prefix_setup_marked[local_run]:
  rename1 `generated_plan_state_wf_marked spillbase ps` >>
  rename1 `MEM r cplan.cp_regions` >>
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (rpt strip_tac >>
     qpat_x_assum `!op. MEM op _ /\ is_var_operand op ==> _` drule >>
     simp[] >> strip_tac
     >- (Cases_on `stack_get_depth op ps.ps_stack` >> fs[] >>
         drule stack_get_depth_props >> simp[stack_peek_def] >>
         strip_tac >> disj1_tac >>
         qpat_x_assum `EL _ _ = op` (SUBST1_TAC o SYM) >>
         irule EL_MEM >> decide_tac) >>
     Cases_on `op IN FDOM ps.ps_spilled` >> fs[FLOOKUP_DEF]) >>
  `residual_budget_wf_marked spillbase [] ps /\ plan_slots_bounded spillbase ps /\
   spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    (drule generated_plan_state_wf_marked_residual_nil >>
     simp[residual_budget_wf_marked_def]) >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops)` by
    (qpat_x_assum `EVERY _ ops` mp_tac >> simp[EVERY_APPEND]) >>
  `asm_block_at prog (st with as_stack := top).as_pc
    (execute_plan cplan.cp_initial_fmp (iops ++ rops))` by
    (gvs[execute_plan_append, asm_block_at_append]) >>
  `PERM (compute_operands inst) (compute_operands inst)` by simp[] >>
  `LENGTH (compute_operands inst) <= LENGTH prepared.ps_stack` by gvs[] >>
  `!op. operand_val (frame_view fn ra vs with vs_memory := st.as_memory) lo op =
    operand_val (frame_view fn ra vs) lo op` by
    (Cases >> simp[operand_val_def]) >>
  `!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs with vs_memory := st.as_memory) lo op =
    operand_val (frame_view fn ra vs with vs_memory := st.as_memory) lo at` by
    (simp[] >> metis_tac[]) >>
  drule_all selected_prefix_prepared_sim_marked >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  suspend "lift"
QED

Resume frame_terminal_prefix_setup_marked[lift]:
  rename1 `venom_asm_rel lo arranged _ endpoint` >>
  `context_memory_rel cplan vs.vs_memory st.as_memory` by
    (qpat_x_assum `fn_frame_inv _ _ _ _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[fn_frame_inv_def, context_venom_asm_rel_def, frame_view_def] >>
     metis_tac[]) >>
  `memory_rel arranged.ps_alloc st.as_memory endpoint.as_memory /\
   venom_asm_terminal_rel vs endpoint /\ endpoint.as_call_ctx = vs.vs_call_ctx` by
    (qpat_x_assum `venom_asm_rel lo arranged _ endpoint` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[venom_asm_rel_def, venom_asm_terminal_rel_def, frame_view_def]) >>
  `context_memory_rel cplan vs.vs_memory endpoint.as_memory` by
    (irule context_memory_rel_local_prefix >>
     qexistsl_tac [`arranged.ps_alloc`, `st.as_memory`, `r`] >>
     metis_tac[]) >>
  drule asm_steps_frame >> disch_then (qspec_then `rest` assume_tac) >>
  `st with as_stack := top ++ rest = st` by
    simp[asm_state_component_equality] >>
  qexistsl_tac [`LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops))`,
    `endpoint with as_stack := endpoint.as_stack ++ rest`, `name`] >>
  conj_tac >- gvs[] >>
  conj_tac
  >- (gvs[execute_plan_append, asm_block_at_append, execute_plan_def,
          exec_stack_op_def]) >>
  simp[venom_asm_terminal_rel_def] >>
  suspend "ready"
QED

Resume frame_terminal_prefix_setup_marked[ready]:
  conj_tac
  >- (qpat_x_assum `venom_asm_terminal_rel vs endpoint` mp_tac >>
      simp[venom_asm_terminal_rel_def]) >>
  `!x. MEM (Var x) (compute_operands inst) ==> ~retpc_var fn x` by
    (qpat_x_assum `opaque_use_ok fn` mp_tac >>
     qpat_x_assum `MEM inst (fn_insts fn)` mp_tac >>
     qpat_x_assum `_ \/ _ \/ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     gvs[compute_operands_def] >> drule ordinary_operand_not_retpc >> simp[] >>
     qexistsl_tac [`x`, `inst`] >> simp[]) >>
  `eval_operands (REVERSE (compute_operands inst))
      (frame_view fn ra vs with vs_memory := st.as_memory) =
    eval_operands (REVERSE (compute_operands inst)) vs` by
    (irule eval_operands_frame_view >> simp[]) >>
  rpt strip_tac >>
  `endpoint.as_stack = values ++
    DROP (LENGTH (compute_operands inst)) endpoint.as_stack` by
    (irule (arranged_eval_operands_stack |> Q.INST
       [`operands` |-> `REVERSE (compute_operands inst)`] |> SRULE []) >>
     conj_tac >- (fs[EVERY_MEM] >> metis_tac[]) >>
     qexistsl_tac [`lo`, `arranged`,
       `stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack`,
       `frame_view fn ra vs with vs_memory := st.as_memory`] >>
     simp[] >> rpt strip_tac >>
     `eval_operand op (frame_view fn ra vs with vs_memory := st.as_memory) =
      eval_operand op (frame_view fn ra vs)` by
       (Cases_on `op` >> simp[eval_operand_def, lookup_var_def]) >>
     metis_tac[]) >>
  `!xs ys. eval_operands xs vs = SOME ys ==> LENGTH ys = LENGTH xs` by
    (POP_ASSUM_LIST (K all_tac) >> Induct >>
     simp[eval_operands_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `LENGTH values = LENGTH (compute_operands inst)` by metis_tac[LENGTH_REVERSE] >>
  qpat_x_assum `endpoint.as_stack = values ++ _` mp_tac >>
  qpat_x_assum `LENGTH values = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  once_asm_rewrite_tac[] >> simp[DROP_APPEND, APPEND_ASSOC] >>
  qpat_x_assum `LENGTH values = _` (fn th => simp[GSYM th]) >>
  `LENGTH values - (LENGTH values + (LENGTH endpoint.as_stack - LENGTH values)) = 0`
    by decide_tac >> simp[]
QED

Finalise frame_terminal_prefix_setup_marked

(* gen_inst_halt_frame_sim with any-depth ownership, generated_plan_state_wf_marked and an
   address bound on spill and restore offsets. *)
Theorem gen_inst_halt_frame_sim_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\
    source_memory_reads_disjoint cp inst vs /\
    opaque_use_ok fn /\
    ~is_param_opcode inst.inst_opcode /\
    (* The invariant's region clause for the output planner state, as in
       gen_inst_frame_sim: the prefix's transient spills lie below
       ps'.ps_alloc.sa_next_offset, so this keeps them inside the region
       whose bytes source_memory_reads_disjoint keeps the payload out of.
       fn_frame_inv bounds only ps at entry, which isn't enough
       (fnFrameTerminalPrep$terminal_escape_halt_counterexample). *)
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    inst_wf inst /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
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
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = Halt vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmHalt as' /\
        venom_asm_terminal_rel vs' as'
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  gen_tac >> disch_tac >>
  SUBGOAL_THEN ``inst.inst_opcode = STOP \/ inst.inst_opcode = RETURN \/
    inst.inst_opcode = SELFDESTRUCT`` assume_tac
  >- (drule step_inst_halt_opcodes >> strip_tac >> simp[] >>
      qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
      gvs[generate_inst_plan_def, is_pre_codegen_opcode_def]) >>
  drule_all frame_terminal_prefix_setup_marked >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qpat_x_assum `_ \/ _ \/ _` strip_assume_tac
  >- suspend "stop"
  >- suspend "return"
  >> suspend "selfdestruct"
QED

Resume gen_inst_halt_frame_sim_deep[stop]:
  `vs' = halt_state (vs with vs_returndata := [])` by
    (qpat_x_assum `step_inst _ _ _ _ = Halt _` mp_tac >>
     simp[Once step_inst_def, step_inst_base_def]) >>
  `name = "STOP"` by fs[venom_to_evm_name_def] >>
  `asm_block_at prog mid.as_pc [AsmOp "STOP"]` by metis_tac[] >>
  drule_all terminal_stop_step >>
  disch_then (qspecl_then [`lo`, `o2pc`] strip_assume_tac) >>
  qexistsl_tac [`n + 1`, `st'`] >> conj_tac
  >- (irule asm_steps_compose_halt >> qexists `mid` >> gvs[]) >>
  gvs[]
QED

Resume gen_inst_halt_frame_sim_deep[return]:
  qpat_x_assum `step_inst _ _ _ _ = Halt _` mp_tac >>
  simp[Once step_inst_def, step_inst_base_def, AllCaseEqs()] >>
  strip_tac >>
  `inst.inst_operands = [off_op; sz_op]` by metis_tac[] >>
  `name = "RETURN"` by fs[venom_to_evm_name_def] >>
  `asm_block_at prog mid.as_pc [AsmOp "RETURN"]` by metis_tac[] >>
  `mid.as_stack = off :: sz :: DROP 2 mid.as_stack` by
    (qpat_x_assum `!values. eval_operands _ _ = _ ==> _` mp_tac >>
     simp[compute_operands_def, python_stack_operands_def,
       ir_specific_operand_order_def, eval_operands_def]) >>
  `MEM (w2n off, w2n sz) (source_memory_read_ranges inst vs)` by
    simp[source_memory_read_ranges_def, memory_range_of_operands_def] >>
  drule_all context_source_payload_agree >> disch_tac >>
  drule_all terminal_return_payload_step >>
  disch_then (qspecl_then [`o2pc`, `lo`] strip_assume_tac) >>
  qexistsl_tac [`n + 1`, `st'`] >> conj_tac
  >- (irule asm_steps_compose_halt >> qexists `mid` >> gvs[]) >>
  gvs[]
QED

Resume gen_inst_halt_frame_sim_deep[selfdestruct]:
  qpat_x_assum `step_inst _ _ _ _ = Halt _` mp_tac >>
  simp[Once step_inst_def, step_inst_base_def, AllCaseEqs()] >>
  strip_tac
  (* the static guard's other disjunct: the operand evaluates, so
     eval_operands can't be NONE *)
  >~ [`eval_operands _ _ = NONE`] >- gvs[eval_operands_def] >>
  `name = "SELFDESTRUCT"` by fs[venom_to_evm_name_def] >>
  `asm_block_at prog mid.as_pc [AsmOp "SELFDESTRUCT"]` by metis_tac[] >>
  `mid.as_stack = addr :: DROP 1 mid.as_stack` by
    (qpat_x_assum `!values. eval_operands _ _ = _ ==> _` mp_tac >>
     simp[compute_operands_def, python_stack_operands_def,
       ir_specific_operand_order_def, eval_operands_def]) >>
  drule_all terminal_selfdestruct_rel_step >>
  disch_then (qspecl_then [`o2pc`, `lo`] strip_assume_tac) >>
  qexistsl_tac [`n + 1`, `st'`] >> conj_tac
  >- (irule asm_steps_compose_halt >> qexists `mid` >> gvs[]) >>
  gvs[COND_RATOR]
QED

Finalise gen_inst_halt_frame_sim_deep
