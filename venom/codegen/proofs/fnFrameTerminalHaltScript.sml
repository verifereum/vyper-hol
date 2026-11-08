Theory fnFrameTerminalHalt
Ancestors
  fnFrameTerminalPrep generatedPrefixSim preparedPrefixSim emitSim
  stackPlanGen stackPlanOps allocMono frameViewFacts frameViewMemory
  contextCodegenRel list venomWf finite_map planWf stackModel
  codegenRel asmFrame venomInst venomEffects asmIR genBlockSim stackOpSim reorderSim
  frameRel planExec asmSem venomState regularMemorySim stackOpAsmSim memoryReadRel

(* Empty outputs eliminate both postfix phases.  Keep the arranged planner
   as the semantic boundary, so prefix simulation needs no shadow-state
   allocation comparison. *)
Theorem output_free_regular_plan:
  venom_to_evm_name inst.inst_opcode = SOME name /\
  inst.inst_outputs = [] /\ ~is_commutative inst.inst_opcode /\
  generate_regular_inst_plan liveness dfg cfg fn inst nl halting term label ps =
    (ops, final) ==>
  ?iops prepared rops arranged.
    emit_input_plan inst.inst_opcode (compute_operands inst) nl ps =
      (iops, prepared) /\
    reorder_plan dfg (compute_operands inst) prepared = (rops, arranged) /\
    ops = iops ++ rops ++ [SOEmit name] /\
    final = release_dead_spills nl
      (arranged with ps_stack := stack_pop (LENGTH (compute_operands inst))
        arranged.ps_stack) /\
    arranged.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
    arranged.ps_alloc.sa_next_offset = final.ps_alloc.sa_next_offset
Proof
  strip_tac >> drule_all regular_plan_selected_prefix >>
  disch_then (REPEAT_TCL CHOOSE_THEN strip_assume_tac) >>
  gvs[release_dead_spills_spill_base, release_dead_spills_next_offset] >>
  metis_tac[]
QED

Theorem ordinary_inst_operand_frame_view:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> PHI /\
  inst.inst_opcode <> RET /\ inst.inst_opcode <> RETFMP /\
  inst.inst_opcode <> DRET /\ MEM op inst.inst_operands ==>
  eval_operand op (frame_view fn ra vs with vs_memory := m) =
    eval_operand op vs
Proof
  strip_tac >> irule eval_operand_frame_view >> gen_tac >> disch_tac >>
  irule ordinary_operand_not_retpc >> simp[] >> qexists `inst` >> gvs[]
QED

Theorem frame_terminal_prefix_setup:
  !ctx cp lo o2pc prog liveness dfg cfg fn inst nl halting term label
    base ps vs st ops final r ra rest mem0.
  (inst.inst_opcode = STOP \/ inst.inst_opcode = RETURN \/
    inst.inst_opcode = SELFDESTRUCT) /\ inst_wf inst /\
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  MEM r cp.cp_regions /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf base ps /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
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
  prefix_spill_wf cp.cp_initial_fmp lo (FRONT ops) ps /\
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

Resume frame_terminal_prefix_setup[local_run]:
  rename1 `generated_plan_state_wf spillbase ps` >>
  rename1 `MEM r cplan.cp_regions` >>
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (rpt strip_tac >>
     qpat_x_assum `!op. MEM op _ /\ is_var_operand op ==> _` drule >>
     simp[] >> strip_tac
     >- (drule stack_get_depth_props >> simp[stack_peek_def] >>
         strip_tac >> disj1_tac >>
         qpat_x_assum `EL _ _ = op` (SUBST1_TAC o SYM) >>
         irule EL_MEM >> decide_tac) >>
     Cases_on `op IN FDOM ps.ps_spilled` >> fs[FLOOKUP_DEF]) >>
  `residual_budget_wf spillbase [] ps /\ plan_slots_bounded spillbase ps /\
   spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    (fs[generated_plan_state_wf_def] >>
     metis_tac[residual_budget_wf_canonical]) >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops)` by
    (simp[] >> irule regular_prefix_segment_address_bounds >>
     qexistsl_tac [`cplan.cp_initial_fmp`, `lo`, `name`, `ops`, `[]`, `ps`] >> simp[]) >>
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
  drule_all selected_prefix_prepared_sim >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  suspend "lift"
QED

Resume frame_terminal_prefix_setup[lift]:
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

Resume frame_terminal_prefix_setup[ready]:
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

Finalise frame_terminal_prefix_setup

(* RETURN only needs agreement of the actual payload, not ordered spill bounds. *)
Theorem terminal_return_payload_step:
  asm_block_at prog st.as_pc [AsmOp "RETURN"] /\
  st.as_stack = offv :: szv :: tail /\
  venom_asm_terminal_rel vs st /\
  TAKE (w2n szv) (DROP (w2n offv) st.as_memory ++ REPLICATE (w2n szv) 0w) =
  TAKE (w2n szv) (DROP (w2n offv) vs.vs_memory ++ REPLICATE (w2n szv) 0w) ==>
  ?st'. asm_steps lo o2pc prog 1 st = AsmHalt st' /\
    venom_asm_terminal_rel
      (halt_state (set_returndata
        (TAKE (w2n szv) (DROP (w2n offv) vs.vs_memory ++
          REPLICATE (w2n szv) 0w)) vs)) st'
Proof
  strip_tac >> `1 = SUC 0` by simp[] >> pop_assum SUBST1_TAC >>
  simp[Once asm_steps_def, asm_steps_def] >>
  fs[asm_block_at_def] >>
  simp[asm_step_def, asm_step_op_def, asm_step_arith_def,
    asm_step_compare_def, asm_step_bitwise_def, asm_step_memory_def,
    asm_step_control_def, asm_return_op_def] >>
  fs[venom_asm_terminal_rel_def, halt_state_def, set_returndata_def] >>
  Cases_on `w2n szv = 0` >> simp[] >>
  fs[venom_returndata_read_byte, expanded_slice_padded_range]
QED

Theorem terminal_selfdestruct_rel_step:
  asm_block_at prog st.as_pc [AsmOp "SELFDESTRUCT"] /\
  st.as_stack = addr :: tail /\
  venom_asm_terminal_rel vs st /\
  st.as_call_ctx = vs.vs_call_ctx ==>
  ?st'. asm_steps lo o2pc prog 1 st = AsmHalt st' /\
    venom_asm_terminal_rel
      (halt_state (set_returndata [] (vs with vs_accounts :=
        (\a. if a = vs.vs_call_ctx.cc_address then
          lookup_account vs.vs_call_ctx.cc_address vs.vs_accounts with balance := 0
        else if a = (w2w addr : address) then
          lookup_account (w2w addr) vs.vs_accounts with balance :=
            (lookup_account vs.vs_call_ctx.cc_address vs.vs_accounts).balance +
            (lookup_account (w2w addr) vs.vs_accounts).balance
        else vs.vs_accounts a)))) st'
Proof
  strip_tac >> `1 = SUC 0` by simp[] >> pop_assum SUBST1_TAC >>
  simp[Once asm_steps_def, asm_steps_def] >>
  fs[asm_block_at_def] >>
  rewrite_tac[stackOpAsmSimTheory.asm_step_selfdestruct, asm_selfdestruct_def] >>
  asm_rewrite_tac[] >>
  fs[venom_asm_terminal_rel_def, halt_state_def, set_returndata_def]
QED
