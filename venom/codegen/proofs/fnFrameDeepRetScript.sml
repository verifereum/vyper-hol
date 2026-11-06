(*
 * gen_ret_frame_sim_deep: fnFrameBoundary's gen_ret_frame_sim for RET, with
 * operands at any stack depth, repeated dead_stack_marker slots
 * (generated_plan_state_wf_marked) and only an address bound on the
 * plan's spill and restore offsets.  fnFrameDeep collects it with the
 * other instruction frame lemmas the block induction composes.
 *
 * TOP-LEVEL:
 *   gen_ret_frame_sim_deep
 *)

Theory fnFrameDeepRet
Ancestors
  deepResidualSim fnPlanPrefix fnFrameBoundary fnFrameBoundaryGenRet
  fnFrameTerminalPrep preparedPrefixSim prefixSim stackOpSim planWf stackModel
  reorderSim asmFrame emitSim stackOpAsmSim frameViewFacts finite_map list rich_list genFrameSim frameRel contextCodegenRel
  codegenRel blockSimHelpers unitShapeDefs genBlockSim mixedPrefixSim
  stackPlanGen stackPlanTypes planExec asmSem venomExecSemantics venomState
  venomInst fcgDefs livenessDefs dfgDefs cfgDefs

(* fnFrameBoundaryGenRet's ret_frame_prefix over generated_plan_state_wf_marked,
   with any-depth ownership and an address bound on the plan's offsets.
   RET's plan never shrinks the planner stack below the operand count and
   ends empty, so the stack holds at most 16 cells throughout. *)
Theorem ret_frame_prefix_marked:
  !ctx cp lo o2pc prog liveness dfg cfg fn inst nl halting term label
    base ps vs st ops final ra rest mem0 values.
  inst.inst_opcode = RET /\ inst_wf inst /\
  generated_plan_state_wf_marked base ps /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)) /\
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
  final.ps_stack = [] /\
  asm_block_at prog st.as_pc (execute_plan cp.cp_initial_fmp ops) /\
  eval_operands (REVERSE (compute_operands inst)) (frame_view fn ra vs) = SOME values ==>
  ?n mid.
    asm_steps lo o2pc prog n st = AsmOK mid /\
    asm_block_at prog mid.as_pc [AsmOp "JUMP"] /\
    mid.as_stack = values ++ rest /\
    context_memory_rel cp vs.vs_memory mid.as_memory /\
    (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
      read_byte b mid.as_memory = read_byte b mem0) /\
    shared_state_rel vs mid
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ret_plan_no_spill >> strip_tac >>
  drule_all ret_plan_decompose >> strip_tac >>
  drule fn_frame_inv_local_state >> strip_tac >>
  suspend "local_run"
QED

Resume ret_frame_prefix_marked[local_run]:
  rename1 `generated_plan_state_wf_marked spillbase ps` >>
  rename1 `fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st` >>
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (rpt strip_tac >>
     qpat_x_assum `!op. MEM op _ /\ is_var_operand op ==> _` drule >>
     simp[] >> strip_tac
     >- (Cases_on `stack_get_depth op ps.ps_stack` >> gvs[] >>
         drule stack_get_depth_props >> simp[stack_peek_def] >>
         strip_tac >> disj1_tac >>
         qpat_x_assum `EL _ _ = op` (SUBST1_TAC o SYM) >>
         irule EL_MEM >> decide_tac) >>
     Cases_on `op IN FDOM ps.ps_spilled` >> fs[FLOOKUP_DEF]) >>
  `residual_budget_wf_marked spillbase [] ps /\ plan_slots_bounded spillbase ps /\
   spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    (drule generated_plan_state_wf_marked_residual_nil >>
     fs[generated_plan_state_wf_marked_def]) >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops)` by
    fs[EVERY_APPEND] >>
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
  suspend "labels"
QED

Resume ret_frame_prefix_marked[labels]:
  `LIST_REL (\op value. operand_val (frame_view fn ra vs) lo op = SOME value)
    (REVERSE (compute_operands inst)) values` by
    (irule eval_operands_operand_val_rel >> simp[]) >>
  `!op. MEM op (compute_operands inst) ==>
    IS_SOME (operand_val (frame_view fn ra vs) lo op)` by
    (qpat_x_assum `LIST_REL _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[LIST_REL_EL_EQN] >> strip_tac >>
     simp[MEM_EL] >> rpt strip_tac >>
     qpat_x_assum `!n. n < _ ==> _` (qspec_then
       `LENGTH (compute_operands inst) - (n + 1)` mp_tac) >>
     `LENGTH (compute_operands inst) - (n + 1) < LENGTH (compute_operands inst)` by decide_tac >>
     simp[EL_REVERSE] >>
     `LENGTH (compute_operands inst) - (LENGTH (compute_operands inst) - (n + 1) + 1) = n` by decide_tac >>
     simp[GSYM arithmeticTheory.ADD1]) >>
  `!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)` by
    (rpt strip_tac >> first_x_assum drule >>
     Cases_on `FLOOKUP lo l` >> simp[operand_val_def]) >>
  `RET <> INVOKE` by simp[] >>
  drule_all selected_prefix_prepared_sim_marked >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  suspend "lift"
QED

Resume ret_frame_prefix_marked[lift]:
  rename1 `venom_asm_rel lo arranged _ endpoint` >>
  `prefix_wf lo (LENGTH ps.ps_stack) iops` by
    (`prefix_wf lo (LENGTH ps.ps_stack)
        (FST (emit_input_plan RET (compute_operands inst) nl ps))` by
       (irule (cj 1 emit_input_plan_wf_len) >> simp[]) >> gvs[]) >>
  `prefix_wf (lo:string |-> num) (LENGTH prepared.ps_stack) rops` by
    (qpat_x_assum `reorder_plan _ _ _ = _` mp_tac >>
     qpat_x_assum `LENGTH (compute_operands inst) <= LENGTH prepared.ps_stack` mp_tac >>
     qpat_x_assum `LENGTH (compute_operands inst) <= 16` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     mp_tac (Q.SPECL [`dfg`, `compute_operands inst`, `prepared`, `lo`]
       (INST_TYPE [alpha |-> ``:num``] reorder_plan_wf_len)) >> simp[] >> strip_tac >> simp[]) >>
  `EVERY is_prefix_op (iops ++ rops)` by
    (simp[] >> metis_tac[prefix_wf_every_prefix_op]) >>
  `!off. ~MEM (SOSpill off) (iops ++ rops)` by
    (gvs[] >> metis_tac[]) >>
  drule_all no_spill_prefix_bytes >> strip_tac >>
  `arranged.ps_stack = compute_operands inst` by gvs[] >>
  `endpoint.as_stack = values` by
    (qpat_x_assum `LIST_REL _ _ _` mp_tac >>
     qpat_x_assum `venom_asm_rel lo arranged _ endpoint` mp_tac >>
     qpat_x_assum `!op. operand_val (_ with vs_memory := _) _ op = _` mp_tac >>
     qpat_x_assum `arranged.ps_stack = compute_operands inst` mp_tac >>
     qpat_x_assum `EVERY (\op. op <> dead_stack_marker /\ _) _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[venom_asm_rel_def, plan_stack_rel_def, LIST_REL_EL_EQN, EVERY_MEM] >>
     rpt strip_tac >> irule LIST_EQ >> simp[] >> rpt strip_tac >>
     first_x_assum (qspec_then `x` mp_tac) >>
     simp[] >> strip_tac >>
     `MEM (EL x (REVERSE (compute_operands inst))) (compute_operands inst)` by
       (once_rewrite_tac[GSYM MEM_REVERSE] >> irule EL_MEM >> simp[]) >>
     `x < LENGTH (compute_operands inst)` by decide_tac >>
     qpat_x_assum `!i. i < LENGTH (compute_operands inst) ==> _`
       (qspec_then `x` mp_tac) >> simp[] >>
     `EL x (REVERSE (compute_operands inst)) <> dead_stack_marker` by metis_tac[] >>
     simp[]) >>
  suspend "finish"
QED

Resume ret_frame_prefix_marked[finish]:
  `context_memory_rel cplan vs.vs_memory st.as_memory /\
   (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
     read_byte b st.as_memory = read_byte b mem0)` by
    (qpat_x_assum `fn_frame_inv _ _ _ _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[fn_frame_inv_def, context_venom_asm_rel_def, frame_view_def] >>
     metis_tac[]) >>
  `context_memory_rel cplan vs.vs_memory endpoint.as_memory` by
    (gvs[context_memory_rel_def] >> metis_tac[]) >>
  `shared_state_rel vs endpoint` by
    (qpat_x_assum `venom_asm_rel lo arranged _ endpoint` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[venom_asm_rel_def, shared_state_rel_def, venom_asm_terminal_rel_def,
       frame_view_def]) >>
  drule asm_steps_frame >> disch_then (qspec_then `rest` assume_tac) >>
  `st with as_stack := top ++ rest = st` by
    simp[asm_state_component_equality] >>
  qexistsl_tac [`LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops))`,
    `endpoint with as_stack := endpoint.as_stack ++ rest`] >>
  conj_tac >- gvs[] >>
  conj_tac
  >- (gvs[execute_plan_append, asm_block_at_append, execute_plan_def,
          exec_stack_op_def]) >>
  gvs[shared_state_rel_def, venom_asm_terminal_rel_def] >>
  metis_tac[]
QED

Finalise ret_frame_prefix_marked

(* gen_ret_frame_sim with any-depth ownership, generated_plan_state_wf_marked and an
   address bound on spill and restore offsets. *)
Theorem gen_ret_frame_sim_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' ra rest mem0 pc_ret.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = RET /\
    MEM inst (fn_insts (reachable_fn fn)) /\
    codegen_ready_fn fn /\ opaque_use_ok fn /\ retpc_shape_ok fn /\
    inst_wf inst /\
    generated_plan_state_wf_marked base ps /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
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
    (fn_has_retpc fn ==> FLOOKUP o2pc (w2n ra) = SOME pc_ret) /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    ps'.ps_stack = [] /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
    !ret vs'. step_inst fuel ctx inst vs = IntRet ret vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        as'.as_pc = pc_ret /\
        as'.as_stack = REVERSE ret.iret_values ++ rest /\
        context_memory_rel cp vs'.vs_memory as'.as_memory /\
        (!b. context_spill_byte cp b /\
             ~closure_spill_byte ctx cp fn.fn_name b ==>
             read_byte b as'.as_memory = read_byte b mem0) /\
        shared_state_rel vs' as'
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_tac >>
  drule_all ret_source_frame_boundary >>
  disch_then (qspec_then `ra` strip_assume_tac) >>
  drule_all ret_frame_prefix_marked >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rename1 `asm_steps lo o2pc prog n as = AsmOK mid` >>
  `FLOOKUP o2pc (w2n ra) = SOME pc_ret` by metis_tac[] >>
  `asm_steps lo o2pc prog (SUC 0) mid =
    AsmOK (mid with <| as_pc := pc_ret;
      as_stack := REVERSE ret.iret_values ++ rest |>)` by
    (pure_rewrite_tac[asm_steps_def] >>
     qpat_x_assum `asm_block_at prog mid.as_pc _` mp_tac >>
     simp[asm_block_at_def] >> strip_tac >>
     `mid.as_pc < LENGTH prog` by decide_tac >>
     gvs[asm_step_jump, asm_jump_def]) >>
  qexistsl_tac [`n + SUC 0`,
    `mid with <| as_pc := pc_ret; as_stack := REVERSE ret.iret_values ++ rest |>`] >>
  conj_tac >- (irule asm_steps_compose_ok >> qexists `mid` >> simp[]) >>
  gvs[shared_state_rel_def, venom_asm_terminal_rel_def]
QED
