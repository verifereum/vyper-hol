(*
 * genBlockSim's gen_inst_ok_sim over a planner state with repeated
 * dead_stack_marker slots (generated_plan_state_wf_marked), with operands
 * owned at any stack depth and only an address bound on the plan's spill
 * and restore offsets.  The input preparation runs on deepResidualSim's
 * marker-tolerant numeric chain.
 *
 * TOP-LEVEL:
 *   gen_inst_ok_sim_marked
 *)

Theory deepInstSim
Ancestors
  deepResidualSim deepResidualBudget fnPlanPrefix regularPostfixSim genBlockSim planWf
  regularEmitSim regularPlanSim emitSim prefixExec prefixSim venomWf
  generatedPrefixSim preparedPrefixSim generatedReorderSim reorderSim
  doSwapSim mixedPrefixSim codegenRel blockSimHelpers planSpillBounds
  stackOpSim stackModel stackPlanGen stackPlanOps stackPlanTypes planExec
  asmSem venomExecSemantics venomState venomInst
  sorting list rich_list arithmetic

(* regularPostfixSim's optimistic_swap_plan_postfix_sim_structural on the
   numeric do_swap simulation: no stack distinctness, an address bound on
   the plan's spill and restore offsets. *)
Theorem optimistic_swap_plan_postfix_sim_numeric:
  !dfg inst next_liveness next_is_term ps ops ps'
   initial_fmp lo o2pc prog vs st.
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    optimistic_swap_plan dfg inst next_liveness next_is_term ps = (ops,ps') /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'.
      asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
      venom_asm_rel lo ps' vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `?dist. ~next_is_term /\ inst.inst_outputs <> [] /\
    next_liveness <> [] /\
    ~operand_equiv dfg (Var (LAST inst.inst_outputs)) (Var (LAST next_liveness)) /\
    stack_get_depth (Var (LAST next_liveness)) ps.ps_stack = SOME dist`
  >- (gvs[optimistic_swap_plan_def] >>
      `dist < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_bound] >>
      drule_all do_swap_venom_asm_rel_numeric >> simp[]) >>
  `ops = [] /\ ps' = ps` by
    (qpat_x_assum `optimistic_swap_plan _ _ _ _ _ = _` mp_tac >>
     simp[optimistic_swap_plan_def] >> rpt (IF_CASES_TAC >> simp[]) >>
     CASE_TAC >> gvs[]) >>
  qexists `st` >> gvs[execute_plan_def, asm_steps_def]
QED

(* regularPostfixSim's regular_generated_postfix_sim_structural on the
   numeric do_swap simulation. *)
Theorem regular_generated_postfix_sim_numeric:
  !dfg inst next_liveness is_halting next_is_term ps7 pop_ops ps8 opt_ops ps9 ps'
   initial_fmp lo o2pc prog vs st.
  LENGTH inst.inst_outputs <= 1 /\
  (!out. inst.inst_outputs = [out] ==>
    stack_get_depth (Var out) ps7.ps_stack = SOME 0) /\
  spill_alloc_layout_wf ps7.ps_alloc ps7.ps_spilled /\
  (if inst.inst_outputs = [] \/ is_halting then ([],ps7)
   else popmany_plan (MAP Var (FILTER (\out. ~MEM out next_liveness)
     inst.inst_outputs)) ps7) = (pop_ops,ps8) /\
  (if FILTER (\out. MEM out next_liveness) inst.inst_outputs = [] then ([],ps8)
   else optimistic_swap_plan dfg inst next_liveness next_is_term ps8) = (opt_ops,ps9) /\
  ps' = release_dead_spills next_liveness ps9 /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) opt_ops /\
  venom_asm_rel lo ps7 vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp (pop_ops ++ opt_ops)) ==>
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp (pop_ops ++ opt_ops))) st =
    AsmOK st' /\ venom_asm_rel lo ps' vs st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp (pop_ops ++ opt_ops))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_outputs` >> gvs[]
  >- (qexists_tac `st` >> simp[execute_plan_def, asm_steps_def] >>
      irule venom_asm_rel_release_dead_spills >> simp[]) >>
  rename1 `inst.inst_outputs = out::outs` >>
  `outs = []` by (Cases_on `outs` >> gvs[]) >> gvs[] >>
  Cases_on `MEM out next_liveness` >> gvs[]
  >- (Cases_on `is_halting` >> gvs[popmany_plan_def] >>
      drule_all optimistic_swap_plan_postfix_sim_numeric >>
      disch_then (qspec_then `o2pc` strip_assume_tac) >>
      qexists_tac `st'` >> simp[] >>
      irule venom_asm_rel_release_dead_spills >> simp[]) >>
  Cases_on `is_halting` >> gvs[]
  >- (qexists_tac `st` >> simp[execute_plan_def, asm_steps_def] >>
      irule venom_asm_rel_release_dead_spills >> simp[]) >>
  drule_all popmany_plan_top_singleton_sim >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists_tac `st'` >> simp[] >>
  irule venom_asm_rel_release_dead_spills >> simp[]
QED

Theorem regular_inst_ok_sim_marked:
  !fuel ctx lo o2pc prog liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label spill_base ps vs as ops ps' name initial_fmp.
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> GAS /\
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    venom_to_evm_name inst.inst_opcode = SOME name /\
    EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
                       ps'.ps_alloc.sa_next_offset <= off)
      (source_memory_read_ranges inst vs) /\
    generated_plan_state_wf_marked spill_base ps /\
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
          eval_operand op vs = operand_val vs lo op) /\
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val vs lo op = operand_val vs lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T)
                inst.inst_outputs) /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs as /\
    n2w initial_fmp = vs.vs_initial_fmp /\
    generate_regular_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps = (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) /\
    step_inst fuel ctx inst vs = OK vs' /\
    inst_memory_safe ps'.ps_alloc inst vs vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as' /\
        (~is_terminator inst.inst_opcode ==>
         as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp ops))
Proof
  rpt strip_tac >>
  drule_all regular_plan_selected_prefix >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  `PERM (compute_operands inst) selected` by
    (irule regular_plan_selected_perm >> metis_tac[]) >>
  `LENGTH selected = LENGTH (compute_operands inst)` by metis_tac[sortingTheory.PERM_LENGTH] >>
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (rpt strip_tac >>
     qpat_x_assum `!op. MEM op _ /\ is_var_operand op ==> _` drule >>
     simp[] >> strip_tac
     >- (fs[stack_get_depth_def, optionTheory.IS_SOME_EXISTS] >> drule stack_find_el >>
         drule planWfTheory.stack_find_bound >>
         metis_tac[MEM_EL, MEM_REVERSE]) >>
     Cases_on `op IN FDOM ps.ps_spilled` >> fs[finite_mapTheory.FLOOKUP_DEF]) >>
  `residual_budget_wf_marked spill_base [] ps` by
    metis_tac[generated_plan_state_wf_marked_residual_nil] >>
  `plan_slots_bounded spill_base ps /\
   spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    fs[generated_plan_state_wf_marked_def] >>
  `LENGTH (compute_operands inst) <= LENGTH prepared.ps_stack` by gvs[] >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops)` by
    gvs[EVERY_APPEND] >>
  `asm_block_at prog as.as_pc (execute_plan initial_fmp (iops ++ rops)) /\
   asm_block_at prog (as.as_pc + LENGTH (execute_plan initial_fmp (iops ++ rops)))
     (execute_plan initial_fmp ([SOEmit name] ++ popops ++ optops))` by
    (qpat_x_assum `asm_block_at _ _ _` mp_tac >>
     qpat_x_assum `ops = _` SUBST1_TAC >>
     POP_ASSUM_LIST (K all_tac) >>
     pure_rewrite_tac[execute_plan_append, asm_block_at_append, LENGTH_APPEND,
       APPEND_ASSOC, ADD_ASSOC] >> strip_tac >> asm_rewrite_tac[]) >>
  `arranged.ps_stack = stack_pop (LENGTH selected) arranged.ps_stack ++ selected` by
    (drule_all selected_input_arranged_marked >> simp[]) >>
  drule_all selected_prefix_prepared_sim_marked >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rename1 `venom_asm_rel lo arranged vs mid` >>
  suspend "prepared"
QED

Resume regular_inst_ok_sim_marked[prepared]:
  drule_all emit_input_plan_output_exclusion >> strip_tac >>
  `LENGTH selected <= 17 /\ LENGTH selected <= LENGTH prepared.ps_stack` by decide_tac >>
  drule_all reorder_plan_output_exclusion >> strip_tac >>
  `emitted = arranged with ps_stack :=
    FOLDL (\stk out. stack_push (Var out) stk)
      (stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack) inst.inst_outputs` by
    simp[emit_output_fold_stack] >>
  `LENGTH inst.inst_outputs <= 1` by metis_tac[regular_named_output_bound] >>
  drule_all materialised_emit_resources_marked >> strip_tac >>
  `!out. inst.inst_outputs = [out] ==>
    stack_get_depth (Var out) emitted.ps_stack = SOME 0` by
    (rpt strip_tac >> irule materialised_emit_singleton_depth >> metis_tac[]) >>
  `arranged.ps_alloc.sa_spill_base = ps'.ps_alloc.sa_spill_base /\
   arranged.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset` by
    (drule_all regular_postfix_alloc_frame >>
     simp[emit_output_fold_alloc]) >>
  `EVERY (\(off,len). len = 0 \/ off + len <= arranged.ps_alloc.sa_spill_base \/
      arranged.ps_alloc.sa_next_offset <= off) (source_memory_read_ranges inst vs) /\
   inst_memory_safe arranged.ps_alloc inst vs vs'` by
    (irule regular_emit_memory_transport >> qexists `ps'` >> simp[]) >>
  `~is_pre_codegen_opcode inst.inst_opcode` by
    (`!bbs. EVERY (\bb. EVERY codegen_ready_inst bb.bb_instructions) bbs ==>
        EVERY codegen_ready_inst (fn_insts_blocks bbs)` by
       (Induct >> simp[fn_insts_blocks_def]) >>
     qpat_x_assum `codegen_ready_fn fn` mp_tac >>
     qpat_x_assum `MEM inst (fn_insts fn)` mp_tac >>
     qpat_x_assum `!bbs. _ ==> EVERY codegen_ready_inst _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[codegen_ready_fn_def, fn_insts_def, EVERY_MEM, codegen_ready_inst_def] >>
     metis_tac[]) >>
  `plan_slots_bounded spill_base arranged` by
    fs[plan_state_residual_wf_marked_def] >>
  `EVERY (\op. op <> dead_stack_marker) (compute_operands inst)` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  suspend "emit_ready"
QED

Resume regular_inst_ok_sim_marked[emit_ready]:
  drule_all regular_emit_ok_sim >>
  disch_then (qspec_then `o2pc` (qx_choose_then `after_emit` strip_assume_tac)) >>
  `venom_asm_rel lo emitted vs' after_emit` by metis_tac[] >>
  `asm_block_at prog mid.as_pc (execute_plan initial_fmp ([SOEmit name] ++ popops ++ optops))` by
    metis_tac[] >>
  `asm_block_at prog mid.as_pc [AsmOp name] /\
   asm_block_at prog after_emit.as_pc (execute_plan initial_fmp (popops ++ optops))` by
    (qpat_x_assum `asm_block_at prog mid.as_pc _` mp_tac >>
     qpat_x_assum `after_emit.as_pc = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     pure_rewrite_tac[execute_plan_append, execute_plan_def, exec_stack_op_def,
       MAP, FLAT, APPEND, asm_block_at_append, asm_block_at_cons] >>
     rpt strip_tac >> asm_rewrite_tac[asm_block_at_nil] >> decide_tac) >>
  suspend "emitted"
QED

Resume regular_inst_ok_sim_marked[emitted]:
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
     | SORestore off => off < dimword(:256) | _ => T) optops` by
    gvs[EVERY_APPEND] >>
  `spill_alloc_layout_wf emitted.ps_alloc emitted.ps_spilled` by
    fs[generated_plan_state_wf_marked_def] >>
  `(if inst.inst_outputs = [] \/ is_halting then ([],emitted)
    else popmany_plan (MAP Var (FILTER (\out. ~MEM out next_liveness)
      inst.inst_outputs)) emitted) = (popops,popped)` by
    (`~(LENGTH inst.inst_outputs > 1)` by decide_tac >>
     qpat_x_assum `if inst.inst_outputs = [] \/ _ then (popops,popped) = _ else _` mp_tac >>
     qpat_x_assum `~(LENGTH inst.inst_outputs > 1)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >> IF_CASES_TAC >> gvs[]) >>
  `(if FILTER (\out. MEM out next_liveness) inst.inst_outputs = [] then ([],popped)
    else optimistic_swap_plan dfg inst next_liveness next_is_term popped) = (optops,tail)` by
    (qpat_x_assum `if inst.inst_outputs = [] \/ FILTER _ _ = [] then _ else _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `inst.inst_outputs = []` >> simp[] >> IF_CASES_TAC >> simp[]) >>
  drule_all regular_generated_postfix_sim_numeric >>
  disch_then (qspec_then `o2pc` (qx_choose_then `endpoint` strip_assume_tac)) >>
  `asm_steps lo o2pc prog 1 mid = AsmOK after_emit` by
    (qpat_x_assum `asm_block_at prog mid.as_pc [AsmOp name]` mp_tac >>
     qpat_x_assum `asm_step_op o2pc name mid = AsmOK after_emit` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     once_rewrite_tac[arithmeticTheory.ONE] >>
     simp[asm_steps_def, asm_step_def, asm_block_at_def]) >>
  suspend "postfix_done"
QED

Resume regular_inst_ok_sim_marked[postfix_done]:
  qexistsl_tac [`LENGTH (execute_plan initial_fmp (iops ++ rops)) +
    (1 + LENGTH (execute_plan initial_fmp (popops ++ optops)))`, `endpoint`] >>
  conj_tac
  >- (irule asm_steps_compose_ok >> qexists `mid` >> conj_tac
      >- asm_rewrite_tac[] >>
      irule asm_steps_compose_ok >> qexists `after_emit` >> asm_rewrite_tac[]) >>
  conj_tac >- asm_rewrite_tac[] >>
  strip_tac >>
  qpat_x_assum `ops = _` SUBST1_TAC >>
  qpat_x_assum `endpoint.as_pc = _` mp_tac >>
  qpat_x_assum `after_emit.as_pc = _` mp_tac >>
  qpat_x_assum `mid.as_pc = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  pure_rewrite_tac[execute_plan_append, execute_plan_def, APPEND, LENGTH_APPEND, LENGTH] >>
  simp[exec_stack_op_def] >> decide_tac
QED

Finalise regular_inst_ok_sim_marked

(* The ASSIGN case of gen_inst_ok_sim_marked. *)
Theorem assign_inst_ok_sim_marked:
  !fuel ctx lo o2pc prog
   liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label base ps vs as ops ps' initial_fmp.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = ASSIGN /\
    inst.inst_opcode <> INVOKE /\
    (* GAS readings are opaque at this level: venom_asm_rel deliberately does
       not relate them to Venom's GAS value.  The frame-aware invariant owns
       GAS, as it owns INVOKE. *)
    inst.inst_opcode <> GAS /\
    (* inst_wf fixes only the output count of the zero-operand reads; extra
       operands would be left on the assembly stack by the EVM opcode. *)
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    (* Source memory reads avoid the compiler-owned spill interval, mirroring
       source_memory_writes_disjoint and the context-level
       source_memory_reads_disjoint; memory_rel says nothing inside it. *)
    EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
                       ps'.ps_alloc.sa_next_offset <= off)
      (source_memory_read_ranges inst vs) /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    (* Jumps are simulated against the frame invariant (genFrameSim), whose
       statements carry the join-reorder and target-resolution premises a
       jump needs and land at the target block's pc.  DJMP is outside
       unit_shape_ok, and Venom's DJMP indexes its label list while the
       generated code jumps to the selector value. *)
    ~MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
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
    (* Every variable input is on the stack at any depth or spilled. *)
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (* Label resolution: all label operands in label_offsets.
       Pipeline obligation from compute_label_offsets over full program. *)
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (* Labels defined in the instruction's own code resolve to their own
       positions (labels are unique in prog). *)
    (!lbl i. i < LENGTH (execute_plan initial_fmp ops) /\
             EL i (execute_plan initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (* Cross-layer operand evaluation agreement.  In particular, Label
       operands must agree between vs_labels and generated label offsets. *)
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op vs = operand_val vs lo op) /\
    (* DFG alias soundness: planner-equivalent operands denote the same
       runtime word under the current value state and label environment.
       This is an explicit pipeline obligation for alias-only reorder steps. *)
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val vs lo op = operand_val vs lo at) /\
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
       operand_val vs lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op vs) /\
    (* Spill and restore offsets fit a PUSH. *)
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs as /\
    n2w initial_fmp = vs.vs_initial_fmp /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
          inst_memory_safe ps'.ps_alloc inst vs vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as' /\
        (~is_terminator inst.inst_opcode ==>
         as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp ops))
Proof
  cheat
QED

(* The LOG case of gen_inst_ok_sim_marked. *)
Theorem log_inst_ok_sim_marked:
  !fuel ctx lo o2pc prog
   liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label base ps vs as ops ps' initial_fmp.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = LOG /\
    inst.inst_opcode <> INVOKE /\
    (* GAS readings are opaque at this level: venom_asm_rel deliberately does
       not relate them to Venom's GAS value.  The frame-aware invariant owns
       GAS, as it owns INVOKE. *)
    inst.inst_opcode <> GAS /\
    (* inst_wf fixes only the output count of the zero-operand reads; extra
       operands would be left on the assembly stack by the EVM opcode. *)
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    (* Source memory reads avoid the compiler-owned spill interval, mirroring
       source_memory_writes_disjoint and the context-level
       source_memory_reads_disjoint; memory_rel says nothing inside it. *)
    EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
                       ps'.ps_alloc.sa_next_offset <= off)
      (source_memory_read_ranges inst vs) /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    (* Jumps are simulated against the frame invariant (genFrameSim), whose
       statements carry the join-reorder and target-resolution premises a
       jump needs and land at the target block's pc.  DJMP is outside
       unit_shape_ok, and Venom's DJMP indexes its label list while the
       generated code jumps to the selector value. *)
    ~MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
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
    (* Every variable input is on the stack at any depth or spilled. *)
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (* Label resolution: all label operands in label_offsets.
       Pipeline obligation from compute_label_offsets over full program. *)
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (* Labels defined in the instruction's own code resolve to their own
       positions (labels are unique in prog). *)
    (!lbl i. i < LENGTH (execute_plan initial_fmp ops) /\
             EL i (execute_plan initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (* Cross-layer operand evaluation agreement.  In particular, Label
       operands must agree between vs_labels and generated label offsets. *)
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op vs = operand_val vs lo op) /\
    (* DFG alias soundness: planner-equivalent operands denote the same
       runtime word under the current value state and label environment.
       This is an explicit pipeline obligation for alias-only reorder steps. *)
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val vs lo op = operand_val vs lo at) /\
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
       operand_val vs lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op vs) /\
    (* Spill and restore offsets fit a PUSH. *)
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs as /\
    n2w initial_fmp = vs.vs_initial_fmp /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
          inst_memory_safe ps'.ps_alloc inst vs vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as' /\
        (~is_terminator inst.inst_opcode ==>
         as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp ops))
Proof
  cheat
QED

(* The ASSERT case of gen_inst_ok_sim_marked. *)
Theorem assert_inst_ok_sim_marked:
  !fuel ctx lo o2pc prog
   liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label base ps vs as ops ps' initial_fmp.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = ASSERT /\
    inst.inst_opcode <> INVOKE /\
    (* GAS readings are opaque at this level: venom_asm_rel deliberately does
       not relate them to Venom's GAS value.  The frame-aware invariant owns
       GAS, as it owns INVOKE. *)
    inst.inst_opcode <> GAS /\
    (* inst_wf fixes only the output count of the zero-operand reads; extra
       operands would be left on the assembly stack by the EVM opcode. *)
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    (* Source memory reads avoid the compiler-owned spill interval, mirroring
       source_memory_writes_disjoint and the context-level
       source_memory_reads_disjoint; memory_rel says nothing inside it. *)
    EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
                       ps'.ps_alloc.sa_next_offset <= off)
      (source_memory_read_ranges inst vs) /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    (* Jumps are simulated against the frame invariant (genFrameSim), whose
       statements carry the join-reorder and target-resolution premises a
       jump needs and land at the target block's pc.  DJMP is outside
       unit_shape_ok, and Venom's DJMP indexes its label list while the
       generated code jumps to the selector value. *)
    ~MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
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
    (* Every variable input is on the stack at any depth or spilled. *)
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (* Label resolution: all label operands in label_offsets.
       Pipeline obligation from compute_label_offsets over full program. *)
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (* Labels defined in the instruction's own code resolve to their own
       positions (labels are unique in prog). *)
    (!lbl i. i < LENGTH (execute_plan initial_fmp ops) /\
             EL i (execute_plan initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (* Cross-layer operand evaluation agreement.  In particular, Label
       operands must agree between vs_labels and generated label offsets. *)
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op vs = operand_val vs lo op) /\
    (* DFG alias soundness: planner-equivalent operands denote the same
       runtime word under the current value state and label environment.
       This is an explicit pipeline obligation for alias-only reorder steps. *)
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val vs lo op = operand_val vs lo at) /\
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
       operand_val vs lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op vs) /\
    (* Spill and restore offsets fit a PUSH. *)
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs as /\
    n2w initial_fmp = vs.vs_initial_fmp /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
          inst_memory_safe ps'.ps_alloc inst vs vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as' /\
        (~is_terminator inst.inst_opcode ==>
         as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp ops))
Proof
  cheat
QED

(* The ASSERT_UNREACHABLE case of gen_inst_ok_sim_marked. *)
Theorem assert_unreachable_inst_ok_sim_marked:
  !fuel ctx lo o2pc prog
   liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label base ps vs as ops ps' initial_fmp.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = ASSERT_UNREACHABLE /\
    inst.inst_opcode <> INVOKE /\
    (* GAS readings are opaque at this level: venom_asm_rel deliberately does
       not relate them to Venom's GAS value.  The frame-aware invariant owns
       GAS, as it owns INVOKE. *)
    inst.inst_opcode <> GAS /\
    (* inst_wf fixes only the output count of the zero-operand reads; extra
       operands would be left on the assembly stack by the EVM opcode. *)
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    (* Source memory reads avoid the compiler-owned spill interval, mirroring
       source_memory_writes_disjoint and the context-level
       source_memory_reads_disjoint; memory_rel says nothing inside it. *)
    EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
                       ps'.ps_alloc.sa_next_offset <= off)
      (source_memory_read_ranges inst vs) /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    (* Jumps are simulated against the frame invariant (genFrameSim), whose
       statements carry the join-reorder and target-resolution premises a
       jump needs and land at the target block's pc.  DJMP is outside
       unit_shape_ok, and Venom's DJMP indexes its label list while the
       generated code jumps to the selector value. *)
    ~MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
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
    (* Every variable input is on the stack at any depth or spilled. *)
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (* Label resolution: all label operands in label_offsets.
       Pipeline obligation from compute_label_offsets over full program. *)
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (* Labels defined in the instruction's own code resolve to their own
       positions (labels are unique in prog). *)
    (!lbl i. i < LENGTH (execute_plan initial_fmp ops) /\
             EL i (execute_plan initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (* Cross-layer operand evaluation agreement.  In particular, Label
       operands must agree between vs_labels and generated label offsets. *)
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op vs = operand_val vs lo op) /\
    (* DFG alias soundness: planner-equivalent operands denote the same
       runtime word under the current value state and label environment.
       This is an explicit pipeline obligation for alias-only reorder steps. *)
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val vs lo op = operand_val vs lo at) /\
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
       operand_val vs lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op vs) /\
    (* Spill and restore offsets fit a PUSH. *)
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs as /\
    n2w initial_fmp = vs.vs_initial_fmp /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
          inst_memory_safe ps'.ps_alloc inst vs vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as' /\
        (~is_terminator inst.inst_opcode ==>
         as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp ops))
Proof
  cheat
QED

(* The PHI case of gen_inst_ok_sim_marked. *)
Theorem phi_inst_ok_sim_marked:
  !fuel ctx lo o2pc prog
   liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label base ps vs as ops ps' initial_fmp.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = PHI /\
    inst.inst_opcode <> INVOKE /\
    (* GAS readings are opaque at this level: venom_asm_rel deliberately does
       not relate them to Venom's GAS value.  The frame-aware invariant owns
       GAS, as it owns INVOKE. *)
    inst.inst_opcode <> GAS /\
    (* inst_wf fixes only the output count of the zero-operand reads; extra
       operands would be left on the assembly stack by the EVM opcode. *)
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    (* Source memory reads avoid the compiler-owned spill interval, mirroring
       source_memory_writes_disjoint and the context-level
       source_memory_reads_disjoint; memory_rel says nothing inside it. *)
    EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
                       ps'.ps_alloc.sa_next_offset <= off)
      (source_memory_read_ranges inst vs) /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    (* Jumps are simulated against the frame invariant (genFrameSim), whose
       statements carry the join-reorder and target-resolution premises a
       jump needs and land at the target block's pc.  DJMP is outside
       unit_shape_ok, and Venom's DJMP indexes its label list while the
       generated code jumps to the selector value. *)
    ~MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
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
    (* Every variable input is on the stack at any depth or spilled. *)
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (* Label resolution: all label operands in label_offsets.
       Pipeline obligation from compute_label_offsets over full program. *)
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (* Labels defined in the instruction's own code resolve to their own
       positions (labels are unique in prog). *)
    (!lbl i. i < LENGTH (execute_plan initial_fmp ops) /\
             EL i (execute_plan initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (* Cross-layer operand evaluation agreement.  In particular, Label
       operands must agree between vs_labels and generated label offsets. *)
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op vs = operand_val vs lo op) /\
    (* DFG alias soundness: planner-equivalent operands denote the same
       runtime word under the current value state and label environment.
       This is an explicit pipeline obligation for alias-only reorder steps. *)
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val vs lo op = operand_val vs lo at) /\
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
       operand_val vs lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op vs) /\
    (* Spill and restore offsets fit a PUSH. *)
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs as /\
    n2w initial_fmp = vs.vs_initial_fmp /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
          inst_memory_safe ps'.ps_alloc inst vs vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as' /\
        (~is_terminator inst.inst_opcode ==>
         as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp ops))
Proof
  cheat
QED

(* The INITIAL_FMP case of gen_inst_ok_sim_marked. *)
Theorem initial_fmp_inst_ok_sim_marked:
  !fuel ctx lo o2pc prog
   liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label base ps vs as ops ps' initial_fmp.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = INITIAL_FMP /\
    inst.inst_opcode <> INVOKE /\
    (* GAS readings are opaque at this level: venom_asm_rel deliberately does
       not relate them to Venom's GAS value.  The frame-aware invariant owns
       GAS, as it owns INVOKE. *)
    inst.inst_opcode <> GAS /\
    (* inst_wf fixes only the output count of the zero-operand reads; extra
       operands would be left on the assembly stack by the EVM opcode. *)
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    (* Source memory reads avoid the compiler-owned spill interval, mirroring
       source_memory_writes_disjoint and the context-level
       source_memory_reads_disjoint; memory_rel says nothing inside it. *)
    EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
                       ps'.ps_alloc.sa_next_offset <= off)
      (source_memory_read_ranges inst vs) /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    (* Jumps are simulated against the frame invariant (genFrameSim), whose
       statements carry the join-reorder and target-resolution premises a
       jump needs and land at the target block's pc.  DJMP is outside
       unit_shape_ok, and Venom's DJMP indexes its label list while the
       generated code jumps to the selector value. *)
    ~MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
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
    (* Every variable input is on the stack at any depth or spilled. *)
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (* Label resolution: all label operands in label_offsets.
       Pipeline obligation from compute_label_offsets over full program. *)
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (* Labels defined in the instruction's own code resolve to their own
       positions (labels are unique in prog). *)
    (!lbl i. i < LENGTH (execute_plan initial_fmp ops) /\
             EL i (execute_plan initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (* Cross-layer operand evaluation agreement.  In particular, Label
       operands must agree between vs_labels and generated label offsets. *)
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op vs = operand_val vs lo op) /\
    (* DFG alias soundness: planner-equivalent operands denote the same
       runtime word under the current value state and label environment.
       This is an explicit pipeline obligation for alias-only reorder steps. *)
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val vs lo op = operand_val vs lo at) /\
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
       operand_val vs lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op vs) /\
    (* Spill and restore offsets fit a PUSH. *)
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs as /\
    n2w initial_fmp = vs.vs_initial_fmp /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
          inst_memory_safe ps'.ps_alloc inst vs vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as' /\
        (~is_terminator inst.inst_opcode ==>
         as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp ops))
Proof
  cheat
QED

(* The BUMP case of gen_inst_ok_sim_marked. *)
Theorem bump_inst_ok_sim_marked:
  !fuel ctx lo o2pc prog
   liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label base ps vs as ops ps' initial_fmp.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = BUMP /\
    inst.inst_opcode <> INVOKE /\
    (* GAS readings are opaque at this level: venom_asm_rel deliberately does
       not relate them to Venom's GAS value.  The frame-aware invariant owns
       GAS, as it owns INVOKE. *)
    inst.inst_opcode <> GAS /\
    (* inst_wf fixes only the output count of the zero-operand reads; extra
       operands would be left on the assembly stack by the EVM opcode. *)
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    (* Source memory reads avoid the compiler-owned spill interval, mirroring
       source_memory_writes_disjoint and the context-level
       source_memory_reads_disjoint; memory_rel says nothing inside it. *)
    EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
                       ps'.ps_alloc.sa_next_offset <= off)
      (source_memory_read_ranges inst vs) /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    (* Jumps are simulated against the frame invariant (genFrameSim), whose
       statements carry the join-reorder and target-resolution premises a
       jump needs and land at the target block's pc.  DJMP is outside
       unit_shape_ok, and Venom's DJMP indexes its label list while the
       generated code jumps to the selector value. *)
    ~MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
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
    (* Every variable input is on the stack at any depth or spilled. *)
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (* Label resolution: all label operands in label_offsets.
       Pipeline obligation from compute_label_offsets over full program. *)
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (* Labels defined in the instruction's own code resolve to their own
       positions (labels are unique in prog). *)
    (!lbl i. i < LENGTH (execute_plan initial_fmp ops) /\
             EL i (execute_plan initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (* Cross-layer operand evaluation agreement.  In particular, Label
       operands must agree between vs_labels and generated label offsets. *)
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op vs = operand_val vs lo op) /\
    (* DFG alias soundness: planner-equivalent operands denote the same
       runtime word under the current value state and label environment.
       This is an explicit pipeline obligation for alias-only reorder steps. *)
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val vs lo op = operand_val vs lo at) /\
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
       operand_val vs lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op vs) /\
    (* Spill and restore offsets fit a PUSH. *)
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs as /\
    n2w initial_fmp = vs.vs_initial_fmp /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
          inst_memory_safe ps'.ps_alloc inst vs vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as' /\
        (~is_terminator inst.inst_opcode ==>
         as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp ops))
Proof
  cheat
QED

(* The ISTORE case of gen_inst_ok_sim_marked. *)
Theorem istore_inst_ok_sim_marked:
  !fuel ctx lo o2pc prog
   liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label base ps vs as ops ps' initial_fmp.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = ISTORE /\
    inst.inst_opcode <> INVOKE /\
    (* GAS readings are opaque at this level: venom_asm_rel deliberately does
       not relate them to Venom's GAS value.  The frame-aware invariant owns
       GAS, as it owns INVOKE. *)
    inst.inst_opcode <> GAS /\
    (* inst_wf fixes only the output count of the zero-operand reads; extra
       operands would be left on the assembly stack by the EVM opcode. *)
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    (* Source memory reads avoid the compiler-owned spill interval, mirroring
       source_memory_writes_disjoint and the context-level
       source_memory_reads_disjoint; memory_rel says nothing inside it. *)
    EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
                       ps'.ps_alloc.sa_next_offset <= off)
      (source_memory_read_ranges inst vs) /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    (* Jumps are simulated against the frame invariant (genFrameSim), whose
       statements carry the join-reorder and target-resolution premises a
       jump needs and land at the target block's pc.  DJMP is outside
       unit_shape_ok, and Venom's DJMP indexes its label list while the
       generated code jumps to the selector value. *)
    ~MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
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
    (* Every variable input is on the stack at any depth or spilled. *)
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (* Label resolution: all label operands in label_offsets.
       Pipeline obligation from compute_label_offsets over full program. *)
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (* Labels defined in the instruction's own code resolve to their own
       positions (labels are unique in prog). *)
    (!lbl i. i < LENGTH (execute_plan initial_fmp ops) /\
             EL i (execute_plan initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (* Cross-layer operand evaluation agreement.  In particular, Label
       operands must agree between vs_labels and generated label offsets. *)
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op vs = operand_val vs lo op) /\
    (* DFG alias soundness: planner-equivalent operands denote the same
       runtime word under the current value state and label environment.
       This is an explicit pipeline obligation for alias-only reorder steps. *)
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val vs lo op = operand_val vs lo at) /\
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
       operand_val vs lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op vs) /\
    (* Spill and restore offsets fit a PUSH. *)
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs as /\
    n2w initial_fmp = vs.vs_initial_fmp /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
          inst_memory_safe ps'.ps_alloc inst vs vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as' /\
        (~is_terminator inst.inst_opcode ==>
         as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp ops))
Proof
  cheat
QED

fun ok_case_lemma_tac th =
  mp_tac th >>
  disch_then (qspecl_then [`fuel`, `ctx`, `lo`, `o2pc`, `prog`, `liveness`,
    `dfg`, `cfg`, `fn`, `inst`, `next_liveness`, `is_halting`,
    `next_is_term`, `bb_label`, `base'`, `ps`, `vs`, `as`, `ops`, `ps'`,
    `initial_fmp`]
    mp_tac) >>
  impl_tac >- ASM_REWRITE_TAC[] >>
  disch_then (qspec_then `vs'` mp_tac) >> ASM_REWRITE_TAC[];

Theorem gen_inst_ok_sim_marked:
  !fuel ctx lo o2pc prog
   liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label base ps vs as ops ps' initial_fmp.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\
    (* GAS readings are opaque at this level: venom_asm_rel deliberately does
       not relate them to Venom's GAS value.  The frame-aware invariant owns
       GAS, as it owns INVOKE. *)
    inst.inst_opcode <> GAS /\
    (* inst_wf fixes only the output count of the zero-operand reads; extra
       operands would be left on the assembly stack by the EVM opcode. *)
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    (* Source memory reads avoid the compiler-owned spill interval, mirroring
       source_memory_writes_disjoint and the context-level
       source_memory_reads_disjoint; memory_rel says nothing inside it. *)
    EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
                       ps'.ps_alloc.sa_next_offset <= off)
      (source_memory_read_ranges inst vs) /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    (* Jumps are simulated against the frame invariant (genFrameSim), whose
       statements carry the join-reorder and target-resolution premises a
       jump needs and land at the target block's pc.  DJMP is outside
       unit_shape_ok, and Venom's DJMP indexes its label list while the
       generated code jumps to the selector value. *)
    ~MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
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
    (* Every variable input is on the stack at any depth or spilled. *)
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (* Label resolution: all label operands in label_offsets.
       Pipeline obligation from compute_label_offsets over full program. *)
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (* Labels defined in the instruction's own code resolve to their own
       positions (labels are unique in prog). *)
    (!lbl i. i < LENGTH (execute_plan initial_fmp ops) /\
             EL i (execute_plan initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (* Cross-layer operand evaluation agreement.  In particular, Label
       operands must agree between vs_labels and generated label offsets. *)
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op vs = operand_val vs lo op) /\
    (* DFG alias soundness: planner-equivalent operands denote the same
       runtime word under the current value state and label environment.
       This is an explicit pipeline obligation for alias-only reorder steps. *)
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val vs lo op = operand_val vs lo at) /\
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
       operand_val vs lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op vs) /\
    (* Spill and restore offsets fit a PUSH. *)
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs as /\
    n2w initial_fmp = vs.vs_initial_fmp /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
          inst_memory_safe ps'.ps_alloc inst vs vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as' /\
        (~is_terminator inst.inst_opcode ==>
         as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp ops))
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = ASSIGN`
  >- ok_case_lemma_tac assign_inst_ok_sim_marked >>
  Cases_on `inst.inst_opcode = LOG`
  >- ok_case_lemma_tac log_inst_ok_sim_marked >>
  Cases_on `inst.inst_opcode = ASSERT`
  >- ok_case_lemma_tac assert_inst_ok_sim_marked >>
  Cases_on `inst.inst_opcode = ASSERT_UNREACHABLE`
  >- ok_case_lemma_tac assert_unreachable_inst_ok_sim_marked >>
  Cases_on `inst.inst_opcode = PHI`
  >- ok_case_lemma_tac phi_inst_ok_sim_marked >>
  Cases_on `inst.inst_opcode = INITIAL_FMP`
  >- ok_case_lemma_tac initial_fmp_inst_ok_sim_marked >>
  Cases_on `inst.inst_opcode = BUMP`
  >- ok_case_lemma_tac bump_inst_ok_sim_marked >>
  Cases_on `inst.inst_opcode = ISTORE`
  >- ok_case_lemma_tac istore_inst_ok_sim_marked >>
  (* Do not substitute concrete maps into the preserved map-parametric proofs. *)
  qpat_x_assum `lo = SND (compute_label_offsets prog)` kall_tac >>
  qpat_x_assum `o2pc = build_offset_to_pc prog` kall_tac >>
  (* Dispatch on generate_inst_plan cases *)
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once generate_inst_plan_def, is_param_opcode_def] >>
  strip_tac >>
  (* is_pre_codegen eliminated by SOME <> NONE *)
  (* Now case split on opcode *)
  Cases_on `inst.inst_opcode = PHI` >- gvs[] >>
  Cases_on `inst.inst_opcode = OFFSET` >- (gvs[] >> suspend "offset") >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (gvs[is_param_opcode_def] >> suspend "param") >>
  Cases_on `inst.inst_opcode = FMP_PARAM`
  >- (gvs[is_param_opcode_def] >> suspend "fmp_param") >>
  Cases_on `inst.inst_opcode = RETPC_PARAM`
  >- (gvs[is_param_opcode_def] >> suspend "retpc_param") >>
  `~is_param_opcode inst.inst_opcode` by simp[is_param_opcode_iff] >>
  gvs[] >>
  Cases_on `inst.inst_opcode = NOP`
  >- (
    gvs[] >> imp_res_tac step_inst_nop_ok >> gvs[] >>
    qexistsl_tac [`0`, `as`] >> simp[asm_steps_def, execute_plan_def]
  ) >>
  (* Regular instruction: dispatch by opcode family *)
  Cases_on `inst.inst_opcode = INVOKE` >- gvs[] >>
  Cases_on `venom_to_evm_name inst.inst_opcode`
  >- (
    (* NONE case: ASSIGN, ISTORE, JMP, JNZ, DJMP, LOG, ASSERT, etc. *)
    gvs[] >> suspend "none"
  ) >>
  rename1 `venom_to_evm_name _ = SOME name` >>
  (* SOME name case: 3-phase plan (prefix + emit + postfix) *)
  gvs[] >>
  suspend "some_name"
QED

Resume gen_inst_ok_sim_marked[offset]:
  drule_all inst_wf_offset_shape >> strip_tac >> gvs[] >>
  qpat_x_assum `generate_offset_plan _ _ = _` mp_tac >>
  simp[generate_offset_plan_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_pure2_def,
       eval_operand_def] >>
  strip_tac >> gvs[] >>
  `?off. FLOOKUP lo lbl = SOME off` by
    (Cases_on `FLOOKUP lo lbl` >> gvs[compute_operands_def]) >>
  `FLOOKUP vs.vs_labels lbl = SOME (n2w off)` by
    (qpat_x_assum `!op. MEM op (compute_operands inst) ==> _`
       (qspec_then `Label lbl` mp_tac) >>
     simp[compute_operands_def, eval_operand_def, operand_val_def]) >>
  gvs[] >>
  `v + n2w off = n2w (off + w2n v)` by
    simp[wordsTheory.word_add_def, arithmeticTheory.ADD_COMM] >>
  `~MEM (Var out) ps.ps_stack` by
    (strip_tac >>
     qpat_x_assum `EVERY _ ps.ps_stack`
       (fn th => mp_tac (REWRITE_RULE [EVERY_MEM] th)) >>
     disch_then (qspec_then `Var out` mp_tac) >> gvs[]) >>
  `Var out NOTIN FDOM ps.ps_spilled` by
    (strip_tac >>
     qpat_x_assum `!op. op IN FDOM _ ==> _`
       (qspec_then `Var out` mp_tac) >> simp[]) >>
  qspecl_then [`lo`, `o2pc`, `prog`, `ps`, `vs`, `as`, `lbl`,
               `w2n v`, `off`] mp_tac simple_op_push_ofst >>
  (impl_tac >-
    (ASM_REWRITE_TAC[] >>
     qpat_x_assum `asm_block_at _ _ (execute_plan _ _)` mp_tac >>
     simp[execute_plan_def, exec_stack_op_def])) >>
  strip_tac >>
  `venom_asm_rel lo
      (ps with ps_stack := stack_push (Var out) ps.ps_stack)
      (update_var out (v + n2w off) vs) st'` by
    (simp[stack_push_def] >>
     irule venom_asm_rel_push_lit_as_fresh_var >>
     ASM_REWRITE_TAC[]) >>
  qexistsl [`1`, `st'`] >> ASM_REWRITE_TAC[] >>
  simp[execute_plan_def, exec_stack_op_def]
QED

Resume gen_inst_ok_sim_marked[param]:
  qexistsl [`0`, `as`] >> simp[asm_steps_def, execute_plan_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  qpat_x_assum `inst_wf inst` mp_tac >>
  simp[inst_wf_def] >> strip_tac >> gvs[] >>
  `?out. inst.inst_outputs = [out]` by
    (Cases_on `inst.inst_outputs` >> fs[] >> Cases_on `t` >> fs[]) >>
  gvs[step_inst_base_def, compute_operands_def, eval_operand_def] >>
  gvs[AllCaseEqs()] >> strip_tac >> gvs[] >>
  PURE_REWRITE_TAC[venom_asm_rel_def] >>
  rpt conj_tac
  >- (irule plan_stack_rel_update_var >> fs[venom_asm_rel_def])
  >- (irule plan_spill_rel_update_var >> fs[venom_asm_rel_def])
  >> fs[venom_asm_rel_def, update_var_def]
QED

Resume gen_inst_ok_sim_marked[fmp_param]:
  qexistsl [`0`, `as`] >> simp[asm_steps_def, execute_plan_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  qpat_x_assum `inst_wf inst` mp_tac >>
  simp[inst_wf_def] >> strip_tac >> gvs[] >>
  ONCE_REWRITE_TAC[step_inst_base_def] >>
  qpat_x_assum `inst.inst_opcode = FMP_PARAM`
    (fn th => PURE_REWRITE_TAC[th]) >>
  asm_simp_tac (srw_ss()) [] >>
  gvs[AllCaseEqs()] >> strip_tac >> gvs[] >>
  PURE_REWRITE_TAC[venom_asm_rel_def] >>
  rpt conj_tac
  >- (irule plan_stack_rel_update_var >> fs[venom_asm_rel_def])
  >- (irule plan_spill_rel_update_var >> fs[venom_asm_rel_def])
  >> fs[venom_asm_rel_def, update_var_def]
QED

Resume gen_inst_ok_sim_marked[retpc_param]:
  qexistsl [`0`, `as`] >> simp[asm_steps_def, execute_plan_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  qpat_x_assum `inst_wf inst` mp_tac >>
  simp[inst_wf_def] >> strip_tac >> gvs[] >>
  gvs[step_inst_base_def, compute_operands_def, eval_operand_def] >>
  gvs[AllCaseEqs()] >> strip_tac >> gvs[] >>
  PURE_REWRITE_TAC[venom_asm_rel_def] >>
  rpt conj_tac
  >- (irule plan_stack_rel_update_var >> fs[venom_asm_rel_def])
  >- (irule plan_spill_rel_update_var >> fs[venom_asm_rel_def])
  >> fs[venom_asm_rel_def, update_var_def]
QED

Resume gen_inst_ok_sim_marked[none]:
  (* Opcodes with an EVM name contradict the NONE case; drop them with a
     goal-only rewrite before the full gvs, which is slow on 100+ goals. *)
  qpat_x_assum `venom_to_evm_name _ = NONE` mp_tac >>
  Cases_on `inst.inst_opcode` >>
  simp_tac (srw_ss()) [venom_to_evm_name_def] >>
  gvs[venom_to_evm_name_def, is_pre_codegen_opcode_def,
      is_unlowered_fmp_opcode_def,
      is_unlowered_internal_call_opcode_def,
      is_raw_fmp_opcode_def, is_fmp_param_opcode_def]
  >> TRY (`inst.inst_opcode <> ISTORE /\
           inst.inst_opcode <> JMP /\
           inst.inst_opcode <> JNZ /\
           inst.inst_opcode <> DJMP /\
           inst.inst_opcode <> ASSIGN /\
           inst.inst_opcode <> LOG /\
           inst.inst_opcode <> ASSERT /\
           inst.inst_opcode <> ASSERT_UNREACHABLE` by simp[] >>
          qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
          simp[step_inst_non_invoke, Once step_inst_base_def] >>
          every_case_tac >> simp[] >> NO_TAC)
  >> gvs[]
QED

Resume gen_inst_ok_sim_marked[some_name]:
  qspecl_then [`fuel`, `ctx`, `lo`, `o2pc`, `prog`, `liveness`, `dfg`, `cfg`,
    `fn`, `inst`, `next_liveness`, `is_halting`, `next_is_term`, `bb_label`,
    `base'`, `ps`, `vs`, `as`, `ops`, `ps'`, `name`, `initial_fmp`]
    mp_tac regular_inst_ok_sim_marked >>
  ASM_REWRITE_TAC[] >>
  impl_tac >- (
    fs[EVERY_MEM, pairTheory.FORALL_PROD] >> rpt strip_tac >>
    res_tac >> gvs[]) >>
  strip_tac >> qexistsl [`n`, `as'`] >> simp[]
QED

Finalise gen_inst_ok_sim_marked
