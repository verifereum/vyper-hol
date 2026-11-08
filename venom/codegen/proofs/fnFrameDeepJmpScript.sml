(*
 * gen_jmp_frame_sim_deep: genFrameSim's gen_jmp_frame_sim for JMP, with
 * operands at any stack depth, repeated dead_stack_marker slots
 * (generated_plan_state_wf_marked) and only an address bound on the
 * plan's spill and restore offsets.  fnFrameDeep collects it with the
 * other instruction frame lemmas the block induction composes.
 *
 * TOP-LEVEL:
 *   gen_jmp_frame_sim_deep
 *)

Theory fnFrameDeepJmp
Ancestors
  deepResidualSim deepResidualBudget fnPlanPrefix genFrameSim frameRel contextCodegenRel
  codegenRel blockSimHelpers unitShapeDefs genBlockSim mixedPrefixSim
  stackPlanGen stackPlanTypes planExec asmSem venomExecSemantics venomState
  venomInst fcgDefs livenessDefs dfgDefs cfgDefs list rich_list
  asmFrame regularPostfixSim generatedReorderSim generatedPrefixSim
  planSpillBounds reorderSim prefixSim stackOpAsmSim stackOpSim
  instSimHelpers planWf frameViewStep frameViewFacts stackPlanOps stackModel
  allocMono contextCodegenRelProps asmIR venomEffects deepDupCallerSim spillPlanSim

(* ===== Restoring a join's spilled targets, with marker slots ===== *)

Theorem do_restore_generated_facts_marked[local]:
  !sb op ps ops ps'.
    do_restore op ps = (ops,ps') /\ generated_plan_state_wf_marked sb ps ==>
    generated_plan_state_wf_marked sb ps' /\
    (!pending. pending_inventory_wf pending ps ==>
               pending_inventory_wf pending ps') /\
    (!at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
          MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  `plan_slots_bounded sb ps' /\
   spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled` by
    metis_tac[do_restore_slots_bounded, do_restore_layout_wf,
              generated_plan_state_wf_marked_def] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >> gvs[do_restore_def] >>
  `op IN FDOM ps.ps_spilled` by gvs[finite_mapTheory.FLOOKUP_DEF] >>
  `~MEM op ps.ps_stack /\ op <> dead_stack_marker` by
    (gvs[generated_plan_state_wf_marked_def, pred_setTheory.IN_DISJOINT] >>
     metis_tac[]) >>
  gvs[generated_plan_state_wf_marked_def, stack_push_def, FILTER_SNOC,
      ALL_DISTINCT_SNOC, MEM_FILTER, pred_setTheory.IN_DISJOINT,
      pending_inventory_wf_def] >>
  rpt strip_tac >> gvs[]
  >~ [`LIST_ELEM_COUNT _ pending`]
  >- (rename1 `LIST_ELEM_COUNT y pending` >>
      first_x_assum (qspec_then `y` mp_tac) >>
      Cases_on `y = op` >> gvs[SNOC_APPEND, LIST_ELEM_COUNT_THM]) >>
  metis_tac[]
QED

Theorem restore_spilled_plan_generated_facts_marked[local]:
  !targets sb ps ops ps'.
    restore_spilled_plan targets ps = (ops,ps') /\
    generated_plan_state_wf_marked sb ps ==>
    generated_plan_state_wf_marked sb ps' /\
    (!pending. pending_inventory_wf pending ps ==>
               pending_inventory_wf pending ps') /\
    (!at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
          MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled)
Proof
  Induct >> simp[restore_spilled_plan_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule_all do_restore_generated_facts_marked >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> metis_tac[]
QED

Theorem residual_budget_wf_marked_nil_pending[local]:
  !base pending ps.
    residual_budget_wf_marked base [] ps ==>
    residual_budget_wf_marked base pending ps
Proof
  rw[residual_budget_wf_marked_def, LIST_ELEM_COUNT_THM] >>
  res_tac >> decide_tac
QED

(* gen_jmp_frame_sim with any-depth ownership, generated_plan_state_wf_marked and an
   address bound on spill and restore offsets. *)
Theorem gen_jmp_frame_sim_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   target target_bb target_stack off pc_t.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = JMP /\
    inst.inst_operands = [Label target] /\
    inst.inst_outputs = [] /\
    lookup_block target fn.fn_blocks = SOME target_bb /\
    target_stack =
      MAP Var (input_vars_from bb_label target_bb.bb_instructions
                 (live_vars_at liveness target 0)) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\
    (!off. MEM (SORestore off) (FST (restore_spilled_plan target_stack ps)) ==>
           off < dimword(:256)) /\
    LENGTH target_stack <=
      LENGTH (SND (restore_spilled_plan target_stack ps)).ps_stack /\
    pending_inventory_wf target_stack ps /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      target_stack /\
    (!op at. MEM op target_stack /\
       (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
       operand_equiv dfg op at ==>
       operand_val (frame_view fn ra vs) lo op =
       operand_val (frame_view fn ra vs) lo at) /\
    FLOOKUP lo target = SOME off /\ off < dimword (:256) /\
    FLOOKUP o2pc off = SOME pc_t /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst next_liveness is_halting
      next_is_term bb_label ps = SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        fn_frame_inv ctx cp lo fn ra rest mem0 ps' vs' as' /\
        as'.as_pc = pc_t /\
        vs' = jump_to target vs
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  rename1 `MEM r cplan.cp_regions` >>
  rename1 `generated_plan_state_wf_marked b0 ps` >>
  qpat_x_assum `lo = _` kall_tac >> qpat_x_assum `o2pc = _` kall_tac >>
  (* Venom: JMP is jump_to. *)
  `vs' = jump_to target vs` by (
    qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
    `inst.inst_opcode <> INVOKE` by simp[] >>
    simp[step_inst_non_invoke, step_inst_base_def]) >>
  pop_assum SUBST_ALL_TAC >>
  (* Planner: ops = join_ops ++ [PUSH target; JUMP], ps' releases spills. *)
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_jmp] >> strip_tac >>
  qpat_x_assum `join_reached _ _ _ _ _` kall_tac >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def, compute_operands_def,
       get_non_label_operands_def, is_commutative_def,
       venom_to_evm_name_def, generate_emit_ops_def, stack_pop_def,
       join_target_ops_def] >>
  qpat_x_assum `target_stack = _` (SUBST_ALL_TAC o SYM) >>
  Cases_on `restore_spilled_plan target_stack ps` >>
  rename1 `restore_spilled_plan target_stack ps = (rest_ops, psr)` >>
  Cases_on `reorder_plan dfg target_stack psr` >>
  rename1 `reorder_plan dfg target_stack psr = (swap_ops, ps2)` >>
  simp[] >> strip_tac >>
  qpat_x_assum `_ = ops` (SUBST_ALL_TAC o GSYM) >>
  qpat_x_assum `_ = ps'` (SUBST_ALL_TAC o GSYM) >>
  qpat_x_assum `restore_spilled_plan _ _ = _` (fn th =>
    RULE_ASSUM_TAC (REWRITE_RULE [th, pairTheory.FST, pairTheory.SND]) >>
    assume_tac th) >>
  `generated_plan_state_wf_marked b0 psr /\ pending_inventory_wf target_stack psr /\
   (!at. MEM at psr.ps_stack \/ at IN FDOM psr.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled)` by (
    drule_all restore_spilled_plan_generated_facts_marked >> metis_tac[]) >>
  (* The frame invariant, on the frame's own stack. *)
  qpat_x_assum `fn_frame_inv _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[fn_frame_inv_def] >> strip_tac >>
  qabbrev_tac `st0 = as with as_stack := top` >>
  qabbrev_tac `vsf = frame_view fn ra vs with vs_memory := as.as_memory` >>
  `venom_asm_rel lo ps vsf st0` by (
    drule context_venom_asm_rel_local >> simp[Abbr`vsf`, Abbr`st0`]) >>
  (* Restore the spilled join targets. *)
  qabbrev_tac `nr = LENGTH (execute_plan cplan.cp_initial_fmp rest_ops)` >>
  `?str. asm_steps lo o2pc prog nr st0 = AsmOK str /\
         venom_asm_rel lo psr vsf str /\ str.as_pc = as.as_pc + nr` by (
    qspecl_then [`target_stack`, `ps`, `rest_ops`, `psr`, `lo`, `o2pc`,
                 `prog`, `vsf`, `st0`, `cplan.cp_initial_fmp`] mp_tac
      restore_spilled_plan_venom_asm_rel >>
    impl_tac >- (
      simp[Abbr`st0`] >> gvs[execute_plan_append, asm_block_at_append]) >>
    strip_tac >> simp[Abbr`nr`] >> simp[Abbr`st0`] >> metis_tac[]) >>
  (* Join reorder. *)
  qabbrev_tac `ns = LENGTH (execute_plan cplan.cp_initial_fmp swap_ops)` >>
  `?st1. asm_steps lo o2pc prog ns str = AsmOK st1 /\
         venom_asm_rel lo ps2 vsf st1 /\ st1.as_pc = str.as_pc + ns` by (
    qspecl_then [`dfg`, `target_stack`, `psr`, `swap_ops`, `ps2`, `b0`,
                 `lo`, `o2pc`, `prog`, `vsf`, `str`] mp_tac
      (Q.INST [`initial_fmp` |-> `cplan.cp_initial_fmp`]
         reorder_plan_venom_asm_rel_numeric_marked) >>
    impl_tac >- (
      simp[] >> rpt conj_tac
      >~ [`residual_budget_wf_marked`]
      >- (irule residual_budget_wf_marked_nil_pending >>
          irule generated_plan_state_wf_marked_residual_nil >> simp[])
      >~ [`EVERY _ swap_ops`] >- gvs[EVERY_APPEND]
      >~ [`operand_val`]
      >- (rpt strip_tac >>
          rename1 `operand_val vsf lo wanted = operand_val vsf lo candidate` >>
          `MEM candidate ps.ps_stack \/ candidate IN FDOM ps.ps_spilled` by
            metis_tac[] >>
          `operand_val (frame_view fn ra vs) lo wanted =
           operand_val (frame_view fn ra vs) lo candidate` by metis_tac[] >>
          Cases_on `wanted` >> Cases_on `candidate` >>
          fs[Abbr`vsf`, operand_val_def])
      >> gvs[execute_plan_append, asm_block_at_append, EVERY_APPEND,
             Abbr`nr`]) >>
    strip_tac >> simp[Abbr`ns`] >> metis_tac[]) >>
  qunabbrev_tac `nr` >> qunabbrev_tac `ns` >>
  qabbrev_tac `n1 = LENGTH (execute_plan cplan.cp_initial_fmp
                              (rest_ops ++ swap_ops))` >>
  `asm_steps lo o2pc prog n1 st0 = AsmOK st1 /\ st1.as_pc = as.as_pc + n1` by (
    simp[Abbr`n1`, execute_plan_append] >> metis_tac[asm_steps_compose_ok]) >>
  (* PUSH target; JUMP. *)
  `execute_plan cplan.cp_initial_fmp [SOPushLabel target; SOEmit "JUMP"] =
   [AsmPushLabel target; AsmOp "JUMP"]` by
    simp[execute_plan_def, exec_stack_op_def] >>
  `st1.as_pc + 2 <= LENGTH prog /\
   EL st1.as_pc prog = AsmPushLabel target /\
   EL (st1.as_pc + 1) prog = AsmOp "JUMP"` by (
    qpat_x_assum `asm_block_at _ _ _` mp_tac >>
    simp[execute_plan_append, asm_block_at_append] >>
    simp[asm_block_at_def, Abbr`n1`, execute_plan_append] >> strip_tac >>
    qpat_x_assum `!j. j < 2 ==> _`
      (fn th => mp_tac (Q.SPEC `0` th) >> mp_tac (Q.SPEC `1` th)) >>
    simp[]) >>
  `asm_steps lo o2pc prog (SUC (SUC 0)) st1 =
   AsmOK (st1 with as_pc := pc_t)` by (
    drule_then assume_tac asm_step_pushlabel_ok >>
    rpt (qpat_x_assum `st1.as_pc = _` kall_tac) >>
    simp[asm_steps_def, asm_next_def] >>
    simp[asm_step_jump, asm_jump_def] >>
    simp[asmSemTheory.asm_state_component_equality]) >>
  `asm_steps lo o2pc prog (n1 + SUC (SUC 0)) st0 =
   AsmOK (st1 with as_pc := pc_t)` by
    metis_tac[asm_steps_compose_ok] >>
  qabbrev_tac `st3 = st1 with as_pc := pc_t` >>
  `st3.as_pc = pc_t /\ st3.as_stack = st1.as_stack /\
   st3.as_memory = st1.as_memory` by simp[Abbr`st3`] >>
  (* Below the frame. *)
  qunabbrev_tac `st0` >>
  `as with as_stack := top ++ rest = as` by
    simp[asmSemTheory.asm_state_component_equality] >>
  `asm_steps lo o2pc prog (n1 + SUC (SUC 0)) as =
   AsmOK (st3 with as_stack := st3.as_stack ++ rest)` by (
    pop_assum (SUBST1_TAC o GSYM) >> irule asm_steps_frame >> simp[]) >>
  (* The invariant again. *)
  `venom_asm_rel lo (release_dead_spills next_liveness ps2) vsf st3` by (
    simp[Abbr`st3`, venom_asm_rel_pc] >>
    irule venom_asm_rel_release_dead_spills >> simp[]) >>
  `memory_rel (release_dead_spills next_liveness ps2).ps_alloc
     as.as_memory st1.as_memory` by (
    qpat_x_assum `venom_asm_rel lo (release_dead_spills _ _) vsf st3` mp_tac >>
    simp[venom_asm_rel_def, Abbr`vsf`]) >>
  `!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
       read_byte b as.as_memory = read_byte b st1.as_memory` by
    metis_tac[memory_rel_outside_region] >>
  `context_venom_asm_rel cplan lo (release_dead_spills next_liveness ps2)
     (frame_view fn ra (jump_to target vs)) st3` by (
    irule venom_asm_rel_context >> conj_tac
    >- (simp[frame_view_def, jump_to_fields] >>
        simp[context_memory_rel_def] >> rpt strip_tac >>
        `read_byte i vs.vs_memory = read_byte i as.as_memory` by (
          qpat_x_assum `context_venom_asm_rel _ _ _ _ _` mp_tac >>
          simp[context_venom_asm_rel_def, context_memory_rel_def,
               frame_view_def]) >>
        `read_byte i as.as_memory = read_byte i st1.as_memory` by (
          first_x_assum irule >> metis_tac[context_spill_byte_of_region]) >>
        simp[])
    >> qexists `as.as_memory` >> simp[frame_view_jump_to] >>
       `jump_to target (frame_view fn ra vs) with vs_memory := as.as_memory =
        jump_to target vsf` by simp[Abbr`vsf`, jump_to_def] >>
       simp[venom_asm_rel_jump_to]) >>
  qexistsl_tac [`n1 + SUC (SUC 0)`, `st3 with as_stack := st3.as_stack ++ rest`] >>
  simp[fn_frame_inv_def, jump_to_fields] >> rpt conj_tac
  >- (`st3 with as_stack := st1.as_stack = st3 /\
       st3 with as_stack := st3.as_stack = st3` by
        simp[asmSemTheory.asm_state_component_equality] >>
      simp[] >> metis_tac[])
  >- (rpt strip_tac >>
      `read_byte b as.as_memory = read_byte b mem0` by metis_tac[] >>
      `read_byte b as.as_memory = read_byte b st1.as_memory` by (
        first_x_assum irule >> metis_tac[closure_spill_byte_own]) >>
      metis_tac[])
  >> qexists_tac `r` >> simp[]
QED
