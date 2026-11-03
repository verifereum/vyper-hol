(*
 * Per-instruction simulation against the frame invariant.
 *
 * genBlockSim's gen_inst_ok_sim relates one planner state to the whole
 * assembly stack with venom_asm_rel.  The frame-aware function simulation
 * (venomToAsmProps$gen_fn_frame_simulation) needs each instruction's
 * step to preserve frameRel$fn_frame_inv instead: the frame's own stack
 * above the caller's rest, return-PC variables read through the frame
 * view, the context-wide memory mask, and spill bytes outside the frame's
 * call-graph closure untouched.
 *
 * This theory holds the cases proved directly against the frame invariant.
 * The local step lemmas run on the frame's own stack (as with as_stack :=
 * top) against the frame view with the assembly memory as the Venom
 * memory, which makes codegenRel$memory_rel hold by reflexivity; asmFrame
 * extends the run below the frame, and the assembly memory footprint of
 * the run, read off memory_rel, re-establishes the context clauses.
 *
 * TOP-LEVEL:
 *   gen_jmp_frame_sim — JMP: join reorder, push label, jump
 *)

Theory genFrameSim
Ancestors
  frameRel asmFrame genBlockSim regularPostfixSim generatedReorderSim
  reorderSim mixedPrefixSim prefixSim stackOpAsmSim stackOpSim instSimHelpers
  blockSimHelpers planWf
  codegenRel contextCodegenRel planExec asmSem stackPlanGen stackPlanTypes
  stackPlanOps stackModel venomExecSemantics venomState venomInst
  allocMono contextCodegenRelProps asmIR venomEffects fcgDefs livenessDefs
  dfgDefs list rich_list

(* The stack and spill relations read the Venom state through vs_vars only. *)
Theorem plan_stack_rel_vars[local]:
  !lo v v' stk astk.
    v'.vs_vars = v.vs_vars ==>
    (plan_stack_rel lo v' stk astk <=> plan_stack_rel lo v stk astk)
Proof
  rpt strip_tac >>
  `!op. operand_val v' lo op = operand_val v lo op` by
    (Cases >> simp[operand_val_def]) >>
  simp[plan_stack_rel_def]
QED

Theorem plan_spill_rel_vars[local]:
  !lo v v' sp am.
    v'.vs_vars = v.vs_vars ==>
    (plan_spill_rel lo v' sp am <=> plan_spill_rel lo v sp am)
Proof
  rpt strip_tac >>
  `!op. operand_val v' lo op = operand_val v lo op` by
    (Cases >> simp[operand_val_def]) >>
  simp[plan_spill_rel_def]
QED

Theorem plan_rels_memory[local]:
  (plan_stack_rel lo (v with vs_memory := m) stk astk <=>
   plan_stack_rel lo v stk astk) /\
  (plan_spill_rel lo (v with vs_memory := m) sp am <=>
   plan_spill_rel lo v sp am)
Proof
  conj_tac >- (irule plan_stack_rel_vars >> simp[]) >>
  irule plan_spill_rel_vars >> simp[]
QED

Theorem plan_rels_jump_to[local]:
  (plan_stack_rel lo (jump_to l v) stk astk <=>
   plan_stack_rel lo v stk astk) /\
  (plan_spill_rel lo (jump_to l v) sp am <=>
   plan_spill_rel lo v sp am)
Proof
  conj_tac >- (irule plan_stack_rel_vars >> simp[jump_to_def]) >>
  irule plan_spill_rel_vars >> simp[jump_to_def]
QED

Theorem venom_asm_rel_jump_to[local]:
  !lo ps l v st.
    venom_asm_rel lo ps (jump_to l v) st <=> venom_asm_rel lo ps v st
Proof
  rpt gen_tac >> simp[venom_asm_rel_def, plan_rels_jump_to] >>
  simp[jump_to_def]
QED

Theorem venom_asm_rel_pc[local]:
  !lo ps v st pc.
    venom_asm_rel lo ps v (st with as_pc := pc) <=> venom_asm_rel lo ps v st
Proof
  simp[venom_asm_rel_def]
QED

Theorem jump_to_fields[local]:
  (jump_to l v).vs_halted = v.vs_halted /\
  (jump_to l v).vs_initial_fmp = v.vs_initial_fmp /\
  (jump_to l v).vs_memory = v.vs_memory
Proof
  simp[jump_to_def]
QED

Theorem frame_view_jump_to[local]:
  !fn ra l v. frame_view fn ra (jump_to l v) = jump_to l (frame_view fn ra v)
Proof
  simp[frame_view_def, jump_to_def]
QED

(* The context relation on a frame's own stack, read as the local relation
   with the assembly memory standing in for the Venom memory. *)
Theorem context_venom_asm_rel_local[local]:
  !cp lo ps v st.
    context_venom_asm_rel cp lo ps v st ==>
    venom_asm_rel lo ps (v with vs_memory := st.as_memory) st
Proof
  simp[context_venom_asm_rel_def, venom_asm_rel_def, plan_rels_memory,
       memory_rel_refl]
QED

Theorem venom_asm_rel_context[local]:
  !cp lo ps v st m.
    venom_asm_rel lo ps (v with vs_memory := m) st /\
    context_memory_rel cp v.vs_memory st.as_memory ==>
    context_venom_asm_rel cp lo ps v st
Proof
  simp[context_venom_asm_rel_def, venom_asm_rel_def, plan_rels_memory]
QED

(* A local run's memory footprint lies inside its allocator's interval;
   when that interval lies inside region r, bytes outside r are kept. *)
Theorem memory_rel_outside_region[local]:
  !alloc m m' r b.
    memory_rel alloc m m' /\
    r.sr_spill_base <= alloc.sa_spill_base /\
    alloc.sa_next_offset <= r.sr_spill_end /\
    ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
    read_byte b m = read_byte b m'
Proof
  rw[memory_rel_def] >> first_x_assum irule >> decide_tac
QED

Theorem closure_spill_byte_own[local]:
  !ctx cp fn r b.
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= b /\ b < r.sr_spill_end ==>
    closure_spill_byte ctx cp fn.fn_name b
Proof
  rw[closure_spill_byte_def, fcg_path_def] >>
  qexists `r` >> simp[relationTheory.RTC_REFL]
QED

(* ===== JMP ===== *)

(* JMP against the frame invariant.  Its plan is the join reorder to the
   target block's entry stack, then PUSH <target>; JUMP; the planner then
   releases dead spills.  The premises on target_stack are those the
   reorder simulation needs; the premises on r are the invariant's region
   clause for the output planner state, which the block induction gets
   from the planner's allocator monotonicity along the function's plan. *)
Theorem gen_jmp_frame_sim:
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
    generated_plan_state_wf base ps /\
    LENGTH target_stack <= 16 /\
    LENGTH target_stack <= LENGTH ps.ps_stack /\
    pending_inventory_wf target_stack ps /\
    reorder_steps_spill_ready cp.cp_initial_fmp dfg target_stack lo
      (MAPi (\i op. (i,op)) target_stack) ps /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      target_stack /\
    (!op at. operand_equiv dfg op at ==>
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
  rename1 `generated_plan_state_wf b0 ps` >>
  qpat_x_assum `lo = _` kall_tac >> qpat_x_assum `o2pc = _` kall_tac >>
  (* Venom: JMP is jump_to. *)
  `vs' = jump_to target vs` by (
    qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
    `inst.inst_opcode <> INVOKE` by simp[] >>
    simp[step_inst_non_invoke, step_inst_base_def]) >>
  pop_assum SUBST_ALL_TAC >>
  (* Planner: ops = join_ops ++ [PUSH target; JUMP], ps' releases spills. *)
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def, is_pre_codegen_opcode_def,
       is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def,
       is_raw_fmp_opcode_def, is_param_opcode_def] >>
  simp[generate_regular_inst_plan_def, compute_operands_def,
       get_non_label_operands_def, is_commutative_def,
       venom_to_evm_name_def, generate_emit_ops_def, stack_pop_def] >>
  pairarg_tac >> simp[] >>
  rename1 `reorder_plan _ _ _ = (join_ops, ps2)` >>
  strip_tac >>
  qpat_x_assum `_ = ops` (SUBST_ALL_TAC o GSYM) >>
  qpat_x_assum `_ = ps'` (SUBST_ALL_TAC o GSYM) >>
  (* The frame invariant, on the frame's own stack. *)
  qpat_x_assum `fn_frame_inv _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[fn_frame_inv_def] >> strip_tac >>
  qabbrev_tac `st0 = as with as_stack := top` >>
  qabbrev_tac `vsf = frame_view fn ra vs with vs_memory := as.as_memory` >>
  `venom_asm_rel lo ps vsf st0` by (
    drule context_venom_asm_rel_local >> simp[Abbr`vsf`, Abbr`st0`]) >>
  qabbrev_tac `n1 = LENGTH (execute_plan cplan.cp_initial_fmp join_ops)` >>
  (* Join reorder. *)
  `?st1. asm_steps lo o2pc prog n1 st0 = AsmOK st1 /\
         venom_asm_rel lo ps2 vsf st1 /\ st1.as_pc = as.as_pc + n1` by (
    qspecl_then [`dfg`, `target_stack`, `ps`, `join_ops`, `ps2`, `b0`,
                 `lo`, `o2pc`, `prog`, `vsf`, `st0`] mp_tac
      (Q.INST [`initial_fmp` |-> `cplan.cp_initial_fmp`]
         reorder_plan_venom_asm_rel_residual) >>
    impl_tac >- (
      simp[Abbr`st0`] >> rpt conj_tac
      >- (irule residual_budget_wf_canonical >>
          gvs[generated_plan_state_wf_def])
      >- (rpt strip_tac >> first_x_assum drule >>
          simp[Abbr`vsf`, operand_val_def] >>
          Cases_on `op1` >> Cases_on `at` >> simp[operand_val_def])
      >> gvs[execute_plan_append, asm_block_at_append]) >>
    strip_tac >> simp[Abbr`n1`] >> simp[Abbr`st0`] >> metis_tac[]) >>
  (* PUSH target; JUMP. *)
  `execute_plan cplan.cp_initial_fmp [SOPushLabel target; SOEmit "JUMP"] =
   [AsmPushLabel target; AsmOp "JUMP"]` by
    simp[execute_plan_def, exec_stack_op_def] >>
  `st1.as_pc + 2 <= LENGTH prog /\
   EL st1.as_pc prog = AsmPushLabel target /\
   EL (st1.as_pc + 1) prog = AsmOp "JUMP"` by (
    qpat_x_assum `asm_block_at _ _ _` mp_tac >>
    simp[execute_plan_append, asm_block_at_append] >>
    simp[asm_block_at_def, Abbr`n1`] >> strip_tac >>
    qpat_x_assum `!j. j < 2 ==> _`
      (fn th => mp_tac (Q.SPEC `0` th) >> mp_tac (Q.SPEC `1` th)) >>
    simp[]) >>
  `asm_steps lo o2pc prog (SUC (SUC 0)) st1 =
   AsmOK (st1 with as_pc := pc_t)` by (
    drule_then assume_tac asm_step_pushlabel_ok >>
    qpat_x_assum `st1.as_pc = _` kall_tac >>
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
