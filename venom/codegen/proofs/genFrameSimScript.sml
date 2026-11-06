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
 *   gen_jnz_frame_sim — JNZ: condition to the top, JUMPI, JUMP
 *   gen_inst_frame_sim — any other non-terminator, non-INVOKE, non-GAS step
 *)

Theory genFrameSim
Ancestors
  frameRel asmFrame genBlockSim spillPlanSim regularPostfixSim generatedReorderSim
  reorderSim mixedPrefixSim prefixSim stackOpAsmSim stackOpSim instSimHelpers
  blockSimHelpers planWf frameViewStep frameViewFacts
  codegenRel contextCodegenRel planExec asmSem stackPlanGen stackPlanTypes
  stackPlanOps stackModel venomExecSemantics venomState venomInst
  allocMono contextCodegenRelProps asmIR venomEffects fcgDefs livenessDefs
  dfgDefs list rich_list deepDupCallerSim

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
      >- (rpt strip_tac >>
          rename1 `operand_val vsf lo wanted = operand_val vsf lo candidate` >>
          `operand_val (frame_view fn ra vs) lo wanted =
           operand_val (frame_view fn ra vs) lo candidate` by metis_tac[] >>
          Cases_on `wanted` >> Cases_on `candidate` >>
          fs[Abbr`vsf`, operand_val_def])
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

Theorem jnz_plan_decompose[local]:
  inst.inst_opcode = JNZ /\
  inst.inst_operands = [cond; Label nz; Label z] /\
  ~is_label_operand cond /\ inst.inst_outputs = [] /\
  generate_inst_plan lv dfg cfg fn inst nl halt term bb ps = SOME (ops, ps') ==>
  ?iops ps1 rops ps2.
    emit_input_plan JNZ [cond] nl ps = (iops, ps1) /\
    reorder_plan dfg [cond] ps1 = (rops, ps2) /\
    ops = iops ++ rops ++
      [SOPushLabel nz; SOEmit "JUMPI"; SOPushLabel z; SOEmit "JUMP"] /\
    ps' = release_dead_spills nl
      (ps2 with ps_stack := stack_pop 1 ps2.ps_stack)
Proof
  strip_tac >>
  `is_label_operand (Label nz) /\ is_label_operand (Label z) /\
   (case cond of Lit v => T | Var v => T | Label l => F)` by
    (Cases_on `cond` >> gvs[is_label_operand_def]) >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def, is_pre_codegen_opcode_def,
       is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def,
       is_raw_fmp_opcode_def, is_param_opcode_def] >>
  simp[generate_regular_inst_plan_def, compute_operands_def,
       get_non_label_operands_def, is_commutative_def,
       venom_to_evm_name_def, generate_emit_ops_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  metis_tac[]
QED

Theorem jnz_input_depth[local]:
  ~is_label_operand op /\
  (is_var_operand op ==>
    (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  emit_input_plan JNZ [op] nl ps = (ops, target) ==>
  ?d. stack_get_depth op target.ps_stack = SOME d /\ d <= 16
Proof
  simp[emit_input_plan_one] >> strip_tac >>
  Cases_on `is_var_operand op /\ IS_SOME (FLOOKUP ps.ps_spilled op)`
  >- (fs[] >> drule_all emit_one_input_restored_depth_zero >> simp[]) >>
  Cases_on `op` >> gvs[is_label_operand_def, is_var_operand_def]
  >- (gvs[emit_one_input_def, is_var_operand_def] >>
      qexists `0` >>
      simp[stack_get_depth_def, stack_push_def, REVERSE_SNOC, stack_find_def]) >>
  rename1 `stack_get_depth (Var v) ps.ps_stack = SOME d` >>
  gvs[emit_one_input_def, is_var_operand_def] >>
  Cases_on `MEM v nl` >> gvs[do_dup_def]
  >- (drule stack_get_depth_props >> strip_tac >>
      qexists `0` >>
      gvs[stack_dup_def] >>
      simp[stack_get_depth_def, stack_push_def, REVERSE_SNOC, stack_find_def]) >>
  qexists `d` >> simp[]
QED

Theorem jnz_prefix_wf[local]:
  emit_input_plan JNZ [op] nl ps = (iops, ps1) /\
  reorder_plan dfg [op] ps1 = (rops, ps2) /\
  1 <= LENGTH ps1.ps_stack /\
  (!l. op = Label l ==> IS_SOME (FLOOKUP lo l)) ==>
  prefix_wf lo (LENGTH ps.ps_stack) (iops ++ rops)
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`JNZ`, `nl`, `op`, `ps`, `lo`]
    emit_one_input_wf_len) >>
  mp_tac (Q.SPECL [`dfg`, `[op]`, `ps1`, `lo`]
    reorder_plan_wf_len) >>
  simp[GSYM emit_input_plan_one] >> rpt strip_tac >>
  irule prefix_wf_append >> simp[]
QED

Theorem jnz_input_alloc[local]:
  ~is_label_operand op /\
  (is_var_operand op ==>
    (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  emit_input_plan JNZ [op] nl ps = (ops, target) ==>
  target.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base /\
  target.ps_alloc.sa_next_offset = ps.ps_alloc.sa_next_offset /\
  (apply_prefix_ops f lo ops ps).ps_alloc = ps.ps_alloc
Proof
  simp[emit_input_plan_one] >> strip_tac >>
  Cases_on `op` >> gvs[is_label_operand_def, is_var_operand_def]
  >- gvs[emit_one_input_def, is_var_operand_def, apply_prefix_ops_def,
         apply_prefix_op_def, strongPrefixSimTheory.apply_simple_op_def] >>
  rename1 `Var v` >>
  Cases_on `FLOOKUP ps.ps_spilled (Var v)` >>
  gvs[emit_one_input_def, is_var_operand_def]
  >- (Cases_on `MEM v nl` >> gvs[do_dup_def, apply_prefix_ops_def,
       apply_prefix_op_def, strongPrefixSimTheory.apply_simple_op_def]) >>
  gvs[do_restore_def] >>
  `!stk. stack_get_depth (Var v) (stack_push (Var v) stk) = SOME 0` by
    simp[stack_get_depth_def, stack_push_def, REVERSE_SNOC, stack_find_def] >>
  Cases_on `MEM v nl` >>
  gvs[do_dup_def, apply_prefix_ops_def, apply_prefix_op_def,
      strongPrefixSimTheory.apply_simple_op_def, free_spill_slot_def]
QED

Theorem jnz_reorder_align[local]:
  reorder_plan dfg [op] ps = (ops, target) /\
  (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 16) /\
  op <> dead_stack_marker /\
  (!at. operand_equiv dfg op at ==> at <> dead_stack_marker) /\
  (!at. (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
    operand_equiv dfg op at ==>
    operand_val v lo op = operand_val v lo at) ==>
  plan_stack_sem_eq lo v (apply_prefix_ops f lo ops ps).ps_stack
    target.ps_stack /\
  (apply_prefix_ops f lo ops ps).ps_spilled =
    target.ps_spilled /\
  (apply_prefix_ops f lo ops ps).ps_alloc.sa_spill_base =
    target.ps_alloc.sa_spill_base /\
  (apply_prefix_ops f lo ops ps).ps_alloc.sa_next_offset =
    target.ps_alloc.sa_next_offset
Proof
  strip_tac >>
  `1 <= LENGTH ps.ps_stack` by
    (drule stack_get_depth_bound >> simp[]) >>
  qpat_x_assum `reorder_plan _ _ _ = _` mp_tac >>
  simp[reorder_plan_def, indexedListsTheory.MAPi_def,
       indexedListsTheory.MAPi_ACC_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  mp_tac (Q.SPECL [`dfg`, `[op]`, `0`, `op`, `ps`, `ops`, `ps'`,
                    `lo`, `v`, `d`]
    (Q.INST [`initial_fmp` |-> `f`] reorder_one_shallow_sem_align)) >>
  simp[stack_get_unfixed_depth_empty_window] >> metis_tac[]
QED

Theorem jnz_input_align[local]:
  ~is_label_operand op /\
  (is_var_operand op ==>
    (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  emit_input_plan JNZ [op] nl ps = (ops, target) /\
  doSwapSim$spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  prefix_spill_wf f lo ops ps ==>
  (apply_prefix_ops f lo ops ps).ps_stack = target.ps_stack /\
  (apply_prefix_ops f lo ops ps).ps_spilled =
    target.ps_spilled /\
  (apply_prefix_ops f lo ops ps).ps_alloc.sa_spill_base =
    target.ps_alloc.sa_spill_base /\
  (apply_prefix_ops f lo ops ps).ps_alloc.sa_next_offset =
    target.ps_alloc.sa_next_offset
Proof
  strip_tac >>
  drule_all jnz_input_alloc >> strip_tac >>
  `!s d. op = Var s /\ MEM s nl /\
       ~IS_SOME (FLOOKUP ps.ps_spilled (Var s)) /\
       stack_get_depth (Var s) ps.ps_stack = SOME d ==> d <= 15` by
    (rpt strip_tac >> gvs[is_var_operand_def] >> metis_tac[]) >>
  `(apply_prefix_ops f lo ops ps).ps_stack = target.ps_stack /\
   (apply_prefix_ops f lo ops ps).ps_spilled = target.ps_spilled` by
    (irule (Q.INST [`initial_fmp` |-> `f`]
       emit_one_input_ss_align_from_spill_wf) >>
     conj_tac
     >- gvs[doSwapSimTheory.spill_alloc_layout_wf_def] >>
     conj_tac >- (qexistsl_tac [`nl`, `op`, `JNZ`] >>
       simp[GSYM emit_input_plan_one]) >> simp[]) >>
  simp[]
QED

Theorem jnz_prefix_transport[local]:
  ~is_label_operand op /\
  (is_var_operand op ==>
    (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  emit_input_plan JNZ [op] nl ps = (iops, ps1) /\
  reorder_plan dfg [op] ps1 = (rops, ps2) /\
  doSwapSim$spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  prefix_spill_wf f lo iops ps /\
  op <> dead_stack_marker /\
  (!at. operand_equiv dfg op at ==> at <> dead_stack_marker) /\
  (!at. (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
    operand_equiv dfg op at ==>
    operand_val v lo op = operand_val v lo at) /\
  venom_asm_rel lo (apply_prefix_ops f lo (iops ++ rops) ps) v st ==>
  venom_asm_rel lo ps2 v st /\
  plan_stack_rel lo v (apply_prefix_ops f lo rops ps1).ps_stack st.as_stack
Proof
  strip_tac >>
  drule_all jnz_input_align >> simp[] >> strip_tac >>
  drule_all jnz_input_depth >> strip_tac >>
  `!at. (MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled) /\
    operand_equiv dfg op at ==>
    operand_val v lo op = operand_val v lo at` by
    (drule_at (Pat `emit_input_plan _ _ _ _ = _`)
       emit_input_plan_inventory_subset >> simp[] >> metis_tac[]) >>
  drule jnz_reorder_align >>
  disch_then (qspecl_then [`v`, `lo`, `f`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  simp[] >> strip_tac >>
  qspecl_then [`rops`, `lo`, `apply_prefix_ops f lo iops ps`, `ps1`] mp_tac
    (Q.INST [`initial_fmp` |-> `f`] apply_prefix_ops_ext_relevant) >>
  (impl_tac >- simp[]) >> simp[LET_THM] >> strip_tac >>
  gvs[planAlignTheory.apply_prefix_ops_append] >>
  conj_tac
  >- (irule venom_asm_rel_sem_stack_transport >>
      qexists `apply_prefix_ops f lo rops (apply_prefix_ops f lo iops ps)` >>
      simp[]) >>
  fs[venom_asm_rel_def]
QED

Theorem jnz_consume_rel[local]:
  venom_asm_rel lo ps v st /\ st.as_stack = w::tail ==>
  venom_asm_rel lo
    (release_dead_spills nl (ps with ps_stack := stack_pop 1 ps.ps_stack))
    v (st with as_stack := tail)
Proof
  strip_tac >> irule venom_asm_rel_release_dead_spills >>
  fs[venom_asm_rel_def] >>
  `LENGTH ps.ps_stack = LENGTH (w::tail)` by
    metis_tac[plan_stack_rel_length] >>
  simp[] >>
  drule plan_stack_rel_pop >>
  disch_then (qspec_then `1` mp_tac) >>
  simp[stack_pop_def]
QED

Theorem jnz_reorder_end_len[local]:
  reorder_plan dfg [op] ps = (ops, target) /\
  stack_get_depth op ps.ps_stack = SOME d /\ d <= 16 ==>
  prefix_end_len lo (LENGTH ps.ps_stack) ops = LENGTH ps.ps_stack
Proof
  strip_tac >>
  drule stack_get_depth_bound >> strip_tac >>
  qpat_x_assum `reorder_plan _ _ _ = _` mp_tac >>
  simp[reorder_plan_def, indexedListsTheory.MAPi_def,
       indexedListsTheory.MAPi_ACC_def] >>
  simp[reorder_one_def, stack_get_unfixed_depth_empty_window] >>
  Cases_on `d = 0`
  >- (simp[] >> strip_tac >> gvs[]) >> simp[] >>
  `0 < LENGTH ps.ps_stack /\ ~(16 < d)` by decide_tac >> simp[] >>
  Cases_on `operand_equiv dfg op (stack_peek 0 ps.ps_stack)` >>
  simp[do_swap_def] >> strip_tac >> gvs[]
QED

Theorem jnz_prepare[local]:
  ~is_label_operand op /\
  (is_var_operand op ==>
    (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  emit_input_plan JNZ [op] nl ps = (iops, ps1) /\
  reorder_plan dfg [op] ps1 = (rops, ps2) /\
  1 <= LENGTH ps1.ps_stack /\
  (!l. op = Label l ==> IS_SOME (FLOOKUP lo l)) /\
  doSwapSim$spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  eops <> [] /\
  prefix_spill_wf f lo (FRONT ((iops ++ rops) ++ eops)) ps /\
  op <> dead_stack_marker /\
  (!at. operand_equiv dfg op at ==> at <> dead_stack_marker) /\
  (!at. (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
    operand_equiv dfg op at ==>
    operand_val v lo op = operand_val v lo at) /\
  venom_asm_rel lo ps v st /\
  asm_block_at prog st.as_pc (execute_plan f ((iops ++ rops) ++ eops)) ==>
  ?mid w tail.
    asm_steps lo o2pc prog (LENGTH (execute_plan f (iops ++ rops))) st = AsmOK mid /\
    mid.as_stack = w::tail /\ operand_val v lo op = SOME w /\
    asm_block_at prog mid.as_pc (execute_plan f eops) /\
    venom_asm_rel lo
      (release_dead_spills nl (ps2 with ps_stack := stack_pop 1 ps2.ps_stack))
      v (mid with as_stack := tail)
Proof
  strip_tac >>
  `prefix_wf lo (LENGTH ps.ps_stack) (iops ++ rops)` by
    (irule jnz_prefix_wf >> metis_tac[]) >>
  `EVERY is_prefix_op (iops ++ rops)` by
    metis_tac[prefix_wf_every_prefix_op] >>
  `prefix_spill_wf f lo (iops ++ rops) ps` by
    (irule (Q.INST [`initial_fmp` |-> `f`] prefix_spill_wf_front_prefix) >>
     metis_tac[]) >>
  `prefix_spill_wf f lo iops ps` by
    (drule prefix_spill_wf_prefix >> simp[]) >>
  drule_all (Q.INST [`initial_fmp` |-> `f`] genBlockSimTheory.prefix_sim) >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rename1 `asm_steps _ _ _ _ st = AsmOK mid` >>
  drule_all jnz_prefix_transport >> strip_tac >>
  drule_all jnz_input_depth >> strip_tac >>
  `prefix_end_len (lo : string |-> num) (LENGTH ps1.ps_stack) rops = LENGTH ps1.ps_stack` by
    (irule jnz_reorder_end_len >> metis_tac[]) >>
  `prefix_end_len (lo : string |-> num) (LENGTH ps.ps_stack) iops = LENGTH ps1.ps_stack` by
    (mp_tac (Q.SPECL [`JNZ`, `nl`, `op`, `ps`, `lo`]
      (INST_TYPE [alpha |-> ``:num``] emit_one_input_wf_len)) >>
     simp[GSYM emit_input_plan_one]) >>
  `mid.as_stack <> []` by
    (gvs[planWfTheory.prefix_end_len_append] >> strip_tac >> gvs[]) >>
  `!at. (MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled) /\
    operand_equiv dfg op at ==>
    operand_val v lo op = operand_val v lo at` by
    (drule_at (Pat `emit_input_plan _ _ _ _ = _`)
       emit_input_plan_inventory_subset >> simp[] >> metis_tac[]) >>
  `operand_val v lo op = SOME (HD mid.as_stack)` by
    (irule (Q.INST [`initial_fmp` |-> `f`] reorder_single_op_val_on_tos) >>
     metis_tac[]) >>
  Cases_on `mid.as_stack` >> gvs[] >>
  irule jnz_consume_rel >> simp[]
QED

Theorem jnz_suffix[local]:
  asm_block_at prog st.as_pc
    [AsmPushLabel nz; AsmOp "JUMPI"; AsmPushLabel z; AsmOp "JUMP"] /\
  st.as_stack = w::tail /\
  FLOOKUP lo nz = SOME off_nz /\ off_nz < dimword (:256) /\
  FLOOKUP o2pc off_nz = SOME pc_nz /\
  FLOOKUP lo z = SOME off_z /\ off_z < dimword (:256) /\
  FLOOKUP o2pc off_z = SOME pc_z ==>
  asm_steps lo o2pc prog
    (if w = 0w then SUC (SUC (SUC (SUC 0))) else SUC (SUC 0)) st =
    AsmOK (st with <|as_stack := tail;
                    as_pc := if w = 0w then pc_z else pc_nz|>)
Proof
  strip_tac >>
  `st.as_pc + 4 <= LENGTH prog /\
   EL st.as_pc prog = AsmPushLabel nz /\
   EL (st.as_pc + 1) prog = AsmOp "JUMPI" /\
   EL (st.as_pc + 2) prog = AsmPushLabel z /\
   EL (st.as_pc + 3) prog = AsmOp "JUMP"` by
    (qpat_x_assum `asm_block_at _ _ _` mp_tac >>
     simp[asm_block_at_def] >> strip_tac >>
     qpat_x_assum `!j. j < 4 ==> _`
       (fn th => map_every (fn n => mp_tac (Q.SPEC n th))
          [`0`, `1`, `2`, `3`]) >> simp[]) >>
  imp_res_tac asm_step_pushlabel_ok >>
  Cases_on `w = 0w` >>
  asm_rewrite_tac [numLib.num_CONV ``4:num``, numLib.num_CONV ``3:num``,
    numLib.num_CONV ``2:num``, numLib.num_CONV ``1:num``, asm_steps_def] >>
  simp[asm_step_pushlabel_ok, asm_next_def,
       asm_step_jumpi, asm_jumpi_def, asm_step_jump, asm_jump_def,
       asmSemTheory.asm_state_component_equality]
QED

Theorem frame_jump_context[local]:
  !cp lo ps fn ra vs st ps' out r label.
  context_venom_asm_rel cp lo ps (frame_view fn ra vs) st /\
  venom_asm_rel lo ps' (frame_view fn ra vs with vs_memory := st.as_memory) out /\
  MEM r cp.cp_regions /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
  context_venom_asm_rel cp lo ps' (frame_view fn ra (jump_to label vs)) out
Proof
  rpt gen_tac >> strip_tac >>
  `memory_rel ps'.ps_alloc st.as_memory out.as_memory` by
    fs[venom_asm_rel_def] >>
  irule venom_asm_rel_context >> conj_tac
  >- (simp[frame_view_def, jump_to_fields, context_memory_rel_def] >>
      rpt strip_tac >>
      `read_byte i vs.vs_memory = read_byte i st.as_memory` by
        fs[context_venom_asm_rel_def, context_memory_rel_def, frame_view_def] >>
      `read_byte i st.as_memory = read_byte i out.as_memory` by
        (irule memory_rel_outside_region >>
         qexistsl_tac [`ps'.ps_alloc`, `r`] >>
         simp[] >> metis_tac[context_spill_byte_of_region]) >> simp[]) >>
  qexists `st.as_memory` >> simp[frame_view_jump_to] >>
  `jump_to label (frame_view fn ra vs) with vs_memory := st.as_memory =
   jump_to label (frame_view fn ra vs with vs_memory := st.as_memory)` by
    simp[jump_to_def] >>
  simp[venom_asm_rel_jump_to]
QED

Theorem frame_jump_lift[local]:
  !ctx cp lo fn ra rest mem0 ps vs ast top ps' out r label n o2pc prog.
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs ast /\
  ast.as_stack = top ++ rest /\
  context_venom_asm_rel cp lo ps (frame_view fn ra vs)
    (ast with as_stack := top) /\
  venom_asm_rel lo ps' (frame_view fn ra vs with vs_memory := ast.as_memory) out /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  asm_steps lo o2pc prog n (ast with as_stack := top) = AsmOK out ==>
  asm_steps lo o2pc prog n ast =
    AsmOK (out with as_stack := out.as_stack ++ rest) /\
  fn_frame_inv ctx cp lo fn ra rest mem0 ps' (jump_to label vs)
    (out with as_stack := out.as_stack ++ rest)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `MEM r cplan.cp_regions` >>
  `memory_rel ps'.ps_alloc ast.as_memory out.as_memory` by
    fs[venom_asm_rel_def] >>
  `!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
       read_byte b ast.as_memory = read_byte b out.as_memory` by
    metis_tac[memory_rel_outside_region] >>
  `context_venom_asm_rel cplan lo ps' (frame_view fn ra (jump_to label vs)) out` by
    (irule frame_jump_context >> conj_tac
     >- (qexists `r` >> simp[]) >>
     qexistsl_tac [`ps`, `ast with as_stack := top`] >> simp[]) >>
  conj_tac
  >- (`ast with as_stack := top ++ rest = ast` by
        simp[asmSemTheory.asm_state_component_equality] >>
      pop_assum (SUBST1_TAC o GSYM) >> irule asm_steps_frame >> simp[]) >>
  fs[fn_frame_inv_def] >> simp[fn_frame_inv_def, jump_to_fields] >>
  conj_tac
  >- (rpt strip_tac >>
      `read_byte b ast.as_memory = read_byte b mem0` by metis_tac[] >>
      `read_byte b ast.as_memory = read_byte b out.as_memory` by
        (first_x_assum irule >> metis_tac[closure_spill_byte_own]) >>
      metis_tac[]) >>
  qexists `r` >> simp[]
QED

(* ===== JNZ ===== *)

(* JNZ against the frame invariant.  Its plan brings the condition to the
   top of the stack (emit_input_plan, reorder_plan), then
   PUSH if_nz; JUMPI; PUSH if_z; JUMP; the planner pops the condition and
   releases dead spills.  The condition premises are gen_inst_ok_sim's,
   read through the frame view on the assembly side: the Venom step reads
   the condition from vs, the code from the frame view.  The premises on
   r are the invariant's region clause for the output planner state, as in
   gen_jmp_frame_sim. *)
Theorem gen_jnz_frame_sim:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   cond_op if_nz if_z off_nz off_z pc_nz pc_z.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = JNZ /\
    inst.inst_operands = [cond_op; Label if_nz; Label if_z] /\
    (* The planner drops label operands of jumps, so a label condition would
       emit nothing; label_positions_ok excludes it. *)
    ~is_label_operand cond_op /\
    inst.inst_outputs = [] /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf base ps /\
    1 <= LENGTH (SND (emit_input_plan JNZ [cond_op] next_liveness ps)).ps_stack /\
    (is_var_operand cond_op ==>
      (?d. stack_get_depth cond_op ps.ps_stack = SOME d /\ d <= 15) \/
      IS_SOME (FLOOKUP ps.ps_spilled cond_op)) /\
    eval_operand cond_op vs = operand_val (frame_view fn ra vs) lo cond_op /\
    (!at. (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
       operand_equiv dfg cond_op at ==>
       operand_val (frame_view fn ra vs) lo cond_op =
       operand_val (frame_view fn ra vs) lo at) /\
    cond_op <> dead_stack_marker /\
    (!at. operand_equiv dfg cond_op at ==> at <> dead_stack_marker) /\
    prefix_spill_wf cp.cp_initial_fmp lo (FRONT ops) ps /\
    FLOOKUP lo if_nz = SOME off_nz /\ off_nz < dimword (:256) /\
    FLOOKUP o2pc off_nz = SOME pc_nz /\
    FLOOKUP lo if_z = SOME off_z /\ off_z < dimword (:256) /\
    FLOOKUP o2pc off_z = SOME pc_z /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst next_liveness is_halting
      next_is_term bb_label ps = SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        fn_frame_inv ctx cp lo fn ra rest mem0 ps' vs' as' /\
        ((vs' = jump_to if_nz vs /\ as'.as_pc = pc_nz) \/
         (vs' = jump_to if_z vs /\ as'.as_pc = pc_z))
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `MEM r cplan.cp_regions` >>
  `!l. cond_op <> Label l` by
    (rpt strip_tac >> qpat_x_assum `~is_label_operand _` mp_tac >>
     asm_rewrite_tac[is_label_operand_def]) >>
  drule_all jnz_plan_decompose >> strip_tac >>
  `?top. as.as_stack = top ++ rest /\
    context_venom_asm_rel cplan lo ps (frame_view fn ra vs)
      (as with as_stack := top)` by
    (fs[fn_frame_inv_def] >> metis_tac[]) >>
  qabbrev_tac `v = frame_view fn ra vs with vs_memory := as.as_memory` >>
  `venom_asm_rel lo ps v (as with as_stack := top)` by
    (drule context_venom_asm_rel_local >> simp[Abbr `v`]) >>
  `!op. operand_val v lo op = operand_val (frame_view fn ra vs) lo op` by
    (Cases >> simp[Abbr `v`, operand_val_def]) >>
  `doSwapSim$spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    fs[generated_plan_state_wf_def] >>
  `?mid w tail.
    asm_steps lo o2pc prog (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)))
      (as with as_stack := top) = AsmOK mid /\
    mid.as_stack = w::tail /\ operand_val v lo cond_op = SOME w /\
    asm_block_at prog mid.as_pc
      [AsmPushLabel if_nz; AsmOp "JUMPI"; AsmPushLabel if_z; AsmOp "JUMP"] /\
    venom_asm_rel lo ps' v (mid with as_stack := tail)` by
    (`1 <= LENGTH ps1.ps_stack` by fs[] >>
     `!at. (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
       operand_equiv dfg cond_op at ==>
       operand_val v lo cond_op = operand_val v lo at` by metis_tac[] >>
     mp_tac (Q.INST
       [`f` |-> `cplan.cp_initial_fmp`,
        `eops` |-> `[SOPushLabel if_nz; SOEmit "JUMPI"; SOPushLabel if_z; SOEmit "JUMP"]`,
        `op` |-> `cond_op`, `nl` |-> `next_liveness`,
        `st` |-> `as with as_stack := top`] jnz_prepare) >>
     (impl_tac >- (simp[APPEND_ASSOC] >> metis_tac[])) >>
     simp[execute_plan_def, exec_stack_op_def] >> metis_tac[]) >>
  drule_all jnz_suffix >> strip_tac >>
  qabbrev_tac `dest = if w = 0w then pc_z else pc_nz` >>
  qabbrev_tac `label = if w = 0w then if_z else if_nz` >>
  qabbrev_tac `out = mid with <|as_stack := tail; as_pc := dest|>` >>
  `venom_asm_rel lo ps' v out` by
    (qunabbrev_tac `out` >>
     `mid with <|as_stack := tail; as_pc := dest|> =
      (mid with as_stack := tail) with as_pc := dest` by
        simp[asmSemTheory.asm_state_component_equality] >>
     pop_assum SUBST1_TAC >> pure_rewrite_tac[venom_asm_rel_pc] >>
     first_assum ACCEPT_TAC) >>
  `asm_steps lo o2pc prog
    (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) +
     (if w = 0w then SUC (SUC (SUC (SUC 0))) else SUC (SUC 0)))
    (as with as_stack := top) = AsmOK out` by
    (irule asm_steps_compose_ok >> qexists `mid` >> simp[Abbr `out`, Abbr `dest`]) >>
  `?n. asm_steps lo o2pc prog n as =
       AsmOK (out with as_stack := out.as_stack ++ rest) /\
     fn_frame_inv ctx cplan lo fn ra rest mem0 ps' (jump_to label vs)
       (out with as_stack := out.as_stack ++ rest)` by
    (qunabbrev_tac `v` >> drule_all frame_jump_lift >> metis_tac[]) >>
  `eval_operand cond_op vs = SOME w` by metis_tac[] >>
  gen_tac >> strip_tac >>
  `vs' = jump_to label vs` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_def] >>
     Cases_on `w = 0w` >> simp[Abbr `label`] >> metis_tac[]) >>
  qexistsl_tac [`n`, `out with as_stack := out.as_stack ++ rest`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[] >>
  Cases_on `w = 0w` >>
  fs[Abbr `out`, Abbr `dest`, Abbr `label`]
QED

(* ===== Non-jump instructions ===== *)

Theorem operand_val_memory_update[local]:
  operand_val (s with vs_memory := m) lo op = operand_val s lo op
Proof
  Cases_on `op` >> simp[operand_val_def]
QED

Theorem source_write_ranges_frame_view[local]:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  ~is_terminator inst.inst_opcode ==>
  source_memory_write_ranges inst (frame_view fn ra s with vs_memory := m) =
  source_memory_write_ranges inst s
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, source_memory_write_ranges_def] >>
  `!op. MEM op inst.inst_operands ==>
    eval_operand op (frame_view fn ra s with vs_memory := m) = eval_operand op s`
    by (rpt strip_tac >> irule eval_operand_frame_view >> gen_tac >> disch_tac >>
        irule ordinary_operand_not_retpc >> simp[] >>
        qexists_tac `inst` >> gvs[]) >>
  Cases_on `inst.inst_operands` >>
  gvs[fixed_source_write_range_def, sized_source_write_range_def] >>
  rename1 `inst.inst_operands = _ :: tail` >> Cases_on `tail` >> gvs[] >>
  rename1 `inst.inst_operands = _ :: _ :: tail` >> Cases_on `tail` >> gvs[] >>
  rename1 `inst.inst_operands = _ :: _ :: _ :: tail` >> Cases_on `tail` >> gvs[] >>
  rename1 `inst.inst_operands = _ :: _ :: _ :: _ :: tail` >> Cases_on `tail` >> gvs[] >>
  rename1 `inst.inst_operands = _ :: _ :: _ :: _ :: _ :: tail` >> Cases_on `tail` >> gvs[] >>
  rename1 `inst.inst_operands = _ :: _ :: _ :: _ :: _ :: _ :: tail` >> Cases_on `tail` >> gvs[] >>
  rename1 `inst.inst_operands = _ :: _ :: _ :: _ :: _ :: _ :: _ :: tail` >> Cases_on `tail` >> gvs[]
QED

Theorem source_read_ranges_frame_view[local]:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  ~is_terminator inst.inst_opcode ==>
  source_memory_read_ranges inst (frame_view fn ra s with vs_memory := m) =
  source_memory_read_ranges inst s
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode` >>
  fs[is_terminator_def] >> simp[source_memory_read_ranges_def] >>
  `!op. MEM op inst.inst_operands ==>
    eval_operand op (frame_view fn ra s with vs_memory := m) = eval_operand op s`
    by (rpt strip_tac >> irule eval_operand_frame_view >> gen_tac >> disch_tac >>
        irule ordinary_operand_not_retpc >> simp[] >>
        qexists_tac `inst` >> gvs[]) >>
  Cases_on `inst.inst_operands` >> gvs[memory_range_of_operands_def]
  >~ [`inst.inst_opcode = LOG`] >- (rename1 `inst.inst_operands = topic_count :: args` >>
     Cases_on `topic_count` >> gvs[] >>
     IF_CASES_TAC >> simp[] >>
     `!op. MEM op (REVERSE args) ==>
       eval_operand op (frame_view fn ra s with vs_memory := m) = eval_operand op s`
       by simp[] >>
     `eval_operands (DROP 2 (REVERSE args))
        (frame_view fn ra s with vs_memory := m) =
      eval_operands (DROP 2 (REVERSE args)) s` by
       (irule eval_operands_frame_view >> rpt gen_tac >> disch_tac >>
        irule ordinary_operand_not_retpc >> simp[] >>
        qexists_tac `inst` >> simp[] >> drule MEM_DROP_IMP >> simp[]) >>
     `MEM (EL 0 (REVERSE args)) (REVERSE args)` by
       (irule EL_MEM >> simp[] >> decide_tac) >>
     `MEM (EL 1 (REVERSE args)) (REVERSE args)` by
       (irule EL_MEM >> simp[] >> decide_tac) >>
     gvs[EL, memory_range_of_operands_def]) >>
  rename1 `inst.inst_operands = _ :: tail` >> Cases_on `tail` >> gvs[] >>
  rename1 `inst.inst_operands = _ :: _ :: tail` >> Cases_on `tail` >> gvs[] >>
  rename1 `inst.inst_operands = _ :: _ :: _ :: tail` >> Cases_on `tail` >> gvs[] >>
  rename1 `inst.inst_operands = _ :: _ :: _ :: _ :: tail` >> Cases_on `tail` >> gvs[] >>
  rename1 `inst.inst_operands = _ :: _ :: _ :: _ :: _ :: tail` >> Cases_on `tail` >> gvs[] >>
  rename1 `inst.inst_operands = _ :: _ :: _ :: _ :: _ :: _ :: tail` >> Cases_on `tail` >> gvs[] >>
  rename1 `inst.inst_operands = _ :: _ :: _ :: _ :: _ :: _ :: _ :: tail` >> Cases_on `tail` >> gvs[]
QED

Theorem context_reads_agree[local]:
  !cp inst vs m. source_memory_reads_disjoint cp inst vs /\
  context_memory_rel cp vs.vs_memory m ==>
  !i. source_memory_read_byte inst vs i ==>
      read_byte i m = read_byte i vs.vs_memory
Proof
  rpt gen_tac >> simp[source_memory_reads_disjoint_def, context_memory_rel_def,
       source_memory_read_byte_def, EVERY_MEM] >>
  rpt strip_tac >> first_x_assum (irule o GSYM) >>
  simp[context_spill_byte_def] >> gen_tac >> CCONTR_TAC >> gvs[] >>
  rename1 `MEM rng (source_memory_read_ranges inst vs)` >>
  PairCases_on `rng` >> gvs[byte_in_memory_range_def] >>
  qpat_x_assum `!e. MEM e _ ==> _` drule >> simp[] >>
  qexists_tac `r` >> simp[] >> decide_tac
QED

Theorem context_reads_local[local]:
  !cp inst vs r alloc. source_memory_reads_disjoint cp inst vs /\ MEM r cp.cp_regions /\
  r.sr_spill_base <= alloc.sa_spill_base /\
  alloc.sa_next_offset <= r.sr_spill_end ==>
  EVERY (\(off,len). len = 0 \/ off + len <= alloc.sa_spill_base \/
                       alloc.sa_next_offset <= off)
    (source_memory_read_ranges inst vs)
Proof
  rpt gen_tac >> simp[source_memory_reads_disjoint_def, EVERY_MEM] >> rpt strip_tac >>
  rename1 `MEM rng (source_memory_read_ranges inst vs)` >>
  PairCases_on `rng` >> simp[] >>
  qpat_x_assum `!e. MEM e _ ==> _` drule >> simp[] >>
  strip_tac >> gvs[] >> first_x_assum drule >> decide_tac
QED

Theorem context_writes_preserve_spills[local]:
  !cp inst vs m m'. context_source_memory_writes_disjoint cp inst vs /\
  (!i. EVERY (\range. ~byte_in_memory_range range i)
         (source_memory_write_ranges inst vs) ==>
       read_byte i m' = read_byte i m) ==>
  !i. context_spill_byte cp i ==> read_byte i m' = read_byte i m
Proof
  rpt gen_tac >> simp[context_source_memory_writes_disjoint_def, context_spill_byte_def,
       EVERY_MEM] >> rpt strip_tac >> first_x_assum irule >>
  rpt strip_tac >>
  rename1 `MEM rng (source_memory_write_ranges inst vs)` >>
  PairCases_on `rng` >> gvs[byte_in_memory_range_def] >>
  qpat_x_assum `!e. MEM e _ ==> _` drule >> simp[] >>
  qexists_tac `r` >> simp[] >> decide_tac
QED

Theorem context_writes_local[local]:
  !cp inst vs r alloc. context_source_memory_writes_disjoint cp inst vs /\ MEM r cp.cp_regions /\
  r.sr_spill_base <= alloc.sa_spill_base /\
  alloc.sa_next_offset <= r.sr_spill_end ==>
  source_memory_writes_disjoint alloc inst vs
Proof
  rpt gen_tac >> simp[context_source_memory_writes_disjoint_def,
       source_memory_writes_disjoint_def, EVERY_MEM] >> rpt strip_tac >>
  rename1 `MEM rng (source_memory_write_ranges inst vs)` >>
  PairCases_on `rng` >> simp[] >>
  qpat_x_assum `!e. MEM e _ ==> _` drule >> simp[] >>
  strip_tac >> gvs[] >> first_x_assum drule >> decide_tac
QED

Theorem frame_view_safe_step[local]:
  !fuel ctx cp fn ra inst vs vs' m r alloc.
  step_inst fuel ctx inst vs = OK vs' /\
  inst.inst_opcode <> INVOKE /\ ~is_param_opcode inst.inst_opcode /\
  ~is_terminator inst.inst_opcode /\
  codegen_ready_fn fn /\ opaque_use_ok fn /\ retpc_shape_ok fn /\
  MEM inst (fn_insts fn) /\
  source_memory_reads_disjoint cp inst vs /\
  context_source_memory_writes_disjoint cp inst vs /\
  context_memory_rel cp vs.vs_memory m /\ MEM r cp.cp_regions /\
  r.sr_spill_base <= alloc.sa_spill_base /\
  alloc.sa_next_offset <= r.sr_spill_end ==>
  ?m'. step_inst fuel ctx inst (frame_view fn ra vs with vs_memory := m) =
         OK (frame_view fn ra vs' with vs_memory := m') /\
       (!i. read_byte i m = read_byte i vs.vs_memory ==>
            read_byte i m' = read_byte i vs'.vs_memory) /\
       (!i. context_spill_byte cp i ==> read_byte i m' = read_byte i m) /\
       inst_memory_safe alloc inst (frame_view fn ra vs with vs_memory := m)
         (frame_view fn ra vs' with vs_memory := m')
Proof
  rpt gen_tac >> strip_tac >>
  drule context_reads_agree >> disch_then drule >> disch_then assume_tac >>
  drule_all step_inst_frame_view >>
  disch_then (qspec_then `ra` strip_assume_tac) >>
  drule context_writes_preserve_spills >> disch_then drule >>
  disch_then assume_tac >>
  qexists_tac `m'` >> simp[] >>
  simp[inst_memory_safe_def, step_mem_safe_def,
       source_memory_writes_disjoint_def, source_write_ranges_frame_view] >>
  conj_tac
  >- (rpt strip_tac >> sym_tac >> first_x_assum irule >>
      simp[context_spill_byte_def] >> goal_assum (drule_at Any) >>
      simp[] >> decide_tac) >>
  drule_all context_writes_local >> simp[source_memory_writes_disjoint_def]
QED

Theorem frame_local_result[local]:
  !ctx cp lo fn ra rest mem0 ps vs ast ps' vs' out r m'.
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs ast /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  ~vs'.vs_halted /\ n2w cp.cp_initial_fmp = vs'.vs_initial_fmp /\
  venom_asm_rel lo ps' (frame_view fn ra vs' with vs_memory := m') out /\
  (!i. read_byte i ast.as_memory = read_byte i vs.vs_memory ==>
       read_byte i m' = read_byte i vs'.vs_memory) /\
  (!i. context_spill_byte cp i ==> read_byte i m' = read_byte i ast.as_memory) ==>
  fn_frame_inv ctx cp lo fn ra rest mem0 ps' vs'
    (out with as_stack := out.as_stack ++ rest)
Proof
  rpt gen_tac >> strip_tac >> rename1 `MEM r cplan.cp_regions` >>
  `memory_rel ps'.ps_alloc m' out.as_memory` by fs[venom_asm_rel_def] >>
  `!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
       read_byte b m' = read_byte b out.as_memory` by
    metis_tac[memory_rel_outside_region] >>
  `context_memory_rel cplan vs'.vs_memory out.as_memory` by
    (simp[context_memory_rel_def] >> rpt strip_tac >>
     `read_byte i ast.as_memory = read_byte i vs.vs_memory` by
       (fs[fn_frame_inv_def, context_venom_asm_rel_def,
           context_memory_rel_def, frame_view_def] >> metis_tac[]) >>
     `~(r.sr_spill_base <= i /\ i < r.sr_spill_end)` by
       metis_tac[context_spill_byte_of_region] >> metis_tac[]) >>
  `context_venom_asm_rel cplan lo ps' (frame_view fn ra vs') out` by
    (irule venom_asm_rel_context >> conj_tac
     >- simp[frame_view_def] >> qexists_tac `m'` >> simp[]) >>
  fs[fn_frame_inv_def] >> simp[fn_frame_inv_def] >> conj_tac
  >- (rpt strip_tac >>
      `~(r.sr_spill_base <= b /\ b < r.sr_spill_end)` by
        metis_tac[closure_spill_byte_own] >> metis_tac[]) >>
  qexists_tac `r` >> simp[]
QED

Theorem frame_view_control_fields[local]:
  (frame_view fn ra vs).vs_prev_bb = vs.vs_prev_bb /\
  (frame_view fn ra vs).vs_initial_fmp = vs.vs_initial_fmp
Proof
  simp[frame_view_def]
QED

(* Every non-INVOKE, non-jump instruction whose step is OK, against the frame
   invariant: gen_inst_ok_sim run on the frame's own stack against the frame
   view (frameViewStep commutes the step with it), extended below the frame
   with asm_steps_frame.  The premises are gen_inst_ok_sim's, with the
   operand facts read through the frame view, and the spill-interval
   memory facts replaced by the context-level obligations and the
   invariant's region clause for the output planner state.
   A revert forwarding's RETURNDATACOPY (in_revert_forward) is exempt from
   codegen_memory_obligations' disjointness, so this theorem's memory
   premises are not available for it and it is outside this theorem; the
   function-level proof handles it separately. *)
Theorem gen_inst_frame_sim:
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
    opaque_use_ok fn /\ retpc_shape_ok fn /\
    ~is_param_opcode inst.inst_opcode /\
    (* The invariant's region clause for the output planner state. *)
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf base ps /\
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
       shallow enough to duplicate or available from the spill map.
       generated_plan_state_wf is structural and does not imply ownership. *)
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
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
    prefix_spill_wf cp.cp_initial_fmp lo (FRONT ops) ps /\
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
  qpat_assum `fn_frame_inv _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [fn_frame_inv_def]) >>
  `venom_asm_rel lo ps
     (frame_view fn ra vs with vs_memory := as.as_memory)
     (as with as_stack := top)` by
    (drule context_venom_asm_rel_local >> simp[]) >>
  `context_memory_rel cplan vs.vs_memory as.as_memory` by
    fs[context_venom_asm_rel_def, frame_view_def] >>
  gen_tac >> strip_tac >>
  `?m'. step_inst fuel ctx inst
      (frame_view fn ra vs with vs_memory := as.as_memory) =
      OK (frame_view fn ra vs' with vs_memory := m') /\
    (!i. read_byte i as.as_memory = read_byte i vs.vs_memory ==>
         read_byte i m' = read_byte i vs'.vs_memory) /\
    (!i. context_spill_byte cplan i ==> read_byte i m' = read_byte i as.as_memory) /\
    inst_memory_safe ps'.ps_alloc inst
      (frame_view fn ra vs with vs_memory := as.as_memory)
      (frame_view fn ra vs' with vs_memory := m')` by
    (irule frame_view_safe_step >> goal_assum (drule_at Any) >>
     simp[] >> qexists_tac `r` >> simp[]) >>
  `EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
      ps'.ps_alloc.sa_next_offset <= off) (source_memory_read_ranges inst vs)` by
    (irule context_reads_local >> qexistsl_tac [`cplan`, `r`] >> simp[]) >>
  `~MEM inst.inst_opcode [JMP; JNZ; DJMP]` by
    (simp[] >> rpt conj_tac >> strip_tac >> gvs[is_terminator_def]) >>
  `EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
      ps'.ps_alloc.sa_next_offset <= off)
      (source_memory_read_ranges inst
        (frame_view fn ra vs with vs_memory := as.as_memory))` by
    (simp[source_read_ranges_frame_view] >> fs[arithmeticTheory.ADD_COMM]) >>
  fs[] >>
  drule_all
    (SRULE [venomMemPropsTheory.eval_operand_with_memory, operand_val_memory_update,
      frame_view_control_fields, arithmeticTheory.ADD_COMM]
    (Q.INST [`initial_fmp` |-> `cplan.cp_initial_fmp`,
       `vs` |-> `frame_view fn ra vs with vs_memory := as.as_memory`,
       `as` |-> `as with as_stack := top`] (SPEC_ALL gen_inst_ok_sim))) >>
  strip_tac >> rename1 `venom_asm_rel _ ps' _ out` >>
  qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  qpat_x_assum `o2pc = _` SUBST_ALL_TAC >>
  `~vs'.vs_halted` by
    (`step_inst_base inst vs = OK vs'` by
       (qpat_x_assum `step_inst fuel ctx inst vs = OK vs'` mp_tac >>
        simp[step_inst_non_invoke]) >>
     drule venomInstProofs1Theory.step_inst_base_preserves_all >> simp[]) >>
  `n2w cplan.cp_initial_fmp = vs'.vs_initial_fmp` by
    (qpat_assum `step_inst fuel ctx inst vs = OK vs'`
       (mp_then Any mp_tac step_inst_non_invoke_preserves_initial_fmp) >> simp[]) >>
  qexistsl_tac [`n`, `out with as_stack := out.as_stack ++ rest`] >>
  conj_tac
  >- (`as with as_stack := top ++ rest = as` by
        simp[asmSemTheory.asm_state_component_equality] >>
      pop_assum (SUBST1_TAC o GSYM) >> irule asm_steps_frame >> simp[]) >>
  conj_tac >- (irule frame_local_result >> simp[] >> conj_tac
               >- (qexists_tac `r` >> simp[]) >>
               qexistsl_tac [`as`, `m'`, `ps`, `vs`] >> simp[]) >>
  qpat_x_assum `~is_terminator _ ==> _` mp_tac >>
  (impl_tac >- simp[]) >>
  rpt (pop_assum kall_tac) >> simp[] >> decide_tac
QED
