(*
 * Function-boundary steps of the frame-aware simulation: RET, INVOKE and
 * the entry block's parameter prefix, against frameRel$fn_frame_inv and
 * frameRel's function boundary relations.
 *
 * TOP-LEVEL (all CHEATED):
 *   gen_ret_frame_sim     — RET: jump to the return address
 *   gen_invoke_frame_sim  — INVOKE, given the callee's gen_fn_simulation
 *   entry_params_frame_sim — the entry block's parameter prefix turns
 *                            fn_entry_state_rel into fn_frame_inv
 *)

Theory fnFrameBoundary
Ancestors
  fnFrameBoundaryGenRet fnFrameBoundaryEntryParams fnFrameBoundaryInvoke
  genFrameSim frameRel codegen
  contextCodegenRel codegenRel stackOpAsmSim stackOpSim blockSimHelpers
  unitShapeDefs genBlockSim stackPlanGen stackPlanTypes planExec asmSem
  venomExecSemantics venomState venomInst fcgDefs livenessDefs dfgDefs

(* ===== RET ===== *)

(* Used for RET in the block induction: gen_fn_frame_simulation's IntRet
   clause, whose conclusion this is.  RET's code reorders its operands to
   the top, the return-PC variable last, and JUMPs.  ps'.ps_stack = [] is
   the planner obligation that the frame's planner stack holds only RET's
   operands (all else is dead and popped; dead_stack_marker cells exist
   only on must-halt paths, which never reach RET), so what is left after
   the jump is the return values above rest.  The RET is in a reachable
   block (reachable_fn), where retpc_shape_ok makes its last operand a
   return-PC variable.

   Why it should hold: the last operand reads ra in the frame view, and
   fn has a RETPC_PARAM (retpc_var needs one; canonical_param_prefix puts
   it among the entry parameters), so fn_has_retpc and the JUMP lands at
   pc_ret; the other operands are ordinary (opaque_use_ok) and are the
   return values; the step changes no Venom state, so the memory, closure
   and shared fields carry over from fn_frame_inv.  RET's code has no
   SOSpill: a spill needs a planner stack of 17 or more cells, which
   RET's plan never shrinks below its operand count (no outputs, so no
   pops), contradicting ps'.ps_stack = [] with at most 16 operands.
   So no memory is written, and a restore only reads. *)
Theorem gen_ret_frame_sim:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' ra rest mem0 pc_ret.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = RET /\
    MEM inst (fn_insts (reachable_fn fn)) /\
    codegen_ready_fn fn /\ opaque_use_ok fn /\ retpc_shape_ok fn /\
    inst_wf inst /\
    generated_plan_state_wf base ps /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
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
    prefix_spill_wf cp.cp_initial_fmp lo (FRONT ops) ps /\
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
  drule_all ret_frame_prefix >>
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

(* ===== INVOKE ===== *)

(* Used for INVOKE in the block induction (all three of
   gen_fn_frame_simulation's clauses and the OK continuation).  The
   callee runs with the step's fuel, which is below the block
   induction's, so the hypothesis is gen_fn_simulation for every function
   at that fuel: the mutual induction hypothesis.  It is stated here
   without the context-level premises gen_fn_simulation shares with this
   lemma: no GAS anywhere in the context, and every INVOKE target has a
   return-PC parameter (the code pushes the return label above the
   arguments, which fn_entry_state_rel matches only then).  The callee's
   arity matches INVOKE's arguments by invoke_layout_wf, from
   fmp_lowered_context_wf in codegen_context_obligations.
   Callee placement is fnPlanPlace$fn_region_placed (the entry label is
   the function name, fn_shape_ok).  The remaining premises are
   gen_inst_frame_sim's.

   Why it should hold: the code pushes the arguments (as an ordinary
   instruction's inputs), the return label and the callee label, and
   jumps, so the callee starts in fn_entry_state_rel with ra the return
   label's offset and rest the caller's remaining stack; fn_entry_inv for
   the callee state is reachability_closed's INVOKE clause.  On IntRet the
   hypothesis lands at the return label with the return values on top;
   the caller's spill region is outside the callee's call-graph closure
   (fn is reachable and the reachable call graph is acyclic), so its
   spills survive, and bytes outside fn's closure are outside the
   callee's; the outputs are bound as the planner pushes them.  Halt and
   Abort pass through. *)
(* Enter the callee and instantiate its simulation; leaves the callee's
   three outcome clauses and the call-entry steps as assumptions. *)
val invoke_enter_tac =
  drule_all invoke_enter_callee >> strip_tac >>
  first_x_assum (qspecl_then [`j`, `callee`, `EL j cplan.cp_regions`, `cvs`,
    `cas`, `n2w ret_off`, `saved ++ rest`,
    `st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) + 3`]
    mp_tac) >>
  impl_tac
  >- (rpt conj_tac >>
      FIRST [first_assum ACCEPT_TAC, simp[] >> NO_TAC,
             qpat_x_assum `setup_callee _ _ _ = SOME _` mp_tac >>
               rw[setup_callee_def] >> fs[] >> NO_TAC,
             fs[] >> NO_TAC]) >>
  strip_tac >>
  `asm_steps lo o2pc prog
     (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) + 3) st =
   AsmOK cas` by
    (irule asm_steps_compose_ok >> qexists `mid` >>
     conj_tac >> first_assum ACCEPT_TAC);

Theorem gen_invoke_frame_sim:
  !fuel rpolicy unit cp prog ctx lo o2pc Inv liveness dfg cfg fn inst
   next_liveness is_halting next_is_term bb_label base ps vs as ops ps' r ra
   rest mem0 nm arg_ops.
    ctx = unit.cu_context /\
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    codegen_context_obligations Inv ctx cp /\
    reachability_closed Inv ctx /\
    MEM fn ctx.ctx_functions /\
    MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    Inv ctx fn inst vs /\ active_inst fn inst vs /\
    inst.inst_opcode = INVOKE /\
    inst.inst_operands = Label nm :: arg_ops /\
    ~vs.vs_call_ctx.cc_static /\
    (!f inst callee_name args callee.
       MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
       MEM inst (fn_insts f) /\
       inst.inst_opcode = INVOKE /\
       inst.inst_operands = Label callee_name :: args /\
       lookup_function callee_name ctx.ctx_functions = SOME callee ==>
       fn_has_retpc callee) /\
    (!j. j < LENGTH ctx.ctx_functions /\ (EL j ctx.ctx_functions).fn_name = nm ==>
       ?off pc. FLOOKUP lo nm = SOME off /\ off < dimword (:256) /\
                FLOOKUP o2pc off = SOME pc /\
                asm_block_at prog pc
                  (execute_plan cp.cp_initial_fmp (EL j cp.cp_regions).sr_plan)) /\
    (* The callee's function-level simulation at this fuel. *)
    (!j callee rj cvs cas cra crest cpc.
       j < LENGTH ctx.ctx_functions /\ EL j ctx.ctx_functions = callee /\
       EL j cp.cp_regions = rj /\
       MEM callee.fn_name (fcg_analyze ctx).fcg_reachable /\
       (!l. FLOOKUP cvs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
       fn_entry_inv Inv ctx callee cvs /\
       ~cvs.vs_call_ctx.cc_static /\
       asm_block_at prog cas.as_pc (execute_plan cp.cp_initial_fmp rj.sr_plan) /\
       LENGTH (get_params (HD callee.fn_blocks).bb_instructions) < dimword (:256) /\
       fn_entry_state_rel cp callee cvs cas cra crest /\
       (fn_has_retpc callee ==> FLOOKUP o2pc (w2n cra) = SOME cpc) ==>
       (!vs'. run_blocks fuel ctx callee cvs = Halt vs' ==>
          ?n as'. asm_steps lo o2pc prog n cas = AsmHalt as' /\
                  venom_asm_terminal_rel vs' as') /\
       (!a vs'. run_blocks fuel ctx callee cvs = Abort a vs' ==>
          ?n as'. ((a = Revert_abort /\
                    asm_steps lo o2pc prog n cas = AsmRevert as') \/
                   (a = ExHalt_abort /\
                    asm_steps lo o2pc prog n cas = AsmFault as')) /\
                  venom_asm_terminal_rel vs' as') /\
       (!ret vs'. run_blocks fuel ctx callee cvs = IntRet ret vs' ==>
          ?n as'. asm_steps lo o2pc prog n cas = AsmOK as' /\
                  as'.as_pc = cpc /\
                  as'.as_stack = REVERSE ret.iret_values ++ crest /\
                  fn_return_state_rel ctx cp callee vs' cas as')) /\
    opaque_use_ok fn /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    inst_wf inst /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
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
    prefix_spill_wf cp.cp_initial_fmp lo (FRONT ops) ps /\
    (!off. MEM (SORestore off) ops ==> off < dimword (:256)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
    (!vs'. step_inst fuel ctx inst vs = OK vs' ==>
       ?n as'.
         asm_steps lo o2pc prog n as = AsmOK as' /\
         fn_frame_inv ctx cp lo fn ra rest mem0 ps' vs' as' /\
         as'.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp ops)) /\
    (!vs'. step_inst fuel ctx inst vs = Halt vs' ==>
       ?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
               venom_asm_terminal_rel vs' as') /\
    (!a vs'. step_inst fuel ctx inst vs = Abort a vs' ==>
       ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
                (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
               venom_asm_terminal_rel vs' as')
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `codegen_context_obligations Inv ctx cplan` >>
  rename1 `fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st` >>
  rename1 `generated_plan_state_wf spillbase ps` >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- suspend "ok"
  >- (drule_all invoke_source_halt >> strip_tac >> invoke_enter_tac >>
      first_x_assum drule >> strip_tac >>
      qexistsl [`LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) + 3 + n`,
        `as'`] >>
      metis_tac[asm_steps_compose_halt]) >>
  drule_all invoke_source_abort >> strip_tac >> invoke_enter_tac >>
  first_x_assum drule >> strip_tac >>
  qexistsl [`LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) + 3 + n`,
    `as'`] >>
  metis_tac[asm_steps_compose_revert, asm_steps_compose_fault]
QED

Resume gen_invoke_frame_sim[ok]:
  drule_all invoke_source_ok >> strip_tac >> invoke_enter_tac >>
  first_x_assum drule >> strip_tac >>
  rename1 `asm_steps lo o2pc prog n cas = AsmOK asr` >>
  drule_all invoke_plan_decompose >> strip_tac >>
  map_every (fn q => qpat_x_assum q kall_tac) [`ctx = _`, `lo = _`, `o2pc = _`] >>
  gvs[] >>
  rename1 `emit_input_plan INVOKE _ _ ps = (iops, prepared)` >>
  rename1 `reorder_plan _ _ prepared = (rops, arranged)` >>
  rename1 `fresh_label "return_label" _ = (ret_lbl, called)` >>
  suspend "frame"
QED

Resume gen_invoke_frame_sim[frame]:
  `ordered_spill_regions cplan.cp_regions /\ ctx_wf ctx` by
    fs[codegen_context_obligations_def, context_plan_layout_wf_def] >>
  `fn_directly_calls ctx fn.fn_name (EL j ctx.ctx_functions).fn_name` by
    metis_tac[invoke_direct_call] >>
  `~TC (fn_directly_calls ctx) fn.fn_name fn.fn_name` by
    metis_tac[invoke_context_no_cycle] >>
  qspecl_then [`spillbase`, `ps`, `inst`, `next_liveness`, `iops`, `prepared`,
    `dfg`, `rops`, `arranged`] mp_tac invoke_entry_structural >>
  impl_tac >- fs[] >> strip_tac >>
  `ALL_DISTINCT inst.inst_outputs` by
    metis_tac[codegen_ready_inst_outputs_distinct] >>
  `EVERY (\x. ~retpc_var fn x) inst.inst_outputs` by
    (simp[listTheory.EVERY_MEM] >> rpt gen_tac >> strip_tac >> irule frameViewFactsTheory.noncopy_output_not_retpc >>
     conj_tac >- fs[codegen_ready_fn_def] >> qexists `inst` >> simp[]) >>
  `!off. MEM (SOSpill off) (pops ++ opts) ==> off < dimword (:256)` by
    (qspecl_then [`cplan.cp_initial_fmp`, `lo`, `iops`, `rops`,
       `(EL j ctx.ctx_functions).fn_name`, `ret_lbl`, `inst.inst_outputs`, `next_liveness`, `is_halting`, `called`,
       `pops`, `popped`, `dfg`, `inst`, `next_is_term`, `opts`, `swapped`, `ps`]
       mp_tac invoke_cleanup_spill_bounds >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  `fn_return_state_rel ctx cplan (EL j ctx.ctx_functions) rvs mid asr` by
    (qpat_x_assum `fn_return_state_rel _ _ _ _ _ asr` mp_tac >>
     simp[fn_return_state_rel_def]) >>
  `asm_block_at prog asr.as_pc
     (execute_plan cplan.cp_initial_fmp (SOLabel ret_lbl :: (pops ++ opts)))` by
    (`asr.as_pc = st.as_pc +
        LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) + 3` by fs[] >>
     pop_assum SUBST1_TAC >> irule invoke_return_block >>
     qexists `(EL j ctx.ctx_functions).fn_name` >> first_assum ACCEPT_TAC) >>
  qspecl_then [`ctx`, `cplan`, `lo`, `o2pc`, `prog`, `fn`, `ra`, `rest`, `mem0`,
    `arranged`, `compute_operands inst`, `args`, `vs`, `mid`, `saved`,
    `ret.iret_values`, `EL j ctx.ctx_functions`, `rvs`, `ret`, `vs'`, `asr`, `r`,
    `inst.inst_outputs`, `next_liveness`, `is_halting`, `dfg`, `inst`,
    `next_is_term`, `ret_lbl`, `called`, `pops`, `popped`, `opts`, `swapped`,
    `release_dead_spills next_liveness swapped`] mp_tac invoke_return_frame >>
  impl_tac
  >- (rpt conj_tac >>
      FIRST [first_assum ACCEPT_TAC, simp[] >> NO_TAC, fs[] >> NO_TAC]) >>
  strip_tac >>
  rename1 `asm_steps lo o2pc prog m asr = AsmOK fin` >>
  qexistsl [`LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) + 3 + n + m`,
    `fin`] >>
  rpt conj_tac
  >- metis_tac[asm_steps_compose_ok]
  >- first_assum ACCEPT_TAC >>
  fs[execute_plan_def, exec_stack_op_def]
QED

Finalise gen_invoke_frame_sim

(* ===== Entry parameters ===== *)

(* Used to derive gen_fn_simulation from gen_fn_frame_simulation: the
   entry block's label and parameter code (prepare_params_plan, from the
   function planner's initial state, which is the entry block's DFS
   state) take fn_entry_state_rel to fn_frame_inv, with mem0 the entry
   memory.  Venom runs the PARAM / FMP_PARAM / RETPC_PARAM prefix one
   instruction at a time; the first conjunct about exec_block says the
   block's run from index 0 is its run from vs_p, past the prefix.  The
   rest of the entry block then runs as any block body does.  The region
   premise is fn_frame_inv's region clause for ps1, as in genFrameSim.
   With 17 or more parameters popmany_plan and optimistic_swap_plan can
   spill; the offset bound keeps those pushes from wrapping, as the
   per-instruction lemmas' SORestore bound does.  The parameter-count
   bound keeps PARAM's word ordinal from wrapping: without it, a function
   with more than 2^256 parameters is a counterexample
   (fnFrameBoundaryEntryParams$entry_params_frame_sim_counterexample).
   Every parameter is on the entry stack, so the stack-height bound
   discharges it.

   Why it should hold: canonical_param_prefix orders the PARAM indices and
   puts RETPC_PARAM last, and fn_entry_state_rel stacks ra above
   REVERSE vs_params, so pushing the outputs in order (bottom-first plan
   stack) matches the assembly stack, the RETPC_PARAM output reading ra
   in the frame view; the label step is a JUMPDEST; popmany_plan and
   optimistic_swap_plan only drop dead outputs and swap; the spill map is
   empty; shared_state_rel and context_memory_rel give the rest of
   context_venom_asm_rel. *)
Theorem entry_params_frame_sim:
  !fuel ctx cp lo o2pc prog liveness fn ch growth spill_base lbl_ctr ps0
   param_ops ps1 r vs as ra rest.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    ps0 = init_cleanup_plan_state ch growth spill_base lbl_ctr /\
    prepare_params_plan liveness fn ps0 = (param_ops, ps1) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= spill_base /\
    ps1.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) param_ops ==> off < dimword (:256)) /\
    LENGTH (get_params (HD fn.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_entry_state_rel cp fn vs as ra rest /\
    asm_block_at prog as.as_pc
      (execute_plan cp.cp_initial_fmp
         (SOLabel (HD fn.fn_blocks).bb_label :: param_ops))
    ==>
    ?n as' vs_p.
      asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = as.as_pc +
        LENGTH (execute_plan cp.cp_initial_fmp
                  (SOLabel (HD fn.fn_blocks).bb_label :: param_ops)) /\
      exec_block fuel ctx (HD fn.fn_blocks) (vs with vs_inst_idx := 0) =
        exec_block fuel ctx (HD fn.fn_blocks) vs_p /\
      vs_p.vs_inst_idx = LENGTH (get_params (HD fn.fn_blocks).bb_instructions) /\
      fn_frame_inv ctx cp lo fn ra rest as.as_memory ps1 vs_p as'
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `fn_entry_state_rel cplan fn vs a ra rest` >>
  qabbrev_tac `params = get_params (HD fn.fn_blocks).bb_instructions` >>
  qabbrev_tac `vp = (entry_bind_pairs (entry_param_pairs vs params) vs)
    with vs_inst_idx := LENGTH params` >>
  `exec_block fuel ctx (HD fn.fn_blocks) (vs with vs_inst_idx := 0) =
    exec_block fuel ctx (HD fn.fn_blocks) vp` by
    (unabbrev_all_tac >> irule bounded_entry_param_skip >> metis_tac[]) >>
  `context_venom_asm_rel cplan lo
    (ps0 with ps_stack := MAP (\i. Var (HD i.inst_outputs)) params)
    (frame_view fn ra vp)
    (a with as_stack := (if fn_has_retpc fn then [ra] else []) ++ REVERSE vs.vs_params)` by
    (irule bounded_entry_installed_context_rel >> metis_tac[]) >>
  qabbrev_tac `top = (if fn_has_retpc fn then [ra] else []) ++ REVERSE vs.vs_params` >>
  qabbrev_tac `local = a with as_stack := top` >>
  qabbrev_tac `start = local with as_pc := local.as_pc + 1` >>
  `asm_block_at prog local.as_pc [AsmLabel (HD fn.fn_blocks).bb_label] /\
   asm_block_at prog start.as_pc (execute_plan cplan.cp_initial_fmp param_ops)` by
    (qpat_x_assum `asm_block_at _ _ _` mp_tac >>
     pure_rewrite_tac[execute_plan_def, listTheory.MAP, listTheory.FLAT, exec_stack_op_def,
       asm_block_at_append] >>
     simp[Abbr `local`, Abbr `start`]) >>
  `asm_steps lo o2pc prog 1 local = AsmOK start` by
    (simp[Abbr `start`] >> irule label_op_asm_steps >> metis_tac[]) >>
  `context_venom_asm_rel cplan lo
    (ps0 with ps_stack := MAP (\i. Var (HD i.inst_outputs)) params)
    (frame_view fn ra vp) start` by
    gvs[Abbr `start`, context_venom_asm_rel_def] >>
  `params = get_params (HD fn.fn_blocks).bb_instructions` by simp[Abbr `params`] >>
  qabbrev_tac `installed = ps0 with ps_stack := MAP (\i. Var (HD i.inst_outputs)) params` >>
  `installed = ps0 with ps_stack := MAP (\i. Var (HD i.inst_outputs)) params` by
    simp[Abbr `installed`] >>
  drule_all entry_prepare_params_context_sim >>
  disch_then (qspecl_then [`o2pc`, `ctx`] strip_assume_tac) >>
  qpat_x_assum `installed = _` kall_tac >>
  qpat_x_assum `params = get_params _` kall_tac >>
  `asm_steps lo o2pc prog (1 + LENGTH (execute_plan cplan.cp_initial_fmp param_ops))
    (a with as_stack := top) = AsmOK st'` by
    (gvs[Abbr `local`] >>
     once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
     irule asm_steps_compose_ok >> qexists `start` >> simp[]) >>
  `a.as_stack = top ++ rest` by gvs[fn_entry_state_rel_def, Abbr `top`] >>
  `~vp.vs_halted /\ n2w cplan.cp_initial_fmp = vp.vs_initial_fmp` by
    gvs[Abbr `vp`, entry_bind_pairs_normal, fn_entry_state_rel_def] >>
  `!b. ~closure_spill_byte ctx cplan fn.fn_name b ==>
    read_byte b st'.as_memory = read_byte b a.as_memory` by
    gvs[Abbr `start`, Abbr `local`] >>
  drule_all entry_local_run_frame_inv >> strip_tac >>
  qexistsl [`1 + LENGTH (execute_plan cplan.cp_initial_fmp param_ops)`, `a'`, `vp`] >>
  simp[] >> conj_tac
  >- gvs[Abbr `start`, Abbr `local`, execute_plan_def, exec_stack_op_def] >>
  simp[Abbr `vp`]
QED

(* The other boundary simulations are separate proof tasks.  Certify this
   entry theorem and every helper in its dedicated theory independently. *)
val _ = List.app (fn (name, th) =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn tag => tag = "DISK_THM") oracles then ()
    else raise Fail ("non-clean entry parameter proof: " ^ name)
  end) (("entry_params_frame_sim", entry_params_frame_sim) ::
        DB.thms "fnFrameBoundaryEntryParams");
