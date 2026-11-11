(*
 * Venom IR → Assembly Correctness — Theorem Statements
 *
 * Function-level simulation for generated context plans. Proved
 * instruction and block helpers remain in the ancestor proof theories.
 *
 * Simulation lemmas use asm_steps (step-counted execution on the full
 * program) so PC is always meaningful and composes with run_asm.
 *
 * Concrete codegen program and label maps; frame-aware entry and return.
 * Venom and assembly GAS readings agree at entry and return.
 *
 * The function boundary definitions (fn_has_retpc, shared_state_rel,
 * fn_entry_state_rel, fn_return_state_rel) are in frameRel.
 *
 * TOP-LEVEL:
 *   gen_fn_simulation       — function-level simulation (M4.2), from
 *                             function entry
 *   gen_fn_frame_simulation — the same from any later block boundary,
 *                             over frameRel$fn_frame_inv
 *
 * Both are proved together by induction on fuel; the steps are
 * fnEntryStep$fn_entry_block_step and fnBlockStep$fn_block_frame_step.
 *)

Theory venomToAsmProps
Ancestors
  frameRel codegenRel contextCodegenRelProps fnPlanDecomp blockSimHelpers
  cleanOpsSim genBlockSim codegen symbolResolve venomExecSemantics venomState
  venomInst fcgDefs livenessDefs dfgDefs cfgDefs fnPlanLineage
  fnSimSpec fnBlockStep fnEntryStep
  list rich_list
  finite_map

(* ===== Fuel induction ===== *)

(* Both function theorems at once, by induction on fuel: run_blocks 0 is
   an Error, and the step is the entry block (fnEntryStep) or a later
   block (fnBlockStep), each given both theorems at the smaller fuel for
   the callees an INVOKE runs and for the rest of the run. *)
Theorem gen_fn_sims_all[local]:
  !fuel. gen_fn_sim_at fuel /\ gen_fn_frame_sim_at fuel
Proof
  Induct
  >- (simp[gen_fn_sim_at_def, gen_fn_frame_sim_at_def] >>
      rpt strip_tac >> gvs[Once run_blocks_def]) >>
  metis_tac[fn_block_frame_step, fn_entry_block_step]
QED

(* ===== Function-Level Simulation ===== *)

(* EXACT PLAN 5.9 target. Restates the ONE existing admission; no bridge or
   additional admitted subcase. Halt/Abort use terminal_rel, IntRet uses the
   explicit leftover-outcome and caller-frame contract above.

   The frame-aware invariant this needs is frameRel$fn_frame_inv, and the
   same simulation from a non-entry block boundary over it is
   gen_fn_frame_simulation below.  Deriving this entry form from it needs
   a simulation of the whole entry block (its parameter prefix turns
   fn_entry_state_rel into fn_frame_inv) and the preservation of the
   shared fields along run_blocks.

   fn is reachable in the call graph: the planner's acyclicity check covers
   only reachable functions, so this rules out unreachable recursion.  GAS
   needs no premise: both sides read the same reading list (shared_state_rel,
   fn_frame_inv), and gasFrameSim's gas_inst_frame_sim is its step.  Every INVOKE target has a return-PC parameter, as
   INVOKE's code pushes the return address above the arguments; the
   lowering gives every internal function one.  codegen_assembly checks
   that labels are distinct and the program fits 2-byte label pushes, so
   no premise carries those.  vs_labels agrees with the assembly label
   offsets, so Label operands have the same value in
   Venom and in the assembly.  The entry block has fewer than 2^256
   parameters, so PARAM's word ordinal doesn't wrap; an interim premise
   until the stack-height bound supplies it, as every parameter is on the
   entry stack. *)
Theorem gen_fn_simulation:
  !fuel rpolicy unit cp prog ctx lo o2pc i r fn vs as Inv ra pc_ret rest.
    ctx = unit.cu_context /\
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    i < LENGTH ctx.ctx_functions /\
    EL i ctx.ctx_functions = fn /\ EL i cp.cp_regions = r /\
    MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
    (!f inst callee_name args callee.
       MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
       MEM inst (fn_insts f) /\
       inst.inst_opcode = INVOKE /\
       inst.inst_operands = Label callee_name :: args /\
       lookup_function callee_name ctx.ctx_functions = SOME callee ==>
       fn_has_retpc callee) /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    codegen_context_obligations Inv ctx cp /\
    reachability_closed Inv ctx /\ fn_entry_inv Inv ctx fn vs /\
    ~vs.vs_call_ctx.cc_static /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp r.sr_plan) /\
    LENGTH (get_params (HD fn.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_entry_state_rel cp fn vs as ra rest /\
    (fn_has_retpc fn ==> FLOOKUP o2pc (w2n ra) = SOME pc_ret)
    ==>
    (!vs'. run_blocks fuel ctx fn vs = Halt vs' ==>
       ?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
               venom_asm_terminal_rel vs' as') /\
    (!a vs'. run_blocks fuel ctx fn vs = Abort a vs' ==>
       ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
                (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
               venom_asm_terminal_rel vs' as') /\
    (!ret vs'. run_blocks fuel ctx fn vs = IntRet ret vs' ==>
       ?n as'. asm_steps lo o2pc prog n as = AsmOK as' /\
               as'.as_pc = pc_ret /\
               as'.as_stack = REVERSE ret.iret_values ++ rest /\
               fn_return_state_rel ctx cp fn vs' as as')
Proof
  rpt gen_tac >>
  mp_tac (CONJUNCT1 (SPEC_ALL gen_fn_sims_all)) >>
  PURE_REWRITE_TAC[gen_fn_sim_at_def] >>
  disch_then MATCH_ACCEPT_TAC
QED

(* The same simulation from any block boundary after the entry block, with
   fn_frame_inv as the state relation: the induction-hypothesis shape for
   the block induction.

   fn's code is the plan generate_context_plan made for it: the function
   planner run with fn's cleanup caller height, the context's growth
   table, region i's spill base, and the label counter the context planner
   had reached (lbl_ctr; cp does not record it, region i's plan pins it).
   The code at as.as_pc is the current block's DFS code, planned from
   ps_dfs.  ps is the state fn_frame_inv is about: the lineage state of the
   run-time path to the block (fnPlanLineage), which differs from ps_dfs at
   a join entered from a predecessor other than the DFS's first.  It is
   stated as a lineage_entry from pred, the block vs_prev_bb names, so the
   planner state matches the edge whose PHI values the block reads.  That a
   lineage state regenerates the block's DFS code is the successor-transfer
   obligation lineage_state_block_plan, whose premise that no operand of
   fn is a dead_stack_marker follows from codegen_ready_fn.  All the
   function-level premises stay fixed along the block
   induction; each step re-establishes the lineage, DFS and reachability
   premises at the successor.

   The entry block is excluded: its parameter prefix values the parameter
   variables in Venom one PARAM at a time while the planner already stacks
   them, which fn_entry_state_rel describes instead.  mem0 is the assembly
   memory at frame entry, so the return clause can state the preservation
   of every spill byte outside the frame's call-graph closure.

   fn is reachable in the call graph: the planner's acyclicity check covers
   only reachable functions, so this rules out unreachable recursion.  GAS
   needs no premise: both sides read the same reading list (shared_state_rel,
   fn_frame_inv), and gasFrameSim's gas_inst_frame_sim is its step.  Every INVOKE target has a return-PC parameter, and
   codegen_assembly checks label distinctness and program size, as for
   gen_fn_simulation.  vs_labels agrees with the assembly label offsets, so Label operands have the same value in Venom and in the
   assembly.  DFG alias soundness: every operand on ps's stack or in its
   spill map has the value of its ASSIGN-chain root (normalize_operand),
   so the planner's alias-only reorder steps read the right word; it is
   stated on the planner's live entries only, which the block induction
   can re-establish at the successor. *)
Theorem gen_fn_frame_simulation:
  !fuel rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch growth
   spill_base lbl_ctr fn_ops ps_end bb pred ps ps_dfs block_ops ps_dfs_after
   vs as Inv ra pc_ret rest mem0.
    ctx = unit.cu_context /\
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    i < LENGTH ctx.ctx_functions /\
    EL i ctx.ctx_functions = fn /\ EL i cp.cp_regions = r /\
    MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
    (!f inst callee_name args callee.
       MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
       MEM inst (fn_insts f) /\
       inst.inst_opcode = INVOKE /\
       inst.inst_operands = Label callee_name :: args /\
       lookup_function callee_name ctx.ctx_functions = SOME callee ==>
       fn_has_retpc callee) /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    codegen_context_obligations Inv ctx cp /\
    reachability_closed Inv ctx /\ fn_entry_inv Inv ctx fn vs /\
    ~vs.vs_call_ctx.cc_static /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    ch = cleanup_caller_height (LENGTH ctx.ctx_functions) ctx
           (fcg_analyze ctx) fn.fn_name /\
    growth = cleanup_growth_table ctx (fcg_analyze ctx) /\
    spill_base = r.sr_spill_base /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
    fn_ops = r.sr_plan /\
    ps_end.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      pred bb.bb_label ps /\
    vs.vs_prev_bb = SOME pred /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      vs.vs_current_bb ps_dfs /\
    generate_block_plan liveness dfg cfg fn bb ps_dfs =
      SOME (block_ops, ps_dfs_after) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp block_ops) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    (fn_has_retpc fn ==> FLOOKUP o2pc (w2n ra) = SOME pc_ret)
    ==>
    (!vs'. run_blocks fuel ctx fn vs = Halt vs' ==>
       ?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
               venom_asm_terminal_rel vs' as') /\
    (!a vs'. run_blocks fuel ctx fn vs = Abort a vs' ==>
       ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
                (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
               venom_asm_terminal_rel vs' as') /\
    (!ret vs'. run_blocks fuel ctx fn vs = IntRet ret vs' ==>
       ?n as'. asm_steps lo o2pc prog n as = AsmOK as' /\
               as'.as_pc = pc_ret /\
               as'.as_stack = REVERSE ret.iret_values ++ rest /\
               context_memory_rel cp vs'.vs_memory as'.as_memory /\
               (!b. context_spill_byte cp b /\
                    ~closure_spill_byte ctx cp fn.fn_name b ==>
                    read_byte b as'.as_memory = read_byte b mem0) /\
               shared_state_rel vs' as')
Proof
  rpt gen_tac >>
  mp_tac (CONJUNCT2 (SPEC_ALL gen_fn_sims_all)) >>
  PURE_REWRITE_TAC[gen_fn_frame_sim_at_def] >>
  disch_then MATCH_ACCEPT_TAC
QED
