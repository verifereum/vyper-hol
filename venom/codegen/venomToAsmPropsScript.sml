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
 * Assembly GAS readings remain unconstrained (no S7 trace claim).
 *
 * TOP-LEVEL:
 *   fn_has_retpc, shared_state_rel, fn_entry_state_rel,
 *   fn_return_state_rel     — function boundary definitions
 *   gen_fn_simulation       — ADMITTED function-level simulation (M4.2),
 *                             from function entry
 *   gen_fn_frame_simulation — ADMITTED restatement from any later block
 *                             boundary, over frameRel$fn_frame_inv
 *
 * STATUS: The function-level Venom→Asm simulation target is open/cheated.
 * Several helper proof layers exist, but theorem statements/preconditions may
 * need stabilization before proof repair; see docs/compiler-proof-roadmap.md.
 *)

Theory venomToAsmProps
Ancestors
  frameRel codegenRel contextCodegenRelProps fnPlanDecomp blockSimHelpers
  cleanOpsSim genBlockSim codegen symbolResolve venomExecSemantics venomState
  venomInst fcgDefs livenessDefs dfgDefs cfgDefs fnPlanLineage list rich_list
  finite_map

(* ===== Function boundary (PLAN 5.9) ===== *)

Definition fn_has_retpc_def:
  fn_has_retpc fn <=>
    EXISTS (\inst. inst.inst_opcode = RETPC_PARAM)
      (get_params (HD fn.fn_blocks).bb_instructions)
End

(* Leftover outcomes are a running/function-return contract ONLY.
   terminal_rel still observes requests but not leftover outcomes or GAS. *)
Definition shared_state_rel_def:
  shared_state_rel vs as <=>
    venom_asm_terminal_rel vs as /\ as.as_outcomes = vs.vs_outcomes /\
    as.as_call_ctx = vs.vs_call_ctx /\ as.as_tx_ctx = vs.vs_tx_ctx /\
    as.as_block_ctx = vs.vs_block_ctx /\ as.as_code = vs.vs_code /\
    as.as_prev_hashes = vs.vs_prev_hashes
End

(* Fresh source variables need no stack-value relation at callee entry.
   ra is an opaque assembly address, not vs_return_pc_token; rest is caller-owned. *)
Definition fn_entry_state_rel_def:
  fn_entry_state_rel cp fn vs as ra rest <=>
    vs.vs_current_bb = (HD fn.fn_blocks).bb_label /\ ~vs.vs_halted /\
    vs.vs_vars = FEMPTY /\
    LENGTH vs.vs_params + (if fn_has_retpc fn then 1 else 0) =
      LENGTH (get_params (HD fn.fn_blocks).bb_instructions) /\
    as.as_stack =
      (if fn_has_retpc fn then [ra] else []) ++ REVERSE vs.vs_params ++ rest /\
    n2w cp.cp_initial_fmp = vs.vs_initial_fmp /\
    context_memory_rel cp vs.vs_memory as.as_memory /\
    shared_state_rel vs as
End

Definition fn_return_state_rel_def:
  fn_return_state_rel ctx cp fn vs' as as' <=>
    context_memory_rel cp vs'.vs_memory as'.as_memory /\
    (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
         read_byte b as'.as_memory = read_byte b as.as_memory) /\
    venom_asm_terminal_rel vs' as' /\ as'.as_outcomes = vs'.vs_outcomes /\
    as'.as_call_ctx = as.as_call_ctx /\ as'.as_tx_ctx = as.as_tx_ctx /\
    as'.as_block_ctx = as.as_block_ctx /\ as'.as_code = as.as_code /\
    as'.as_prev_hashes = as.as_prev_hashes
End

(* ===== Function-Level Simulation ===== *)

(* EXACT PLAN 5.9 target. Restates the ONE existing admission; no bridge or
   additional admitted subcase. Halt/Abort use terminal_rel, IntRet uses the
   explicit leftover-outcome and caller-frame contract above.

   The frame-aware invariant this needs is frameRel$fn_frame_inv, and the
   same simulation from a non-entry block boundary over it is
   gen_fn_frame_simulation below.  Deriving this entry form from it needs
   a simulation of the whole entry block (its parameter prefix turns
   fn_entry_state_rel into fn_frame_inv) and the preservation of the
   shared fields along run_blocks. *)
Theorem gen_fn_simulation:
  !fuel rpolicy unit cp prog i r fn vs as Inv ra pc_ret rest.
    let ctx = unit.cu_context;
        lo = SND (compute_label_offsets prog);
        o2pc = build_offset_to_pc prog in
    generate_context_plan ctx = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    i < LENGTH ctx.ctx_functions /\
    EL i ctx.ctx_functions = fn /\ EL i cp.cp_regions = r /\
    codegen_context_obligations Inv ctx cp /\
    reachability_closed Inv ctx /\ fn_entry_inv Inv ctx fn vs /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp r.sr_plan) /\
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
  cheat
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
   a join entered from a predecessor other than the DFS's first.  That a
   lineage state regenerates the block's DFS code is the successor-transfer
   obligation lineage_state_block_plan; its premise that no operand of fn
   is a dead_stack_marker is not implied by the others here, so it is
   assumed.  All the function-level premises stay fixed along the block
   induction; each step re-establishes the lineage, DFS and reachability
   premises at the successor.

   The entry block is excluded: its parameter prefix values the parameter
   variables in Venom one PARAM at a time while the planner already stacks
   them, which fn_entry_state_rel describes instead.  mem0 is the assembly
   memory at frame entry, so the return clause can state the preservation
   of every spill byte outside the frame's call-graph closure.
   retpc_shape_ok makes the code's final JUMP land at pc_ret. *)
Theorem gen_fn_frame_simulation:
  !fuel rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch growth
   spill_base lbl_ctr fn_ops ps_end bb ps ps_dfs block_ops ps_dfs_after
   vs as Inv ra pc_ret rest mem0.
    ctx = unit.cu_context /\
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    i < LENGTH ctx.ctx_functions /\
    EL i ctx.ctx_functions = fn /\ EL i cp.cp_regions = r /\
    retpc_shape_ok fn /\
    codegen_context_obligations Inv ctx cp /\
    reachability_closed Inv ctx /\ fn_entry_inv Inv ctx fn vs /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    ch = cleanup_caller_height (LENGTH ctx.ctx_functions) ctx
           (fcg_analyze ctx) fn.fn_name /\
    growth = cleanup_growth_table ctx (fcg_analyze ctx) /\
    spill_base = r.sr_spill_base /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
    fn_ops = r.sr_plan /\
    EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    lineage_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      vs.vs_current_bb ps /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      vs.vs_current_bb ps_dfs /\
    generate_block_plan liveness dfg cfg fn bb ps_dfs =
      SOME (block_ops, ps_dfs_after) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp block_ops) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
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
  cheat
QED
