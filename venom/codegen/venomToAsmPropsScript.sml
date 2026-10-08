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
 *   closure_spill_byte, fn_return_state_rel — function boundary definitions
 *   gen_fn_simulation       — ADMITTED function-level simulation (M4.2)
 *
 * STATUS: The function-level Venom→Asm simulation target is open/cheated.
 * Several helper proof layers exist, but theorem statements/preconditions may
 * need stabilization before proof repair; see docs/compiler-proof-roadmap.md.
 *)

Theory venomToAsmProps
Ancestors
  codegenRel contextCodegenRelProps fnPlanDecomp blockSimHelpers cleanOpsSim genBlockSim
  codegen symbolResolve venomExecSemantics venomState venomInst fcgDefs
  list rich_list finite_map

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

Definition closure_spill_byte_def:
  closure_spill_byte ctx cp name b <=>
    ?r. MEM r cp.cp_regions /\ fcg_path ctx name r.sr_fn_name /\
        r.sr_spill_base <= b /\ b < r.sr_spill_end
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

   M4.2 still owes a frame-aware invariant, NOT context_venom_asm_rel with its
   equal model/assembly stack lengths and already-valued parameter variables:
   (1) exempt opaque return-address and GAS variables from stack/spill value
       matching (no source-GAS = assembly-reading premise);
   (2) at RET, the callee stack contains exactly the RET operands, above rest;
   (3) assembly steps preserve entries below the operands they pop.
   These are obligations, not theorems provided by this admission or by the
   boundary helpers. Caller spill preservation must cover the complement of
   the complete callee call-graph closure, not just its own spill interval. *)
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
