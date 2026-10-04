(*
 * Venom IR → Assembly Correctness — Theorem Statements
 *
 * Function-level simulation for generated context plans. Proved
 * instruction and block helpers remain in the ancestor proof theories.
 *
 * Simulation lemmas use asm_steps (step-counted execution on the full
 * program) so PC is always meaningful and composes with run_asm.
 *
 * Preconditions: codegen_ready (SSA, SUE, normalized CFG, no bad opcodes).
 * Stated modulo gas.
 *
 * TOP-LEVEL:
 *   gen_fn_simulation       — function-level simulation
 *
 * STATUS: The function-level Venom→Asm simulation target is open/cheated.
 * Several helper proof layers exist, but theorem statements/preconditions may
 * need stabilization before proof repair; see docs/compiler-proof-roadmap.md.
 *)

Theory venomToAsmProps
Ancestors
  codegenRel contextCodegenRelProps fnPlanDecomp blockSimHelpers cleanOpsSim genBlockSim

(* ===== Function-Level Simulation ===== *)

(* Full function simulation for the region assigned by a successful context
   plan.  The ambient context relation masks every caller/callee spill region;
   the active function's local plan state starts at its assigned region base.
   The semantic proof gap is intentionally retained. *)
Theorem gen_fn_simulation:
  ∀fuel ctx cp i r fn label_offsets offset_to_pc prog
   vs as Inv.
    generate_context_plan ctx = SOME cp ∧
    i < LENGTH ctx.ctx_functions ∧
    EL i ctx.ctx_functions = fn ∧
    EL i cp.cp_regions = r ∧
    codegen_context_obligations Inv ctx cp ∧
    codegen_reachability_package Inv ctx vs ∧
    codegen_ready_fn fn ∧
    context_venom_asm_rel cp label_offsets
      (fn_init_ps fn r.sr_spill_base) vs as ∧
    asm_block_at prog as.as_pc
      (execute_plan cp.cp_initial_fmp r.sr_plan) ⇒
    (* Halt case *)
    (∀vs'. run_blocks fuel ctx fn vs = Halt vs' ⇒
      ∃n as'.
        asm_steps label_offsets offset_to_pc prog n as = AsmHalt as' ∧
        venom_asm_terminal_rel vs' as') ∧
    (* Abort case *)
    (∀a vs'. run_blocks fuel ctx fn vs = Abort a vs' ⇒
      ∃n as'.
        ((a = Revert_abort ∧
          asm_steps label_offsets offset_to_pc prog n as =
            AsmRevert as') ∨
         (a = ExHalt_abort ∧
          asm_steps label_offsets offset_to_pc prog n as =
            AsmFault as')) ∧
        venom_asm_terminal_rel vs' as')
Proof
  cheat
QED
