(*
 * Venom IR → Assembly Correctness — Theorem Statements
 *
 * Simulation: for each Venom execution step, the generated asm
 * instructions (from stackPlanGen + planExec) preserve venom_asm_rel.
 *
 * Simulation lemmas use asm_steps (step-counted execution on the full
 * program) so PC is always meaningful and composes with run_asm.
 *
 * Preconditions: codegen_ready (SSA, SUE, normalized CFG, no bad opcodes).
 * Stated modulo gas.
 *
 * TOP-LEVEL:
 *   gen_inst_simulation     — per-instruction simulation
 *   gen_block_simulation    — block-level simulation
 *   gen_fn_simulation       — function-level simulation
 *)

Theory venomToAsmProps
Ancestors
  codegenRel

(* ===== Per-Instruction Simulation ===== *)

(* Core simulation lemma: after Venom steps one instruction and asm
   executes the generated plan, venom_asm_rel is maintained.

   Precondition asm_block_at ensures the generated instructions are
   placed at the current PC in the program. The conclusion uses
   asm_steps so PC is always tracked correctly.

   Covers continuation (OK) case only. Halting/aborting instructions
   are handled at the block level. *)
Theorem gen_inst_simulation:
  ∀fuel ctx label_offsets offset_to_pc fn_eom prog
   liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label ps vs as ops ps'.
    codegen_ready_fn fn ∧
    venom_asm_rel label_offsets fn_eom ps vs as ∧
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') ∧
    asm_block_at prog as.as_pc (execute_plan ops) ⇒
    ∀vs'. step_inst fuel ctx inst vs = OK vs' ⇒
      ∃n as'.
        asm_steps label_offsets offset_to_pc prog n as = AsmOK as' ∧
        venom_asm_rel label_offsets fn_eom ps' vs' as'
Proof
  cheat
QED

(* ===== Block-Level Simulation ===== *)

(* Running a basic block in Venom and executing the generated plan
   as asm steps produce related results.

   The generated instructions must be placed at the current PC
   (asm_block_at precondition). Covers all exec_result cases:
   OK (continuation), Halt, and Abort (both Revert and ExHalt). *)
Theorem gen_block_simulation:
  ∀fuel ctx label_offsets offset_to_pc fn_eom prog
   liveness dfg cfg fn bb ps vs as block_ops ps'.
    codegen_ready_fn fn ∧
    venom_asm_rel label_offsets fn_eom ps vs as ∧
    generate_block_plan liveness dfg cfg fn bb ps =
      SOME (block_ops, ps') ∧
    asm_block_at prog as.as_pc (execute_plan block_ops) ⇒
    (* OK case: block continues to next block *)
    (∀vs'. run_block fuel ctx bb vs = OK vs' ⇒
      ∃n as'.
        asm_steps label_offsets offset_to_pc prog n as = AsmOK as' ∧
        venom_asm_rel label_offsets fn_eom ps' vs' as') ∧
    (* Halt case *)
    (∀vs'. run_block fuel ctx bb vs = Halt vs' ⇒
      ∃n as'.
        asm_steps label_offsets offset_to_pc prog n as = AsmHalt as' ∧
        venom_asm_rel label_offsets fn_eom ps' vs' as') ∧
    (* Abort case: both revert and exceptional halt *)
    (∀a vs'. run_block fuel ctx bb vs = Abort a vs' ⇒
      ∃n as'.
        ((a = Revert_abort ∧
          asm_steps label_offsets offset_to_pc prog n as =
            AsmRevert as') ∨
         (a = ExHalt_abort ∧
          asm_steps label_offsets offset_to_pc prog n as =
            AsmFault as')) ∧
        venom_asm_rel label_offsets fn_eom ps' vs' as')
Proof
  cheat
QED

(* ===== Function-Level Simulation ===== *)

(* Full function simulation. The entire function's plan is placed
   in the program starting at some PC. Running the function in Venom
   and executing the asm produce related terminal results.

   Note: asm_block_at is implicitly required for each block via
   the codegen pipeline producing a correctly laid out program.
   The prog parameter IS the output of execute_plan on the full
   function plan (+ data segment). *)
Theorem gen_fn_simulation:
  ∀fuel ctx label_offsets offset_to_pc fn_eom prog
   fn fn_ops ps vs as.
    codegen_ready_fn fn ∧
    generate_fn_plan fn fn_eom 0 = SOME (fn_ops, ps) ∧
    venom_asm_rel label_offsets fn_eom (init_plan_state fn_eom) vs as ∧
    asm_block_at prog as.as_pc (execute_plan fn_ops) ⇒
    (* Halt case *)
    (∀vs'. run_function fuel ctx fn vs = Halt vs' ⇒
      ∃n as'.
        asm_steps label_offsets offset_to_pc prog n as = AsmHalt as' ∧
        venom_asm_rel label_offsets fn_eom ps vs' as') ∧
    (* Abort case *)
    (∀a vs'. run_function fuel ctx fn vs = Abort a vs' ⇒
      ∃n as'.
        ((a = Revert_abort ∧
          asm_steps label_offsets offset_to_pc prog n as =
            AsmRevert as') ∨
         (a = ExHalt_abort ∧
          asm_steps label_offsets offset_to_pc prog n as =
            AsmFault as')) ∧
        venom_asm_rel label_offsets fn_eom ps vs' as')
Proof
  cheat
QED
