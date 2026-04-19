(*
 * Plan Simulation — Terminal instruction dispatch + composition
 *
 * Terminal asm instructions (STOP, RETURN, REVERT, INVALID,
 * SELFDESTRUCT) produce AsmHalt/AsmRevert/AsmFault.
 * These lemmas show the dispatch from asm_step through
 * asm_step_op to the specific handler.
 *
 * Combined with asm_one_step_result (stackOpAsmSimTheory)
 * and asm_steps_compose_halt/revert/fault (blockSimHelpersTheory),
 * these give the terminal portion of halt/abort simulation.
 *)


Theory planSim
Ancestors
  asmSem asmIR stackOpAsmSim list arithmetic

(* Dispatch definitions for evaluating asm_step_op on concrete names *)
val dispatch_ss = [asm_step_def, asm_step_op_def,
  asm_step_arith_def, asm_step_compare_def, asm_step_bitwise_def,
  asm_step_memory_def, asm_step_control_def, asm_step_extcall_def,
  asm_step_copy_def, asm_step_context_def,
  dup_table_def, swap_table_def, log_table_def];

(* RETURN: produces AsmHalt, needs stack >= 2 *)
Theorem asm_step_return:
  !lo o2pc st.
    LENGTH st.as_stack >= 2 ==>
    ?st'. asm_step lo o2pc (AsmOp "RETURN") st = AsmHalt st'
Proof
  rpt strip_tac >>
  simp dispatch_ss >>
  simp[asm_return_op_def] >>
  Cases_on `st.as_stack` >> fs[] >>
  Cases_on `t` >> fs[]
QED

(* REVERT: produces AsmRevert, needs stack >= 2 *)
Theorem asm_step_revert:
  !lo o2pc st.
    LENGTH st.as_stack >= 2 ==>
    ?st'. asm_step lo o2pc (AsmOp "REVERT") st = AsmRevert st'
Proof
  rpt strip_tac >>
  simp dispatch_ss >>
  simp[asm_revert_op_def] >>
  Cases_on `st.as_stack` >> fs[] >>
  Cases_on `t` >> fs[]
QED

(* SELFDESTRUCT: produces AsmHalt, needs stack >= 1 *)
Theorem asm_step_selfdestruct:
  !lo o2pc st.
    LENGTH st.as_stack >= 1 ==>
    ?st'. asm_step lo o2pc (AsmOp "SELFDESTRUCT") st = AsmHalt st'
Proof
  rpt strip_tac >>
  simp dispatch_ss >>
  simp[asm_selfdestruct_def] >>
  Cases_on `st.as_stack` >> fs[]
QED

(* ===== Empty-prefix specialization =====
   When the plan is just [SOEmit name] (no prefix ops),
   the proof is trivial: single asm step. *)

Theorem empty_prefix_halt:
  !lo o2pc prog st name.
    asm_block_at prog st.as_pc [AsmOp name] /\
    asm_step lo o2pc (AsmOp name) st = AsmHalt st ==>
    asm_steps lo o2pc prog 1 st = AsmHalt st
Proof
  metis_tac[asm_one_step_result]
QED
