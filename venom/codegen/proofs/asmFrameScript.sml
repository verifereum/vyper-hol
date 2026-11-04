(*
 * Stack-frame extension for assembly steps.
 *
 * An assembly step reads and writes only the stack entries it pops and
 * pushes: a step that succeeds on a stack top succeeds on the same top
 * above any rest, with the rest intact.  The frame-aware simulation
 * (frameRel$fn_frame_inv) runs the local step lemmas on a frame's own
 * stack and extends their AsmOK runs below the frame with this; the
 * terminal results (AsmHalt, AsmRevert, AsmFault) are not lifted here.
 *
 * TOP-LEVEL:
 *   asm_step_frame   — one step
 *   asm_steps_frame  — a step-counted run
 * Helpers:
 *   asm_step_<class>_none   — a class's NONE depends only on the name
 *   asm_step_<class>_frame  — one dispatch class
 *   asm_step_op_frame       — AsmOp over the classes
 *)

Theory asmFrame
Ancestors
  asmSem asmFrameHelpers

Theorem asm_step_arith_none:
  (asm_step_arith name s = NONE) = (asm_step_arith name u = NONE)
Proof
  simp[asm_step_arith_def]
QED

Theorem asm_step_compare_none:
  (asm_step_compare name s = NONE) = (asm_step_compare name u = NONE)
Proof
  simp[asm_step_compare_def]
QED

Theorem asm_step_bitwise_none:
  (asm_step_bitwise name s = NONE) = (asm_step_bitwise name u = NONE)
Proof
  simp[asm_step_bitwise_def]
QED

Theorem asm_step_memory_none:
  (asm_step_memory name s = NONE) = (asm_step_memory name u = NONE)
Proof
  simp[asm_step_memory_def]
QED

Theorem asm_step_control_none:
  (asm_step_control o2pc name s = NONE) = (asm_step_control o2pc name u = NONE)
Proof
  simp[asm_step_control_def]
QED

Theorem asm_step_extcall_none:
  (asm_step_extcall name s = NONE) = (asm_step_extcall name u = NONE)
Proof
  simp[asm_step_extcall_def]
QED

Theorem asm_step_copy_none:
  (asm_step_copy name s = NONE) = (asm_step_copy name u = NONE)
Proof
  simp[asm_step_copy_def]
QED

Theorem asm_step_context_none:
  (asm_step_context name s = NONE) = (asm_step_context name u = NONE)
Proof
  simp[asm_step_context_def]
QED

Theorem asm_step_arith_frame:
  asm_step_arith name (s with as_stack := top) = SOME (AsmOK t) ==>
  asm_step_arith name (s with as_stack := top ++ rest) =
    SOME (AsmOK (t with as_stack := t.as_stack ++ rest))
Proof
  rw[asm_step_arith_def] >> metis_tac[asm_binop_frame, asm_ternop_frame]
QED

Theorem asm_step_compare_frame:
  asm_step_compare name (s with as_stack := top) = SOME (AsmOK t) ==>
  asm_step_compare name (s with as_stack := top ++ rest) =
    SOME (AsmOK (t with as_stack := t.as_stack ++ rest))
Proof
  rw[asm_step_compare_def] >> metis_tac[asm_binop_frame, asm_unop_frame]
QED

Theorem asm_step_bitwise_frame:
  asm_step_bitwise name (s with as_stack := top) = SOME (AsmOK t) ==>
  asm_step_bitwise name (s with as_stack := top ++ rest) =
    SOME (AsmOK (t with as_stack := t.as_stack ++ rest))
Proof
  rw[asm_step_bitwise_def] >> metis_tac[asm_binop_frame, asm_unop_frame]
QED

Theorem asm_step_memory_frame:
  asm_step_memory name (s with as_stack := top) = SOME (AsmOK t) ==>
  asm_step_memory name (s with as_stack := top ++ rest) =
    SOME (AsmOK (t with as_stack := t.as_stack ++ rest))
Proof
  rw[asm_step_memory_def] >>
  metis_tac[asm_pop_frame, asm_mload_frame, asm_mstore_frame, asm_mstore8_frame,
    asm_mcopy_frame, asm_push_val_frame, asm_sload_frame, asm_sstore_frame,
    asm_tload_frame, asm_tstore_frame, asm_sha3_frame]
QED

Theorem asm_step_control_frame:
  asm_step_control o2pc name (s with as_stack := top) = SOME (AsmOK t) ==>
  asm_step_control o2pc name (s with as_stack := top ++ rest) =
    SOME (AsmOK (t with as_stack := t.as_stack ++ rest))
Proof
  rw[asm_step_control_def] >>
  gvs[asm_return_op_not_ok, asm_revert_op_not_ok, asm_next_def] >>
  metis_tac[asm_jump_frame, asm_jumpi_frame]
QED

Theorem asm_step_extcall_frame:
  asm_step_extcall name (s with as_stack := top) = SOME (AsmOK t) ==>
  asm_step_extcall name (s with as_stack := top ++ rest) =
    SOME (AsmOK (t with as_stack := t.as_stack ++ rest))
Proof
  rw[asm_step_extcall_def] >> gvs[asm_selfdestruct_not_ok] >>
  metis_tac[asm_exec_call_frame, asm_exec_staticcall_frame,
    asm_exec_delegatecall_frame, asm_exec_create_frame, asm_exec_create2_frame]
QED

Theorem asm_step_copy_frame:
  asm_step_copy name (s with as_stack := top) = SOME (AsmOK t) ==>
  asm_step_copy name (s with as_stack := top ++ rest) =
    SOME (AsmOK (t with as_stack := t.as_stack ++ rest))
Proof
  rw[asm_step_copy_def] >>
  metis_tac[asm_copy_to_mem_frame, asm_returndatacopy_frame, asm_extcodecopy_frame]
QED

Theorem asm_step_context_frame:
  asm_step_context name (s with as_stack := top) = SOME (AsmOK t) ==>
  asm_step_context name (s with as_stack := top ++ rest) =
    SOME (AsmOK (t with as_stack := t.as_stack ++ rest))
Proof
  pure_rewrite_tac[asm_step_context_def] >>
  rpt IF_CASES_TAC >> simp[] >> strip_tac >>
  FIRST [irule asm_push_val_frame, irule asm_gas_frame,
         irule asm_state_unop_frame] >> simp[]
QED

Theorem asm_step_op_frame:
  asm_step_op o2pc name (s with as_stack := top) = AsmOK t ==>
  asm_step_op o2pc name (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  pure_rewrite_tac[asm_step_op_def] >>
  reverse (Cases_on `asm_step_arith name (s with as_stack := top)`)
  >- (simp[] >> strip_tac >> gvs[] >> drule asm_step_arith_frame >> simp[]) >>
  `asm_step_arith name (s with as_stack := top ++ rest) = NONE`
    by metis_tac[asm_step_arith_none] >> simp[] >>
  reverse (Cases_on `asm_step_compare name (s with as_stack := top)`)
  >- (simp[] >> strip_tac >> gvs[] >> drule asm_step_compare_frame >> simp[]) >>
  `asm_step_compare name (s with as_stack := top ++ rest) = NONE`
    by metis_tac[asm_step_compare_none] >> simp[] >>
  reverse (Cases_on `asm_step_bitwise name (s with as_stack := top)`)
  >- (simp[] >> strip_tac >> gvs[] >> drule asm_step_bitwise_frame >> simp[]) >>
  `asm_step_bitwise name (s with as_stack := top ++ rest) = NONE`
    by metis_tac[asm_step_bitwise_none] >> simp[] >>
  reverse (Cases_on `asm_step_memory name (s with as_stack := top)`)
  >- (simp[] >> strip_tac >> gvs[] >> drule asm_step_memory_frame >> simp[]) >>
  `asm_step_memory name (s with as_stack := top ++ rest) = NONE`
    by metis_tac[asm_step_memory_none] >> simp[] >>
  reverse (Cases_on `asm_step_control o2pc name (s with as_stack := top)`)
  >- (simp[] >> strip_tac >> gvs[] >> drule asm_step_control_frame >> simp[]) >>
  `asm_step_control o2pc name (s with as_stack := top ++ rest) = NONE`
    by metis_tac[asm_step_control_none] >> simp[] >>
  reverse (Cases_on `asm_step_extcall name (s with as_stack := top)`)
  >- (simp[] >> strip_tac >> gvs[] >> drule asm_step_extcall_frame >> simp[]) >>
  `asm_step_extcall name (s with as_stack := top ++ rest) = NONE`
    by metis_tac[asm_step_extcall_none] >> simp[] >>
  reverse (Cases_on `asm_step_copy name (s with as_stack := top)`)
  >- (simp[] >> strip_tac >> gvs[] >> drule asm_step_copy_frame >> simp[]) >>
  `asm_step_copy name (s with as_stack := top ++ rest) = NONE`
    by metis_tac[asm_step_copy_none] >> simp[] >>
  reverse (Cases_on `asm_step_context name (s with as_stack := top)`)
  >- (simp[] >> strip_tac >> gvs[] >> drule asm_step_context_frame >> simp[]) >>
  `asm_step_context name (s with as_stack := top ++ rest) = NONE`
    by metis_tac[asm_step_context_none] >> simp[] >>
  Cases_on `ALOOKUP dup_table name` >> simp[]
  >- (Cases_on `ALOOKUP swap_table name` >> simp[]
      >- (Cases_on `ALOOKUP log_table name` >> simp[] >>
          metis_tac[asm_log_frame]) >> metis_tac[asm_swap_frame]) >>
  metis_tac[asm_dup_frame]
QED

(* ===== Steps and runs ===== *)

(* Every opcode either fails (underflow, bad jump, executed data) or
   consumes a fixed number of entries from the top of the stack and pushes
   its results on what remains.  No opcode reads the stack's length except
   to detect underflow, so success on top is success on top ++ rest. *)
Theorem asm_step_frame:
  !lo o2pc inst s top rest s'.
    asm_step lo o2pc inst (s with as_stack := top) = AsmOK s' ==>
    asm_step lo o2pc inst (s with as_stack := top ++ rest) =
      AsmOK (s' with as_stack := s'.as_stack ++ rest)
Proof
  rpt gen_tac >> Cases_on `inst` >>
  simp[asm_step_def, asm_next_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  metis_tac[asm_step_op_frame]
QED

Theorem asm_steps_frame:
  !n lo o2pc prog s top rest s'.
    asm_steps lo o2pc prog n (s with as_stack := top) = AsmOK s' ==>
    asm_steps lo o2pc prog n (s with as_stack := top ++ rest) =
      AsmOK (s' with as_stack := s'.as_stack ++ rest)
Proof
  Induct >> simp[asm_steps_def] >> rpt gen_tac >>
  simp[AllCaseEqs()] >> strip_tac >> rename1 `asm_step _ _ _ _ = AsmOK s1` >>
  drule_then (qspec_then `rest` assume_tac) asm_step_frame >> simp[] >>
  first_x_assum (qspecl_then [`lo`, `o2pc`, `prog`, `s1`, `s1.as_stack`, `rest`, `s'`] mp_tac) >>
  simp[] >> disch_then irule >>
  `s1 with as_stack := s1.as_stack = s1` by simp[asmSemTheory.asm_state_component_equality] >>
  simp[]
QED
