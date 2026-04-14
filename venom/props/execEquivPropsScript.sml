(*
 * Execution Equivalence Properties (API)
 *
 * Re-exports top-level theorems from execEquivProofs via ACCEPT_TAC.
 *
 * TOP-LEVEL THEOREMS:
 *   - step_inst_result_equiv : Instruction step preserves result_equiv
 *   - exec_block_state_equiv  : Block execution preserves state_equiv (OK case)
 *   - exec_block_result_equiv : Block execution preserves result_equiv (all cases)
 *   - run_function_result_equiv : Function execution preserves result_equiv
 *)

Theory execEquivProps
Ancestors
  execEquivProofs venomExecSemantics venomWf

(* Single instruction step preserves result_equiv modulo fresh variables,
   provided operand variables are not in the exception set.
   step_inst_base version: internal, used by proof infrastructure.
   step_inst version (below): public API for non-INVOKE instructions. *)
Theorem step_inst_base_result_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  ACCEPT_TAC execEquivProofsTheory.step_inst_result_equiv
QED

(* Public API: step_inst preserves result_equiv for non-INVOKE instructions.
   Bridges to step_inst_base_result_equiv via step_inst_non_invoke. *)
Theorem step_inst_result_equiv:
  !fuel ctx vars inst s1 s2.
    state_equiv vars s1 s2 /\
    inst.inst_opcode <> INVOKE /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (step_inst fuel ctx inst s1) (step_inst fuel ctx inst s2)
Proof
  rw[step_inst_non_invoke] >>
  irule step_inst_base_result_equiv >> simp[]
QED

(* Running a block on equivalent states produces equivalent OK results *)
Theorem exec_block_state_equiv:
  !fuel ctx vars bb s1 s2 r1.
    state_equiv vars s1 s2 /\
    EVERY (\inst. inst.inst_opcode <> INVOKE) bb.bb_instructions /\
    (!inst. MEM inst bb.bb_instructions ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    exec_block fuel ctx bb s1 = OK r1
  ==>
    ?r2. exec_block fuel ctx bb s2 = OK r2 /\ state_equiv vars r1 r2
Proof
  ACCEPT_TAC execEquivProofsTheory.exec_block_state_equiv
QED

(* Running a block on equivalent states produces equivalent results (all cases) *)
Theorem exec_block_result_equiv:
  !fuel ctx vars bb s1 s2.
    state_equiv vars s1 s2 /\
    EVERY (\inst. inst.inst_opcode <> INVOKE) bb.bb_instructions /\
    (!inst. MEM inst bb.bb_instructions ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (exec_block fuel ctx bb s1) (exec_block fuel ctx bb s2)
Proof
  ACCEPT_TAC execEquivProofsTheory.exec_block_result_equiv
QED

(* Running a function on equivalent states produces equivalent results,
   provided all blocks have no INVOKE and operand vars outside exception set.
   Used for state-patching: patching non-live vars doesn't affect function execution. *)
Theorem run_function_result_equiv:
  !fuel ctx vars fn s1 s2.
    state_equiv vars s1 s2 /\
    (!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==>
      EVERY (\inst. inst.inst_opcode <> INVOKE) bb.bb_instructions /\
      (!inst x. MEM inst bb.bb_instructions /\
               MEM (Var x) inst.inst_operands ==> x NOTIN vars)) ==>
    result_equiv vars (run_function fuel ctx fn s1) (run_function fuel ctx fn s2)
Proof
  ACCEPT_TAC execEquivProofsTheory.run_function_result_equiv
QED

(* Same as run_function_result_equiv but restricted to a safe set of blocks
   closed under successors. Operand/well-formedness conditions only required
   for blocks in safe. Used when patching is limited to reachable blocks. *)
Theorem run_function_result_equiv_closed:
  !fuel ctx vars fn s1 s2 safe.
    state_equiv vars s1 s2 /\
    (!lbl. fn_entry_label fn = SOME lbl ==> lbl IN safe) /\
    (!lbl bb. lbl IN safe /\ lookup_block lbl fn.fn_blocks = SOME bb ==>
      bb_well_formed bb /\
      EVERY inst_wf bb.bb_instructions /\
      EVERY (\inst. inst.inst_opcode <> INVOKE) bb.bb_instructions /\
      (!inst x. MEM inst bb.bb_instructions /\
               MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
      (!s. MEM s (bb_succs bb) ==> s IN safe)) ==>
    result_equiv vars (run_function fuel ctx fn s1) (run_function fuel ctx fn s2)
Proof
  ACCEPT_TAC execEquivProofsTheory.run_function_result_equiv_closed
QED
