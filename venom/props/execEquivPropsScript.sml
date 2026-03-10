(*
 * Execution Equivalence Properties (API)
 *
 * Re-exports top-level theorems from execEquivProofs via ACCEPT_TAC.
 *
 * TOP-LEVEL THEOREMS:
 *   - step_inst_result_equiv : Instruction step preserves result_equiv
 *   - run_block_state_equiv  : Block execution preserves state_equiv (OK case)
 *   - run_block_result_equiv : Block execution preserves result_equiv (all cases)
 *)

Theory execEquivProps
Ancestors
  execEquivProofs venomExecSemantics

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
Theorem run_block_state_equiv:
  !fuel ctx vars bb s1 s2 r1.
    state_equiv vars s1 s2 /\
    EVERY (\inst. inst.inst_opcode <> INVOKE) bb.bb_instructions /\
    (!inst. MEM inst bb.bb_instructions ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    run_block fuel ctx bb s1 = OK r1
  ==>
    ?r2. run_block fuel ctx bb s2 = OK r2 /\ state_equiv vars r1 r2
Proof
  ACCEPT_TAC execEquivProofsTheory.run_block_state_equiv
QED

(* Running a block on equivalent states produces equivalent results (all cases) *)
Theorem run_block_result_equiv:
  !fuel ctx vars bb s1 s2.
    state_equiv vars s1 s2 /\
    EVERY (\inst. inst.inst_opcode <> INVOKE) bb.bb_instructions /\
    (!inst. MEM inst bb.bb_instructions ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (run_block fuel ctx bb s1) (run_block fuel ctx bb s2)
Proof
  ACCEPT_TAC execEquivProofsTheory.run_block_result_equiv
QED
