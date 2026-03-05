(*
 * Venom Execution Properties (Statements Only)
 *
 * Re-exports theorems from venomExecProofs via ACCEPT_TAC.
 * Proofs live in proofs/venomExecProofsScript.sml.
 *)

Theory venomExecProps
Ancestors
  venomExecProofs

(* ==========================================================================
   bool_to_word Properties
   ========================================================================== *)

(* bool_to_word T = 1w *)
Theorem bool_to_word_T:
  bool_to_word T = 1w
Proof
  ACCEPT_TAC venomExecProofsTheory.bool_to_word_T
QED

(* bool_to_word F = 0w *)
Theorem bool_to_word_F:
  bool_to_word F = 0w
Proof
  ACCEPT_TAC venomExecProofsTheory.bool_to_word_F
QED

(* ==========================================================================
   Instruction Behavior Lemmas
   ========================================================================== *)

(* ISZERO instruction computes bool_to_word of equality with zero *)
Theorem step_iszero_value:
  !s cond_op out id cond.
    eval_operand cond_op s = SOME cond ==>
    step_inst <| inst_id := id; inst_opcode := ISZERO;
                 inst_operands := [cond_op]; inst_outputs := [out] |> s =
    OK (update_var out (bool_to_word (cond = 0w)) s)
Proof
  ACCEPT_TAC venomExecProofsTheory.step_iszero_value
QED

(* ASSERT reverts on zero, continues on nonzero *)
Theorem step_assert_behavior:
  !s cond_op id cond.
    eval_operand cond_op s = SOME cond ==>
    step_inst <| inst_id := id; inst_opcode := ASSERT;
                 inst_operands := [cond_op]; inst_outputs := [] |> s =
    if cond = 0w then Revert (revert_state s) else OK s
Proof
  ACCEPT_TAC venomExecProofsTheory.step_assert_behavior
QED

(* REVERT instruction always produces Revert result *)
Theorem step_revert_always_reverts:
  !inst s.
    inst.inst_opcode = REVERT ==>
    step_inst inst s = Revert (revert_state s)
Proof
  ACCEPT_TAC venomExecProofsTheory.step_revert_always_reverts
QED

(* JMP instruction jumps to the given label *)
Theorem step_jmp_behavior:
  !s lbl id.
    step_inst <| inst_id := id; inst_opcode := JMP;
                 inst_operands := [Label lbl]; inst_outputs := [] |> s =
    OK (jump_to lbl s)
Proof
  ACCEPT_TAC venomExecProofsTheory.step_jmp_behavior
QED

(* JNZ branches on nonzero condition *)
Theorem step_jnz_behavior:
  !s cond_op if_nonzero if_zero id cond.
    eval_operand cond_op s = SOME cond ==>
    step_inst <| inst_id := id; inst_opcode := JNZ;
                 inst_operands := [cond_op; Label if_nonzero; Label if_zero];
                 inst_outputs := [] |> s =
    if cond <> 0w then OK (jump_to if_nonzero s)
    else OK (jump_to if_zero s)
Proof
  ACCEPT_TAC venomExecProofsTheory.step_jnz_behavior
QED

(* ==========================================================================
   step_in_block / run_block Properties
   ========================================================================== *)

(* Non-terminator step increments instruction index by one *)
Theorem step_in_block_increments_idx:
  !bb s v.
    step_in_block bb s = (OK v, F)
    ==>
    v.vs_inst_idx = SUC s.vs_inst_idx
Proof
  ACCEPT_TAC venomExecProofsTheory.step_in_block_increments_idx
QED

(* Block returning OK means state is not halted *)
Theorem run_block_OK_not_halted:
  !bb s v. run_block bb s = OK v ==> ~v.vs_halted
Proof
  ACCEPT_TAC venomExecProofsTheory.run_block_OK_not_halted
QED

(* Block returning OK resets instruction index to 0 *)
Theorem run_block_OK_inst_idx_0:
  !bb s v. run_block bb s = OK v ==> v.vs_inst_idx = 0
Proof
  ACCEPT_TAC venomExecProofsTheory.run_block_OK_inst_idx_0
QED

(* ==========================================================================
   Lookup Helpers
   ========================================================================== *)

(* Found block is a member of the block list *)
Theorem lookup_block_MEM:
  !lbl bbs bb.
    lookup_block lbl bbs = SOME bb ==> MEM bb bbs
Proof
  ACCEPT_TAC venomExecProofsTheory.lookup_block_MEM
QED

(* Blocks with same instruction prefix produce same step result *)
Theorem step_in_block_prefix_same:
  !bb1 bb2 s n.
    TAKE (SUC n) bb1.bb_instructions = TAKE (SUC n) bb2.bb_instructions /\
    s.vs_inst_idx = n /\
    n < LENGTH bb1.bb_instructions /\
    n < LENGTH bb2.bb_instructions
  ==>
    step_in_block bb1 s = step_in_block bb2 s
Proof
  ACCEPT_TAC venomExecProofsTheory.step_in_block_prefix_same
QED

(* ==========================================================================
   Lookup Function Properties
   ========================================================================== *)

(* Found function is a member of the function list *)
Theorem lookup_function_MEM:
  !name fns fn. lookup_function name fns = SOME fn ==> MEM fn fns
Proof
  ACCEPT_TAC venomInstTheory.lookup_function_MEM
QED
