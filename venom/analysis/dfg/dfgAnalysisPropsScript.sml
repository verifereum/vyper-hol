(*
 * DFG Analysis Correctness (Statements Only)
 *
 * Exported API for consumers of the DFG analysis.
 *
 * 1) Correctness — if dfg_get_def returns an instruction, it comes from
 *    the original instruction list.
 * 2) Finiteness — dfg_def_ids is finite (stated in defs/dfgDefsScript.sml).
 *
 * The well-formedness results (building a DFG preserves well_formed_dfg)
 * live only in proofs/dfgCorrectnessProofScript.sml.
 *)

Theory dfgAnalysisProps
Ancestors
  dfgCorrectnessProof

(* ==========================================================================
   1) Def-source correctness
   ========================================================================== *)

Theorem dfg_build_function_correct:
  !fn v inst.
    dfg_get_def (dfg_build_function fn) v = SOME inst
    ==>
    MEM v inst.inst_outputs /\ MEM inst (fn_insts fn)
Proof
  ACCEPT_TAC dfg_build_function_correct_proof
QED

(* ==========================================================================
   2) Uses correctness
   ========================================================================== *)

(* If dfg_get_uses reports inst as a user of v, then inst is from the
   function and v appears among its operand variables. *)
Theorem dfg_build_function_uses_sound:
  !fn v inst.
    MEM inst (dfg_get_uses (dfg_build_function fn) v) ==>
    MEM inst (fn_insts fn) /\ MEM v (operand_vars inst.inst_operands)
Proof
  ACCEPT_TAC dfg_build_function_uses_sound_proof
QED

(* Every instruction in the function that mentions v as an operand
   variable appears in the uses list for v. *)
Theorem dfg_build_function_uses_complete:
  !fn v inst.
    MEM inst (fn_insts fn) /\
    MEM v (operand_vars inst.inst_operands) ==>
    MEM inst (dfg_get_uses (dfg_build_function fn) v)
Proof
  ACCEPT_TAC dfg_build_function_uses_complete_proof
QED

(* ==========================================================================
   3) Defs completeness
   ========================================================================== *)

(* If any instruction in the function lists v as an output, then
   dfg_get_def returns some defining instruction for v. *)
Theorem dfg_build_function_defs_complete:
  !fn v inst.
    MEM inst (fn_insts fn) /\
    MEM v inst.inst_outputs ==>
    ?inst'. dfg_get_def (dfg_build_function fn) v = SOME inst'
Proof
  ACCEPT_TAC dfg_build_function_defs_complete_proof
QED

(* ==========================================================================
   4) Normalization correctness
   ========================================================================== *)

(* dfg_assigns_sound: every ASSIGN in the DFG is faithfully reflected in
   the runtime state (the output variable holds eval_operand of the operand). *)
Theorem normalize_operand_eval:
  !dfg visited op s.
    dfg_assigns_sound dfg s ==>
    eval_operand (normalize_operand dfg visited op) s = eval_operand op s
Proof
  ACCEPT_TAC normalize_operand_eval_proof
QED

