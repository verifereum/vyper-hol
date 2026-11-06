(*
 * DFG Analysis Correctness (Statements Only)
 *
 * Exported API for consumers of the DFG analysis.
 *
 * 1) Correctness — if dfg_get_def returns an instruction, it comes from
 *    the original instruction list.
 * 2) Finiteness — dfg_def_ids is finite.
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
   2) Finiteness / termination helpers
   ========================================================================== *)

Theorem dfg_def_ids_finite:
  !dfg. FINITE (dfg_def_ids dfg)
Proof
  ACCEPT_TAC dfg_def_ids_finite_proof
QED

Theorem dfg_get_def_implies_dfg_def_ids:
  !dfg v inst. dfg_get_def dfg v = SOME inst ==> inst.inst_id IN dfg_def_ids dfg
Proof
  ACCEPT_TAC dfg_get_def_implies_dfg_def_ids_proof
QED

(* ==========================================================================
   3) Uses correctness
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
   4) Defs completeness
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
   5) Normalization correctness
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

