(*
 * DFG Analysis Correctness (Statements Only)
 *
 * Exported API for consumers of the DFG analysis.
 *
 * 1) Well-formedness — building a DFG preserves well_formed_dfg.
 * 2) Correctness — if dfg_get_def returns an instruction, it comes from
 *    the original instruction list.
 * 3) Finiteness — dfg_def_ids is finite.
 *
 * Internal proof machinery lives in proofs/dfgCorrectnessProofScript.sml.
 * Re-exported via ACCEPT_TAC.
 *)

Theory dfgAnalysisProps
Ancestors
  dfgCorrectnessProof

(* ==========================================================================
   1) Well-formedness preservation
   ========================================================================== *)

Theorem well_formed_dfg_update:
  !dfg inst v.
    well_formed_dfg dfg /\ MEM v inst.inst_outputs
    ==> well_formed_dfg (dfg with dfg_defs := dfg.dfg_defs |+ (v, inst))
Proof
  ACCEPT_TAC well_formed_dfg_update_proof
QED

Theorem dfg_add_defs_well_formed:
  !dfg vs inst.
    well_formed_dfg dfg /\ EVERY (\v. MEM v inst.inst_outputs) vs
    ==> well_formed_dfg (dfg_add_defs dfg vs inst)
Proof
  ACCEPT_TAC dfg_add_defs_well_formed_proof
QED

Theorem dfg_add_use_get_def:
  !dfg v inst u.
    dfg_get_def (dfg_add_use dfg u inst) v = dfg_get_def dfg v
Proof
  ACCEPT_TAC dfg_add_use_get_def_proof
QED

Theorem dfg_add_uses_get_def:
  !dfg vs inst v.
    dfg_get_def (dfg_add_uses dfg vs inst) v = dfg_get_def dfg v
Proof
  ACCEPT_TAC dfg_add_uses_get_def_proof
QED

Theorem dfg_add_uses_preserve_wf:
  !dfg vs inst.
    well_formed_dfg dfg ==> well_formed_dfg (dfg_add_uses dfg vs inst)
Proof
  ACCEPT_TAC dfg_add_uses_preserve_wf_proof
QED

Theorem well_formed_dfg_update_ids:
  !dfg ids. well_formed_dfg dfg ==> well_formed_dfg (dfg with dfg_ids := ids)
Proof
  ACCEPT_TAC well_formed_dfg_update_ids_proof
QED

Theorem dfg_add_inst_well_formed:
  !dfg inst.
    well_formed_dfg dfg ==> well_formed_dfg (dfg_add_inst dfg inst)
Proof
  ACCEPT_TAC dfg_add_inst_well_formed_proof
QED

Theorem dfg_build_insts_rev_well_formed:
  !dfg insts.
    well_formed_dfg dfg ==> well_formed_dfg (dfg_build_insts_rev dfg insts)
Proof
  ACCEPT_TAC dfg_build_insts_rev_well_formed_proof
QED

Theorem dfg_build_insts_well_formed:
  !insts. well_formed_dfg (dfg_build_insts insts)
Proof
  ACCEPT_TAC dfg_build_insts_well_formed_proof
QED

Theorem dfg_build_function_well_formed:
  !fn. well_formed_dfg (dfg_build_function fn)
Proof
  ACCEPT_TAC dfg_build_function_well_formed_proof
QED

(* ==========================================================================
   2) Def-source correctness
   ========================================================================== *)

Theorem dfg_add_defs_lookup:
  !dfg vs inst v inst'.
    dfg_get_def (dfg_add_defs dfg vs inst) v = SOME inst' ==>
    dfg_get_def dfg v = SOME inst' \/ (inst' = inst /\ MEM v vs)
Proof
  ACCEPT_TAC dfg_add_defs_lookup_proof
QED

Theorem dfg_add_inst_get_def:
  !dfg inst0 v.
    dfg_get_def (dfg_add_inst dfg inst0) v =
    dfg_get_def
      (dfg_add_defs
         (dfg_add_uses dfg (operand_vars inst0.inst_operands) inst0)
         inst0.inst_outputs inst0) v
Proof
  ACCEPT_TAC dfg_add_inst_get_def_proof
QED

Theorem dfg_add_inst_lookup:
  !dfg inst0 v inst.
    dfg_get_def (dfg_add_inst dfg inst0) v = SOME inst ==>
    dfg_get_def dfg v = SOME inst \/ (inst = inst0 /\ MEM v inst0.inst_outputs)
Proof
  ACCEPT_TAC dfg_add_inst_lookup_proof
QED

Theorem dfg_build_insts_rev_correct:
  !insts dfg v inst.
    dfg_get_def (dfg_build_insts_rev dfg insts) v = SOME inst ==>
    dfg_get_def dfg v = SOME inst \/
    (MEM inst insts /\ MEM v inst.inst_outputs)
Proof
  ACCEPT_TAC dfg_build_insts_rev_correct_proof
QED

Theorem dfg_build_insts_correct:
  !insts v inst.
    dfg_get_def (dfg_build_insts insts) v = SOME inst ==>
    MEM inst insts /\ MEM v inst.inst_outputs
Proof
  ACCEPT_TAC dfg_build_insts_correct_proof
QED

Theorem dfg_build_function_correct:
  !fn v inst.
    dfg_get_def (dfg_build_function fn) v = SOME inst
    ==>
    MEM v inst.inst_outputs /\ MEM inst (fn_insts fn)
Proof
  ACCEPT_TAC dfg_build_function_correct_proof
QED

(* ==========================================================================
   3) Finiteness / termination helpers
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
   4) Uses correctness
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
   5) Defs completeness
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
   6) ID map correctness
   ========================================================================== *)

(* If dfg_get_inst_by_id returns an instruction, it is from the function. *)
Theorem dfg_build_function_ids_sound:
  !fn id inst.
    dfg_get_inst_by_id (dfg_build_function fn) id = SOME inst ==>
    MEM inst (fn_insts fn)
Proof
  ACCEPT_TAC dfg_build_function_ids_sound_proof
QED

(* Every instruction in the function is retrievable by its ID. *)
Theorem dfg_build_function_ids_complete:
  !fn inst.
    MEM inst (fn_insts fn) ==>
    ?inst'. dfg_get_inst_by_id (dfg_build_function fn) inst.inst_id = SOME inst'
Proof
  ACCEPT_TAC dfg_build_function_ids_complete_proof
QED

(* ==========================================================================
   7) Normalization correctness
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

(* Restricted version: only requires ASSIGN equalities for variables NOT
   in the visited set.  Enables use at program points where
   dfg_assigns_sound may not hold globally. *)
Theorem normalize_operand_eval_restricted:
  !dfg visited op s.
    (!v inst. ~MEM v visited ==>
       FLOOKUP dfg.dfg_defs v = SOME inst /\
       inst.inst_opcode = ASSIGN ==>
       case inst.inst_operands of
         [op'] => lookup_var v s = eval_operand op' s
       | _ => T) ==>
    eval_operand (normalize_operand dfg visited op) s = eval_operand op s
Proof
  ACCEPT_TAC normalize_operand_eval_restricted_proof
QED

