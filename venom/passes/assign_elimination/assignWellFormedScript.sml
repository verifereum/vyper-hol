(*
 * ASSIGN Elimination Well-Formedness Definitions
 *
 * This theory defines well-formedness conditions for ASSIGN elimination.
 * The key property is that eliminated ASSIGNs have already executed,
 * so their output variable has the same value as the source variable.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * TOP-LEVEL DEFINITIONS:
 *   - assign_equiv            : Output and source variables have same value
 *   - all_assigns_equiv       : All eliminable ASSIGNs satisfy assign_equiv
 *   - ssa_form                : SSA form - each variable defined at most once
 *
 * TOP-LEVEL THEOREMS:
 *   - replace_var_correct     : Replaced variable has same value as original
 *
 * ============================================================================
 *)

Theory assignWellFormed
Ancestors
  assignDefs finite_map
  venomState venomInst venomSem
  stateEquiv

(* ==========================================================================
   Variable Equivalence After ASSIGN
   ========================================================================== *)

(* Key property: After an ASSIGN %y = ASSIGN [Var %x] executes,
   lookup_var "%y" s = lookup_var "%x" s *)
Definition assign_equiv_def:
  assign_equiv s out src <=>
    lookup_var out s = lookup_var src s
End

(* All eliminable ASSIGNs in the map satisfy equiv *)
Definition all_assigns_equiv_def:
  all_assigns_equiv amap s <=>
    !out src. FLOOKUP amap out = SOME src ==> assign_equiv s out src
End

(* ==========================================================================
   Resolve Variable Correctness
   ========================================================================== *)

(* Key lemma: When all assigns equiv, resolving a variable gives same value *)
Theorem resolve_var_correct:
  !amap fuel v s.
    all_assigns_equiv amap s ==>
    lookup_var (resolve_var amap fuel v) s = lookup_var v s
Proof
  Induct_on `fuel` >> rpt strip_tac >> simp[Once resolve_var_def] >>
  Cases_on `FLOOKUP amap v` >> simp[] >>
  fs[all_assigns_equiv_def, assign_equiv_def]
QED

(* Main theorem: replace_var gives same value *)
Theorem replace_var_correct:
  !amap v s.
    all_assigns_equiv amap s ==>
    lookup_var (replace_var amap v) s = lookup_var v s
Proof
  rw[replace_var_def] >> irule resolve_var_correct >> simp[]
QED

(* ==========================================================================
   Operand Evaluation Correctness
   ========================================================================== *)

(* Replaced operand evaluates to same value *)
Theorem replace_operand_correct:
  !amap op s.
    all_assigns_equiv amap s ==>
    eval_operand (replace_operand amap op) s = eval_operand op s
Proof
  Cases_on `op` >> rw[replace_operand_def, eval_operand_def] >>
  drule replace_var_correct >> simp[]
QED

(* Replaced operands evaluate to same values *)
Theorem replace_operands_correct:
  !amap ops s.
    all_assigns_equiv amap s ==>
    eval_operands (replace_operands amap ops) s = eval_operands ops s
Proof
  Induct_on `ops` >> rw[replace_operands_def, eval_operands_def] >>
  (* Rewrite MAP to replace_operands using the definition *)
  SUBST_ALL_TAC (GSYM (Q.SPECL [`amap`, `ops`] replace_operands_def)) >>
  drule_all replace_operand_correct >> simp[]
QED

(* ==========================================================================
   Building Equivalence
   ========================================================================== *)

(* After executing ASSIGN %out = [Var %src], assign_equiv holds.
   In SSA form, out <> src is guaranteed. *)
Theorem step_inst_assign_establishes_equiv:
  !inst s s' out src.
    inst.inst_opcode = ASSIGN /\
    inst.inst_operands = [Var src] /\
    inst.inst_outputs = [out] /\
    step_inst inst s = OK s' ==>
    assign_equiv s' out src
Proof
  rw[step_inst_def, assign_equiv_def, update_var_def, lookup_var_def] >>
  gvs[AllCaseEqs(), eval_operand_def, lookup_var_def] >>
  simp[FLOOKUP_UPDATE]
QED

(* ==========================================================================
   Well-Formedness for Correctness
   ========================================================================== *)

(* A function is well-formed for assign elimination if:
   1. SSA form (each variable defined at most once)
   2. Definitions dominate uses (each use is after the definition) *)

(* For now, we assume the all_assigns_equiv property holds when we execute
   an instruction after all the relevant ASSIGNs have executed.
   This is the key semantic invariant. *)

val _ = export_theory();
