(*
 * SSA Construction Block-Level: Instruction Result Equivalence (Core)
 *
 * TOP-LEVEL:
 *   - exec_binop_result_ssa_equiv
 *   - exec_unop_result_ssa_equiv
 *   - exec_modop_result_ssa_equiv
 *   - single_output_result_ssa_equiv
 *
 * Helpers:
 *   - ssa_result_equiv_error
 *   - option_pair_case, option_triple_case, case_list_singleton
 *   - inst_ssa_compatible_outputs_equiv
 *)

Theory ssaBlockResultCore
Ancestors
  ssaBlockCompat ssaStateEquiv venomSem

(* ==========================================================================
   Instruction Result Equivalence with Same VM
   ========================================================================== *)

(* Helper: exec_binop gives ssa_result_equiv with SAME vm.
 * The output variable is determined by vm via inst_ssa_compatible pattern.
 * Requires LENGTH inst.inst_outputs <= 1 (Venom instructions have at most 1 output). *)
Theorem exec_binop_result_ssa_equiv:
  !f inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    LENGTH inst.inst_outputs <= 1 /\
    (case inst.inst_outputs of
       [] => inst_ssa.inst_outputs = []
     | [out] =>
         let ssa_out = case FLOOKUP vm out of SOME x => x | NONE => out in
         inst_ssa.inst_outputs = [ssa_out] /\
         (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
         (FLOOKUP vm ssa_out = NONE ==>
          FLOOKUP vm out = NONE \/ FLOOKUP vm out = SOME out)
     | _ => T) ==>
    ssa_result_equiv vm (exec_binop f inst s_orig) (exec_binop f inst_ssa s_ssa)
Proof
  rw[exec_binop_def] >>
  (* Case split on operands *)
  Cases_on `inst.inst_operands` >> fs[ssa_result_equiv_def] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >>
  Cases_on `t'` >> fs[ssa_result_equiv_def] >>
  (* Now have exactly 2 operands *)
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  `eval_operand h' s_orig = eval_operand (ssa_operand vm h') s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  gvs[] >>
  (* Case split on operand evaluation *)
  Cases_on `eval_operand (ssa_operand vm h) s_ssa` >> gvs[ssa_result_equiv_def] >>
  Cases_on `eval_operand (ssa_operand vm h') s_ssa` >> gvs[ssa_result_equiv_def] >>
  (* Case split on outputs - LENGTH <= 1 means [] or [out] only *)
  Cases_on `inst.inst_outputs` >> gvs[ssa_result_equiv_def] >>
  Cases_on `t` >> gvs[ssa_result_equiv_def] >>
  (* Single output case - use ssa_state_equiv_update_same_vm *)
  irule ssa_state_equiv_update_same_vm >> gvs[]
QED

(* Helper: exec_unop gives ssa_result_equiv with SAME vm.
 * Requires LENGTH inst.inst_outputs <= 1 (Venom instructions have at most 1 output). *)
Theorem exec_unop_result_ssa_equiv:
  !f inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    LENGTH inst.inst_outputs <= 1 /\
    (case inst.inst_outputs of
       [] => inst_ssa.inst_outputs = []
     | [out] =>
         let ssa_out = case FLOOKUP vm out of SOME x => x | NONE => out in
         inst_ssa.inst_outputs = [ssa_out] /\
         (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
         (FLOOKUP vm ssa_out = NONE ==>
          FLOOKUP vm out = NONE \/ FLOOKUP vm out = SOME out)
     | _ => T) ==>
    ssa_result_equiv vm (exec_unop f inst s_orig) (exec_unop f inst_ssa s_ssa)
Proof
  rw[exec_unop_def] >>
  Cases_on `inst.inst_operands` >> fs[ssa_result_equiv_def] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >>
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  gvs[] >>
  Cases_on `eval_operand (ssa_operand vm h) s_ssa` >> gvs[ssa_result_equiv_def] >>
  (* Case split on outputs - LENGTH <= 1 means [] or [out] only *)
  Cases_on `inst.inst_outputs` >> gvs[ssa_result_equiv_def] >>
  Cases_on `t` >> gvs[ssa_result_equiv_def] >>
  irule ssa_state_equiv_update_same_vm >> gvs[]
QED

(* Helper: exec_modop gives ssa_result_equiv with SAME vm.
 * Requires LENGTH inst.inst_outputs <= 1 (Venom instructions have at most 1 output). *)
Theorem exec_modop_result_ssa_equiv:
  !f inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    LENGTH inst.inst_outputs <= 1 /\
    (case inst.inst_outputs of
       [] => inst_ssa.inst_outputs = []
     | [out] =>
         let ssa_out = case FLOOKUP vm out of SOME x => x | NONE => out in
         inst_ssa.inst_outputs = [ssa_out] /\
         (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
         (FLOOKUP vm ssa_out = NONE ==>
          FLOOKUP vm out = NONE \/ FLOOKUP vm out = SOME out)
     | _ => T) ==>
    ssa_result_equiv vm (exec_modop f inst s_orig) (exec_modop f inst_ssa s_ssa)
Proof
  rw[exec_modop_def] >>
  Cases_on `inst.inst_operands` >> fs[ssa_result_equiv_def] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >>
  Cases_on `t'` >> fs[ssa_result_equiv_def] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >>
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  `eval_operand h' s_orig = eval_operand (ssa_operand vm h') s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  `eval_operand h'' s_orig = eval_operand (ssa_operand vm h'') s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  gvs[] >>
  Cases_on `eval_operand (ssa_operand vm h) s_ssa` >> gvs[ssa_result_equiv_def] >>
  Cases_on `eval_operand (ssa_operand vm h') s_ssa` >> gvs[ssa_result_equiv_def] >>
  Cases_on `eval_operand (ssa_operand vm h'') s_ssa` >> gvs[ssa_result_equiv_def] >>
  (* Case split on outputs - LENGTH <= 1 means [] or [out] only *)
  Cases_on `inst.inst_outputs` >> gvs[ssa_result_equiv_def] >>
  Cases_on `t` >> gvs[ssa_result_equiv_def] >>
  irule ssa_state_equiv_update_same_vm >> gvs[]
QED

(* Helper: ssa_result_equiv for Error cases (trivially true) *)
Theorem ssa_result_equiv_error:
  !vm e1 e2. ssa_result_equiv vm (Error e1) (Error e2)
Proof
  rw[ssa_result_equiv_def]
QED

(* Helper: expand option-pair case to nested cases. *)
Theorem option_pair_case:
  !x y e f.
    (case (x,y) of (SOME a, SOME b) => f a b | _ => e) =
    (case x of NONE => e | SOME a => case y of NONE => e | SOME b => f a b)
Proof
  Cases_on `x` >> Cases_on `y` >> simp[]
QED

(* Helper: expand option-triple case to nested cases. *)
Theorem option_triple_case:
  !x y z e f.
    (case (x,y,z) of
       (NONE,v3) => e
     | (SOME a,NONE,v9) => e
     | (SOME a,SOME b,NONE) => e
     | (SOME a,SOME b,SOME c) => f a b c) =
    (case x of
       NONE => e
     | SOME a =>
         case y of
           NONE => e
         | SOME b =>
             case z of
               NONE => e
             | SOME c => f a b c)
Proof
  Cases_on `x` >> Cases_on `y` >> Cases_on `z` >> simp[]
QED

(* Helper: collapse []/singleton/longer list cases into singleton/default. *)
Theorem case_list_singleton:
  !xs e f.
    (case xs of [] => e | [x] => f x | x::y::zs => e) =
    (case xs of [x] => f x | _ => e)
Proof
  Cases_on `xs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[]
QED

(* Helper: finishing tactic for output preconditions.
   When goal has form:
   case inst.inst_outputs of [] => ... | [out] => ... /\ cond | ... => T
   and assumption 3 has the compatible form, need to case split *)
Theorem inst_ssa_compatible_outputs_equiv:
  !vm inst inst_ssa out.
    inst_ssa_compatible vm inst inst_ssa /\ inst.inst_outputs = [out] ==>
    inst_ssa.inst_outputs = [case FLOOKUP vm out of NONE => out | SOME x => x] /\
    (!v. v <> out ==> FLOOKUP vm v <> SOME (case FLOOKUP vm out of NONE => out | SOME x => x)) /\
    (FLOOKUP vm (case FLOOKUP vm out of NONE => out | SOME x => x) = NONE ==>
     FLOOKUP vm out = NONE \/ FLOOKUP vm out = SOME out)
Proof
  rw[inst_ssa_compatible_def] >>
  Cases_on `FLOOKUP vm out` >> gvs[]
QED

(* Helper: inst_ssa_compatible yields output compatibility when LENGTH <= 1. *)
Theorem inst_ssa_compatible_outputs_ok:
  !vm inst inst_ssa.
    inst_ssa_compatible vm inst inst_ssa /\
    LENGTH inst.inst_outputs <= 1 ==>
    (case inst.inst_outputs of
       [] => inst_ssa.inst_outputs = []
     | [out] =>
         let ssa_out = case FLOOKUP vm out of SOME x => x | NONE => out in
         inst_ssa.inst_outputs = [ssa_out] /\
         (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
         (FLOOKUP vm ssa_out = NONE ==>
          FLOOKUP vm out = NONE \/ FLOOKUP vm out = SOME out)
     | _ => T)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_outputs` >| [
    fs[inst_ssa_compatible_def],
    (Cases_on `t` >| [
       (drule_all inst_ssa_compatible_outputs_equiv >> strip_tac >> gvs[]),
       gvs[]
     ])
  ]
QED

(* Helper: Single-output update with a known value preserves ssa_result_equiv. *)
Theorem single_output_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm val_orig val_ssa err.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa_compatible vm inst inst_ssa /\
    LENGTH inst.inst_outputs <= 1 /\
    val_orig = val_ssa ==>
    ssa_result_equiv vm
      (case inst.inst_outputs of
         [out] => OK (update_var out val_orig s_orig)
       | _ => Error err)
      (case inst_ssa.inst_outputs of
         [out] => OK (update_var out val_ssa s_ssa)
       | _ => Error err)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_outputs` >| [
    (Cases_on `inst_ssa.inst_outputs` >>
     fs[inst_ssa_compatible_def] >>
     gvs[ssa_result_equiv_def]),
    (Cases_on `t` >| [
       (drule_all inst_ssa_compatible_outputs_equiv >> strip_tac >>
        gvs[ssa_result_equiv_def] >>
        irule ssa_state_equiv_update_same_vm >> gvs[]),
       gvs[ssa_result_equiv_def]
     ])
  ]
QED
