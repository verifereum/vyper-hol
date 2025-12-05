(*
 * State Equivalence Infrastructure
 *
 * This theory defines state equivalence and proves that semantic operations
 * preserve it. This is reusable infrastructure for proving correctness of
 * optimization passes that transform instructions but preserve behavior.
 *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory stringTheory optionTheory pairTheory;
open pred_setTheory finite_mapTheory;
open vfmTypesTheory;
open venomStateTheory venomInstTheory venomSemTheory;

val _ = new_theory "venomEquiv";

(* --------------------------------------------------------------------------
   State Equivalence Definition
   -------------------------------------------------------------------------- *)

(* Variable equivalence: same values for all variables *)
Definition var_equiv_def:
  var_equiv s1 s2 <=>
    !v. lookup_var v s1 = lookup_var v s2
End

(* Full state equivalence *)
Definition state_equiv_def:
  state_equiv s1 s2 <=>
    var_equiv s1 s2 /\
    s1.vs_memory = s2.vs_memory /\
    s1.vs_storage = s2.vs_storage /\
    s1.vs_transient = s2.vs_transient /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    s1.vs_halted = s2.vs_halted /\
    s1.vs_reverted = s2.vs_reverted
End

(* --------------------------------------------------------------------------
   Equivalence Relation Properties
   -------------------------------------------------------------------------- *)

Theorem state_equiv_refl:
  !s. state_equiv s s
Proof
  rw[state_equiv_def, var_equiv_def]
QED

Theorem state_equiv_sym:
  !s1 s2. state_equiv s1 s2 ==> state_equiv s2 s1
Proof
  rw[state_equiv_def, var_equiv_def]
QED

Theorem state_equiv_trans:
  !s1 s2 s3. state_equiv s1 s2 /\ state_equiv s2 s3 ==> state_equiv s1 s3
Proof
  rw[state_equiv_def, var_equiv_def]
QED

(* --------------------------------------------------------------------------
   Result Equivalence
   -------------------------------------------------------------------------- *)

Definition result_equiv_def:
  result_equiv (OK s1) (OK s2) = state_equiv s1 s2 /\
  result_equiv (Halt s1) (Halt s2) = state_equiv s1 s2 /\
  result_equiv (Revert s1) (Revert s2) = state_equiv s1 s2 /\
  result_equiv (Error e1) (Error e2) = (e1 = e2) /\
  result_equiv _ _ = F
End

Theorem result_equiv_refl:
  !r. result_equiv r r
Proof
  Cases >> rw[result_equiv_def, state_equiv_refl]
QED

(* --------------------------------------------------------------------------
   Operand Evaluation Preserves Equivalence
   -------------------------------------------------------------------------- *)

Theorem eval_operand_state_equiv:
  !op s1 s2.
    state_equiv s1 s2 ==>
    eval_operand op s1 = eval_operand op s2
Proof
  Cases_on `op` >>
  rw[eval_operand_def, state_equiv_def, var_equiv_def]
QED

(* --------------------------------------------------------------------------
   State Mutation Operations Preserve Equivalence
   -------------------------------------------------------------------------- *)

Theorem update_var_state_equiv:
  !x v s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (update_var x v s1) (update_var x v s2)
Proof
  rw[state_equiv_def, var_equiv_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem mload_state_equiv:
  !offset s1 s2.
    state_equiv s1 s2 ==>
    mload offset s1 = mload offset s2
Proof
  rw[mload_def, state_equiv_def]
QED

Theorem mstore_state_equiv:
  !offset v s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (mstore offset v s1) (mstore offset v s2)
Proof
  rw[state_equiv_def, var_equiv_def, mstore_def, lookup_var_def]
QED

Theorem sload_state_equiv:
  !key s1 s2.
    state_equiv s1 s2 ==>
    sload key s1 = sload key s2
Proof
  rw[sload_def, state_equiv_def]
QED

Theorem sstore_state_equiv:
  !key v s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (sstore key v s1) (sstore key v s2)
Proof
  rw[state_equiv_def, var_equiv_def, sstore_def, lookup_var_def]
QED

Theorem tload_state_equiv:
  !key s1 s2.
    state_equiv s1 s2 ==>
    tload key s1 = tload key s2
Proof
  rw[tload_def, state_equiv_def]
QED

Theorem tstore_state_equiv:
  !key v s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (tstore key v s1) (tstore key v s2)
Proof
  rw[state_equiv_def, var_equiv_def, tstore_def, lookup_var_def]
QED

Theorem jump_to_state_equiv:
  !lbl s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (jump_to lbl s1) (jump_to lbl s2)
Proof
  rw[state_equiv_def, var_equiv_def, jump_to_def, lookup_var_def]
QED

Theorem halt_state_state_equiv:
  !s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (halt_state s1) (halt_state s2)
Proof
  rw[state_equiv_def, var_equiv_def, halt_state_def, lookup_var_def]
QED

Theorem revert_state_state_equiv:
  !s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (revert_state s1) (revert_state s2)
Proof
  rw[state_equiv_def, var_equiv_def, revert_state_def, lookup_var_def]
QED

(* --------------------------------------------------------------------------
   Binary/Unary/Mod Operations Preserve Equivalence
   -------------------------------------------------------------------------- *)

Theorem exec_binop_state_equiv:
  !f inst s1 s2 r1.
    state_equiv s1 s2 /\
    exec_binop f inst s1 = OK r1
  ==>
    ?r2. exec_binop f inst s2 = OK r2 /\ state_equiv r1 r2
Proof
  rw[exec_binop_def] >>
  Cases_on `inst.inst_operands` >> fs[] >>
  Cases_on `t` >> fs[] >>
  Cases_on `t'` >> fs[] >>
  Cases_on `eval_operand h s1` >> fs[] >>
  Cases_on `eval_operand h' s1` >> fs[] >>
  Cases_on `inst.inst_output` >> fs[] >>
  `eval_operand h s2 = eval_operand h s1` by metis_tac[eval_operand_state_equiv] >>
  `eval_operand h' s2 = eval_operand h' s1` by metis_tac[eval_operand_state_equiv] >>
  fs[] >> metis_tac[update_var_state_equiv]
QED

Theorem exec_unop_state_equiv:
  !f inst s1 s2 r1.
    state_equiv s1 s2 /\
    exec_unop f inst s1 = OK r1
  ==>
    ?r2. exec_unop f inst s2 = OK r2 /\ state_equiv r1 r2
Proof
  rw[exec_unop_def] >>
  Cases_on `inst.inst_operands` >> fs[] >>
  Cases_on `t` >> fs[] >>
  Cases_on `eval_operand h s1` >> fs[] >>
  Cases_on `inst.inst_output` >> fs[] >>
  `eval_operand h s2 = eval_operand h s1` by metis_tac[eval_operand_state_equiv] >>
  fs[] >> metis_tac[update_var_state_equiv]
QED

Theorem exec_modop_state_equiv:
  !f inst s1 s2 r1.
    state_equiv s1 s2 /\
    exec_modop f inst s1 = OK r1
  ==>
    ?r2. exec_modop f inst s2 = OK r2 /\ state_equiv r1 r2
Proof
  rw[exec_modop_def] >>
  gvs[AllCaseEqs()] >>
  metis_tac[eval_operand_state_equiv, update_var_state_equiv]
QED

(* --------------------------------------------------------------------------
   Instruction Stepping Preserves Equivalence
   -------------------------------------------------------------------------- *)

Theorem step_inst_state_equiv:
  !inst s1 s2 r1.
    state_equiv s1 s2 /\
    step_inst inst s1 = OK r1
  ==>
    ?r2. step_inst inst s2 = OK r2 /\ state_equiv r1 r2
Proof
  rpt strip_tac >>
  fs[step_inst_def] >>
  Cases_on `inst.inst_opcode` >> fs[] >>
  FIRST [
    drule_all exec_binop_state_equiv >> simp[],
    drule_all exec_modop_state_equiv >> simp[],
    drule_all exec_unop_state_equiv >> simp[],
    gvs[AllCaseEqs()] >>
    metis_tac[eval_operand_state_equiv, update_var_state_equiv,
              mload_state_equiv, mstore_state_equiv,
              sload_state_equiv, sstore_state_equiv,
              tload_state_equiv, tstore_state_equiv,
              jump_to_state_equiv, state_equiv_refl, state_equiv_def]
  ]
QED

(* --------------------------------------------------------------------------
   Block Stepping Preserves Equivalence
   -------------------------------------------------------------------------- *)

Theorem step_in_block_state_equiv:
  !fn bb s1 s2 r1 is_term.
    state_equiv s1 s2 /\
    step_in_block fn bb s1 = (OK r1, is_term)
  ==>
    ?r2. step_in_block fn bb s2 = (OK r2, is_term) /\ state_equiv r1 r2
Proof
  rw[step_in_block_def] >>
  fs[state_equiv_def] >> fs[] >>
  Cases_on `get_instruction bb s1.vs_inst_idx` >> fs[] >>
  Cases_on `step_inst x s1` >> fs[] >>
  `state_equiv s1 s2` by fs[state_equiv_def] >>
  drule_all step_inst_state_equiv >> strip_tac >>
  Cases_on `is_terminator x.inst_opcode` >> fs[state_equiv_def] >>
  gvs[next_inst_def, var_equiv_def, lookup_var_def]
QED

(* --------------------------------------------------------------------------
   Block Execution Preserves Equivalence
   -------------------------------------------------------------------------- *)

Theorem run_block_state_equiv:
  !fn bb s1 s2 r1.
    state_equiv s1 s2 /\
    run_block fn bb s1 = OK r1
  ==>
    ?r2. run_block fn bb s2 = OK r2 /\ state_equiv r1 r2
Proof
  ho_match_mp_tac run_block_ind >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `run_block _ _ _ = _` mp_tac >>
  simp[Once run_block_def] >>
  Cases_on `step_in_block fn bb s1` >>
  Cases_on `q` >> simp[] >>
  strip_tac >>
  drule_all step_in_block_state_equiv >>
  strip_tac >>
  simp[Once run_block_def] >>
  `(v.vs_halted <=> r2.vs_halted)` by fs[state_equiv_def] >>
  Cases_on `v.vs_halted` >> fs[] >>
  Cases_on `r` >> fs[] >-
    (gvs[] >> simp[Once run_block_def] >> metis_tac[]) >>
  simp[Once run_block_def]
QED

val _ = export_theory();
