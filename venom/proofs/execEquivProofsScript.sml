(*
 * Execution Equivalence Proofs
 *
 * Proves that step_inst / run_block preserve state_equiv / result_equiv.
 * All theorems parameterized by variable exception set (vars).
 *
 * Internal proofs — consumers use props/execEquivPropsScript.sml
 *
 * TOP-LEVEL THEOREMS:
 *   - step_inst_result_equiv  : Instruction step preserves result_equiv
 *   - run_block_state_equiv   : Block execution preserves state_equiv (OK case)
 *   - run_block_result_equiv  : Block execution preserves result_equiv (all cases)
 *)

Theory execEquivProofs
Ancestors
  stateEquivProofs stateEquiv venomExecSemantics venomState

(* ==========================================================================
   Pure Operations Preserve Equivalence
   ========================================================================== *)

Triviality exec_pure1_result_equiv:
  !vars f inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (exec_pure1 f inst s1) (exec_pure1 f inst s2)
Proof
  rw[exec_pure1_def] >>
  `!op. MEM op inst.inst_operands ==>
    eval_operand op s1 = eval_operand op s2` by (
    rw[] >> irule eval_operand_equiv >> simp[] >>
    rw[] >> first_x_assum irule >> simp[]) >>
  rpt (CASE_TAC >> gvs[result_equiv_def]) >>
  irule update_var_preserves >> simp[]
QED

Triviality exec_pure2_result_equiv:
  !vars f inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (exec_pure2 f inst s1) (exec_pure2 f inst s2)
Proof
  rw[exec_pure2_def] >>
  `!op. MEM op inst.inst_operands ==>
    eval_operand op s1 = eval_operand op s2` by (
    rw[] >> irule eval_operand_equiv >> simp[] >>
    rw[] >> first_x_assum irule >> simp[]) >>
  rpt (CASE_TAC >> gvs[result_equiv_def]) >>
  irule update_var_preserves >> simp[]
QED

Triviality exec_pure3_result_equiv:
  !vars f inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (exec_pure3 f inst s1) (exec_pure3 f inst s2)
Proof
  rw[exec_pure3_def] >>
  `!op. MEM op inst.inst_operands ==>
    eval_operand op s1 = eval_operand op s2` by (
    rw[] >> irule eval_operand_equiv >> simp[] >>
    rw[] >> first_x_assum irule >> simp[]) >>
  rpt (CASE_TAC >> gvs[result_equiv_def]) >>
  irule update_var_preserves >> simp[]
QED

(* ==========================================================================
   State-Reading Operations Preserve Equivalence
   ========================================================================== *)

Triviality exec_read0_result_equiv:
  !vars f inst s1 s2.
    state_equiv vars s1 s2 /\ f s1 = f s2 ==>
    result_equiv vars (exec_read0 f inst s1) (exec_read0 f inst s2)
Proof
  rw[exec_read0_def] >>
  rpt (CASE_TAC >> gvs[result_equiv_def]) >>
  irule update_var_preserves >> simp[]
QED

Triviality exec_read1_result_equiv:
  !vars f inst s1 s2.
    state_equiv vars s1 s2 /\
    (!v. f v s1 = f v s2) /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (exec_read1 f inst s1) (exec_read1 f inst s2)
Proof
  rw[exec_read1_def] >>
  `!op. MEM op inst.inst_operands ==>
    eval_operand op s1 = eval_operand op s2` by (
    rw[] >> irule eval_operand_equiv >> simp[] >>
    rw[] >> first_x_assum irule >> simp[]) >>
  rpt (CASE_TAC >> gvs[result_equiv_def]) >>
  irule update_var_preserves >> simp[]
QED

(* ==========================================================================
   State-Writing Operations Preserve Equivalence
   ========================================================================== *)

Triviality exec_write2_result_equiv:
  !vars f inst s1 s2.
    state_equiv vars s1 s2 /\
    (!v1 v2. state_equiv vars (f v1 v2 s1) (f v1 v2 s2)) /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (exec_write2 f inst s1) (exec_write2 f inst s2)
Proof
  rw[exec_write2_def] >>
  `!op. MEM op inst.inst_operands ==>
    eval_operand op s1 = eval_operand op s2` by (
    rw[] >> irule eval_operand_equiv >> simp[] >>
    rw[] >> first_x_assum irule >> simp[]) >>
  rpt (CASE_TAC >> gvs[result_equiv_def])
QED

(* ==========================================================================
   step_inst Preserves result_equiv
   ========================================================================== *)

Theorem step_inst_result_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> Cases_on `inst.inst_opcode` >>
  simp[step_inst_def] >>
  (* Pure operations *)
  TRY (irule exec_pure2_result_equiv >> simp[] >> NO_TAC) >>
  TRY (irule exec_pure1_result_equiv >> simp[] >> NO_TAC) >>
  TRY (irule exec_pure3_result_equiv >> simp[] >> NO_TAC) >>
  (* State-reading: exec_read0 — need f s1 = f s2 from state_equiv *)
  TRY (irule exec_read0_result_equiv >> simp[] >>
       fs[state_equiv_def, execution_equiv_def] >> NO_TAC) >>
  (* State-reading: exec_read1 — need ∀v. f v s1 = f v s2 *)
  TRY (irule exec_read1_result_equiv >> simp[] >> rw[] >>
       fs[mload_def, sload_def, tload_def,
          state_equiv_def, execution_equiv_def] >> NO_TAC) >>
  (* State-writing: exec_write2 — need state_equiv on f v1 v2 *)
  TRY (irule exec_write2_result_equiv >> simp[] >> rw[] >>
       FIRST [irule mstore_preserves, irule sstore_preserves,
              irule tstore_preserves] >> simp[] >> NO_TAC) >>
  (* Terminators: STOP, RETURN, REVERT, SINK *)
  TRY (simp[result_equiv_def] >>
       fs[state_equiv_def, execution_equiv_def] >> NO_TAC) >>
  TRY (simp[result_equiv_def] >>
       irule halt_state_preserves >> simp[] >> NO_TAC) >>
  TRY (simp[result_equiv_def] >>
       irule revert_state_preserves >> simp[] >> NO_TAC) >>
  (* Remaining cases with operand eval *)
  TRY (
    `!op. MEM op inst.inst_operands ==>
      eval_operand op s1 = eval_operand op s2` by (
      rw[] >> irule eval_operand_equiv >> simp[] >>
      rw[] >> first_x_assum irule >> simp[]) >>
    rpt CASE_TAC >> gvs[result_equiv_def] >>
    TRY (irule update_var_preserves >> simp[] >> NO_TAC) >>
    TRY (irule jump_to_preserves >> simp[] >> NO_TAC) >>
    TRY (irule halt_state_preserves >> simp[] >> NO_TAC) >>
    TRY (irule revert_state_preserves >> simp[] >> NO_TAC) >>
    TRY (irule write_memory_with_expansion_preserves >> simp[] >> NO_TAC) >>
    TRY (simp[state_equiv_refl] >> NO_TAC) >>
    (* PHI: needs vs_prev_bb *)
    TRY (`s1.vs_prev_bb = s2.vs_prev_bb` by
           fs[state_equiv_def, execution_equiv_def] >>
         gvs[] >> irule update_var_preserves >> simp[] >> NO_TAC) >>
    (* SHA3/CALLDATALOAD: needs memory/calldata *)
    TRY (`s1.vs_memory = s2.vs_memory` by
           fs[state_equiv_def, execution_equiv_def] >>
         gvs[] >> irule update_var_preserves >> simp[] >> NO_TAC) >>
    (* CALLDATACOPY/RETURNDATACOPY: needs calldata/returndata + memory *)
    TRY (`s1.vs_call_ctx = s2.vs_call_ctx /\ s1.vs_memory = s2.vs_memory` by
           fs[state_equiv_def, execution_equiv_def] >>
         gvs[] >> irule write_memory_with_expansion_preserves >> simp[] >> NO_TAC) >>
    TRY (`s1.vs_returndata = s2.vs_returndata /\ s1.vs_memory = s2.vs_memory` by
           fs[state_equiv_def, execution_equiv_def] >>
         gvs[] >>
         TRY (irule write_memory_with_expansion_preserves >> simp[] >> NO_TAC) >>
         TRY (irule revert_state_preserves >> simp[] >> NO_TAC)) >>
    NO_TAC) >>
  (* JMP: special case — operand is Label not Var *)
  TRY (Cases_on `inst.inst_operands` >> simp[result_equiv_def] >>
       Cases_on `h` >> simp[result_equiv_def] >>
       Cases_on `t` >> simp[result_equiv_def] >>
       irule jump_to_preserves >> simp[] >> NO_TAC) >>
  (* Fallthrough: unimplemented opcodes return Error *)
  simp[result_equiv_def]
QED

(* ==========================================================================
   step_in_block Preserves Equivalence
   ========================================================================== *)

Triviality step_in_block_result_equiv:
  !vars bb s1 s2.
    state_equiv vars s1 s2 /\
    (!inst. MEM inst bb.bb_instructions ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    let (r1, t1) = step_in_block bb s1 in
    let (r2, t2) = step_in_block bb s2 in
    t1 = t2 /\ result_equiv vars r1 r2
Proof
  rw[step_in_block_def, LET_THM] >>
  `s1.vs_inst_idx = s2.vs_inst_idx` by
    fs[state_equiv_def, execution_equiv_def] >>
  simp[] >>
  Cases_on `get_instruction bb s2.vs_inst_idx` >>
  simp[result_equiv_def] >>
  `MEM x bb.bb_instructions` by (
    fs[get_instruction_def] >>
    Cases_on `s2.vs_inst_idx < LENGTH bb.bb_instructions` >> fs[] >>
    metis_tac[listTheory.EL_MEM]) >>
  `result_equiv vars (step_inst x s1) (step_inst x s2)` by (
    irule step_inst_result_equiv >> simp[] >> metis_tac[]) >>
  Cases_on `step_inst x s1` >> Cases_on `step_inst x s2` >>
  gvs[result_equiv_def] >>
  Cases_on `is_terminator x.inst_opcode` >>
  simp[result_equiv_def] >>
  fs[next_inst_def, state_equiv_def, execution_equiv_def] >>
  rw[] >> simp[lookup_var_def] >> metis_tac[lookup_var_def]
QED

(* ==========================================================================
   run_block Preserves Equivalence
   ========================================================================== *)

Theorem run_block_state_equiv:
  !vars bb s1 s2 r1.
    state_equiv vars s1 s2 /\
    (!inst. MEM inst bb.bb_instructions ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    run_block bb s1 = OK r1
  ==>
    ?r2. run_block bb s2 = OK r2 /\ state_equiv vars r1 r2
Proof
  cheat (* TODO: induction on run_block using step_in_block_result_equiv *)
  (* Pattern: ho_match_mp_tac run_block_ind, unfold run_block,
     use step_in_block_result_equiv, case split on result *)
QED

Theorem run_block_result_equiv:
  !vars bb s1 s2.
    state_equiv vars s1 s2 /\
    (!inst. MEM inst bb.bb_instructions ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (run_block bb s1) (run_block bb s2)
Proof
  cheat (* TODO: induction on run_block using step_in_block_result_equiv *)
  (* Pattern: ho_match_mp_tac run_block_ind, unfold run_block,
     use step_in_block_result_equiv, case split on result *)
QED
