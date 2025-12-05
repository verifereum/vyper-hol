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
  result_equiv (Error e1) (Error e2) = T /\  (* Any error equiv to any error *)
  result_equiv _ _ = F
End

Theorem result_equiv_refl:
  !r. result_equiv r r
Proof
  Cases >> rw[result_equiv_def, state_equiv_refl]
QED

(* Specific rewrites for result_equiv *)
Theorem result_equiv_error[simp]:
  result_equiv (Error e) (Error e) = T
Proof
  rw[result_equiv_def]
QED

Theorem result_equiv_ok[simp]:
  result_equiv (OK s1) (OK s2) = state_equiv s1 s2
Proof
  rw[result_equiv_def]
QED

Theorem result_equiv_halt[simp]:
  result_equiv (Halt s1) (Halt s2) = state_equiv s1 s2
Proof
  rw[result_equiv_def]
QED

Theorem result_equiv_revert[simp]:
  result_equiv (Revert s1) (Revert s2) = state_equiv s1 s2
Proof
  rw[result_equiv_def]
QED

Theorem result_equiv_error_any[simp]:
  result_equiv (Error e1) (Error e2) = T
Proof
  rw[result_equiv_def]
QED

(* Mismatch cases are false *)
Theorem result_equiv_ok_halt[simp]:
  result_equiv (OK s) (Halt s') = F
Proof
  rw[result_equiv_def]
QED

Theorem result_equiv_ok_revert[simp]:
  result_equiv (OK s) (Revert s') = F
Proof
  rw[result_equiv_def]
QED

Theorem result_equiv_ok_error[simp]:
  result_equiv (OK s) (Error e) = F
Proof
  rw[result_equiv_def]
QED

Theorem result_equiv_halt_ok[simp]:
  result_equiv (Halt s) (OK s') = F
Proof
  rw[result_equiv_def]
QED

Theorem result_equiv_halt_revert[simp]:
  result_equiv (Halt s) (Revert s') = F
Proof
  rw[result_equiv_def]
QED

Theorem result_equiv_halt_error[simp]:
  result_equiv (Halt s) (Error e) = F
Proof
  rw[result_equiv_def]
QED

Theorem result_equiv_revert_ok[simp]:
  result_equiv (Revert s) (OK s') = F
Proof
  rw[result_equiv_def]
QED

Theorem result_equiv_revert_halt[simp]:
  result_equiv (Revert s) (Halt s') = F
Proof
  rw[result_equiv_def]
QED

Theorem result_equiv_revert_error[simp]:
  result_equiv (Revert s) (Error e) = F
Proof
  rw[result_equiv_def]
QED

Theorem result_equiv_error_ok[simp]:
  result_equiv (Error e) (OK s) = F
Proof
  rw[result_equiv_def]
QED

Theorem result_equiv_error_halt[simp]:
  result_equiv (Error e) (Halt s) = F
Proof
  rw[result_equiv_def]
QED

Theorem result_equiv_error_revert[simp]:
  result_equiv (Error e) (Revert s) = F
Proof
  rw[result_equiv_def]
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

(* --------------------------------------------------------------------------
   Result Equivalence for Operations (handles all result types)
   -------------------------------------------------------------------------- *)

Theorem exec_binop_result_equiv:
  !f inst s1 s2.
    state_equiv s1 s2 ==>
    result_equiv (exec_binop f inst s1) (exec_binop f inst s2)
Proof
  rw[exec_binop_def] >>
  Cases_on `inst.inst_operands` >> simp[result_equiv_def] >>
  Cases_on `t` >> simp[result_equiv_def] >>
  Cases_on `t'` >> simp[result_equiv_def] >>
  `eval_operand h s2 = eval_operand h s1` by metis_tac[eval_operand_state_equiv] >>
  `eval_operand h' s2 = eval_operand h' s1` by metis_tac[eval_operand_state_equiv] >>
  simp[] >>
  Cases_on `eval_operand h s1` >> simp[result_equiv_def] >>
  Cases_on `eval_operand h' s1` >> simp[result_equiv_def] >>
  Cases_on `inst.inst_output` >> simp[result_equiv_def] >>
  irule update_var_state_equiv >> simp[]
QED

Theorem exec_unop_result_equiv:
  !f inst s1 s2.
    state_equiv s1 s2 ==>
    result_equiv (exec_unop f inst s1) (exec_unop f inst s2)
Proof
  rw[exec_unop_def] >>
  Cases_on `inst.inst_operands` >> simp[result_equiv_def] >>
  Cases_on `t` >> simp[result_equiv_def] >>
  `eval_operand h s2 = eval_operand h s1` by metis_tac[eval_operand_state_equiv] >>
  simp[] >>
  Cases_on `eval_operand h s1` >> simp[result_equiv_def] >>
  Cases_on `inst.inst_output` >> simp[result_equiv_def] >>
  irule update_var_state_equiv >> simp[]
QED

Theorem exec_modop_result_equiv:
  !f inst s1 s2.
    state_equiv s1 s2 ==>
    result_equiv (exec_modop f inst s1) (exec_modop f inst s2)
Proof
  rw[exec_modop_def] >>
  Cases_on `inst.inst_operands` >> simp[result_equiv_def] >>
  Cases_on `t` >> simp[result_equiv_def] >>
  Cases_on `t'` >> simp[result_equiv_def] >>
  (* After 3 splits: h::h'::h''::t where t is the remaining tail *)
  Cases_on `t` >> simp[result_equiv_def] >- (
    (* 3 operands case: h::h'::h''::[] *)
    `eval_operand h s2 = eval_operand h s1` by metis_tac[eval_operand_state_equiv] >>
    `eval_operand h' s2 = eval_operand h' s1` by metis_tac[eval_operand_state_equiv] >>
    `eval_operand h'' s2 = eval_operand h'' s1` by metis_tac[eval_operand_state_equiv] >>
    simp[] >>
    Cases_on `eval_operand h s1` >> simp[result_equiv_def] >>
    Cases_on `eval_operand h' s1` >> simp[result_equiv_def] >>
    Cases_on `eval_operand h'' s1` >> simp[result_equiv_def] >>
    Cases_on `inst.inst_output` >> simp[result_equiv_def] >>
    irule update_var_state_equiv >> simp[]
  )
QED

(* Helper: handles load operations (MLOAD, SLOAD, TLOAD) *)
Theorem load_result_equiv_helper:
  !load_fn inst s1 s2.
    state_equiv s1 s2 /\
    (!offset s1 s2. state_equiv s1 s2 ==> load_fn offset s1 = load_fn offset s2)
  ==>
    result_equiv
      (case inst.inst_operands of
         [] => Error "requires 1 operand"
       | [op1] =>
         (case eval_operand op1 s1 of
            NONE => Error "undefined operand"
          | SOME addr =>
            case inst.inst_output of
              NONE => Error "requires output"
            | SOME out => OK (update_var out (load_fn (w2n addr) s1) s1))
       | _ => Error "requires 1 operand")
      (case inst.inst_operands of
         [] => Error "requires 1 operand"
       | [op1] =>
         (case eval_operand op1 s2 of
            NONE => Error "undefined operand"
          | SOME addr =>
            case inst.inst_output of
              NONE => Error "requires output"
            | SOME out => OK (update_var out (load_fn (w2n addr) s2) s2))
       | _ => Error "requires 1 operand")
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_operands` >> simp[result_equiv_def] >>
  Cases_on `t` >> simp[result_equiv_def] >>
  `eval_operand h s2 = eval_operand h s1` by metis_tac[eval_operand_state_equiv] >>
  simp[] >>
  Cases_on `eval_operand h s1` >> simp[result_equiv_def] >>
  Cases_on `inst.inst_output` >> simp[result_equiv_def] >>
  `load_fn (w2n x) s1 = load_fn (w2n x) s2` by metis_tac[] >>
  simp[] >> irule update_var_state_equiv >> simp[]
QED

(* Helper: handles store operations (MSTORE, SSTORE, TSTORE) *)
Theorem store_result_equiv_helper:
  !store_fn inst s1 s2.
    state_equiv s1 s2 /\
    (!k v s1 s2. state_equiv s1 s2 ==> state_equiv (store_fn k v s1) (store_fn k v s2))
  ==>
    result_equiv
      (case inst.inst_operands of
         [] => Error "requires 2 operands"
       | [_] => Error "requires 2 operands"
       | [op_val; op_key] =>
         (case eval_operand op_val s1 of
            NONE => Error "undefined operand"
          | SOME value =>
            case eval_operand op_key s1 of
              NONE => Error "undefined operand"
            | SOME key => OK (store_fn key value s1))
       | _ => Error "requires 2 operands")
      (case inst.inst_operands of
         [] => Error "requires 2 operands"
       | [_] => Error "requires 2 operands"
       | [op_val; op_key] =>
         (case eval_operand op_val s2 of
            NONE => Error "undefined operand"
          | SOME value =>
            case eval_operand op_key s2 of
              NONE => Error "undefined operand"
            | SOME key => OK (store_fn key value s2))
       | _ => Error "requires 2 operands")
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_operands` >> simp[result_equiv_def] >>
  Cases_on `t` >> simp[result_equiv_def] >>
  Cases_on `t'` >> simp[result_equiv_def] >>
  `eval_operand h s2 = eval_operand h s1` by metis_tac[eval_operand_state_equiv] >>
  `eval_operand h' s2 = eval_operand h' s1` by metis_tac[eval_operand_state_equiv] >>
  simp[] >>
  Cases_on `eval_operand h s1` >> simp[result_equiv_def] >>
  Cases_on `eval_operand h' s1` >> simp[result_equiv_def] >>
  metis_tac[]
QED

(* Helper for JNZ case - use CASE_TAC to break down all operand patterns *)
Theorem jnz_result_equiv:
  !inst s1 s2.
    state_equiv s1 s2 /\ inst.inst_opcode = JNZ ==>
    result_equiv (step_inst inst s1) (step_inst inst s2)
Proof
  rpt strip_tac >>
  simp[step_inst_def] >>
  (* CASE_TAC breaks down both case expressions, generating many subgoals *)
  (* Most are Error = Error which simplify away *)
  rpt CASE_TAC >> gvs[result_equiv_def] >>
  (* Remaining cases involve eval_operand and jump_to *)
  (* Prove eval_operand equality and substitute *)
  TRY (
    `eval_operand h s1 = eval_operand h s2` by metis_tac[eval_operand_state_equiv] >>
    gvs[] >>
    irule jump_to_state_equiv >> simp[]
  )
QED

Theorem step_inst_result_equiv:
  !inst s1 s2.
    state_equiv s1 s2 ==>
    result_equiv (step_inst inst s1) (step_inst inst s2)
Proof
  rpt strip_tac >>
  (* Handle JNZ specially before unfolding *)
  Cases_on `inst.inst_opcode = JNZ` >- (
    irule jnz_result_equiv >> simp[]
  ) >>
  simp[step_inst_def] >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  (* Binary ops *)
  TRY (irule exec_binop_result_equiv >> simp[] >> NO_TAC) >>
  (* Unary ops *)
  TRY (irule exec_unop_result_equiv >> simp[] >> NO_TAC) >>
  (* Mod ops *)
  TRY (irule exec_modop_result_equiv >> simp[] >> NO_TAC) >>
  (* Default case: Error = Error *)
  TRY (simp[result_equiv_def] >> NO_TAC) >>
  (* Load operations: MLOAD, SLOAD, TLOAD *)
  TRY (
    Cases_on `inst.inst_operands` >> simp[result_equiv_def] >>
    Cases_on `t` >> simp[result_equiv_def] >>
    `eval_operand h s2 = eval_operand h s1` by metis_tac[eval_operand_state_equiv] >>
    simp[] >>
    Cases_on `eval_operand h s1` >> simp[result_equiv_def] >>
    Cases_on `inst.inst_output` >> simp[result_equiv_def] >>
    irule update_var_state_equiv >> simp[] >> NO_TAC
  ) >>
  (* For SLOAD/TLOAD with load function, need the load fact *)
  TRY (
    Cases_on `inst.inst_operands` >> simp[result_equiv_def] >>
    Cases_on `t` >> simp[result_equiv_def] >>
    `eval_operand h s2 = eval_operand h s1` by metis_tac[eval_operand_state_equiv] >>
    simp[] >>
    Cases_on `eval_operand h s1` >> simp[result_equiv_def] >>
    Cases_on `inst.inst_output` >> simp[result_equiv_def] >>
    `sload x s1 = sload x s2` by fs[sload_def, state_equiv_def] >>
    simp[] >> irule update_var_state_equiv >> simp[] >> NO_TAC
  ) >>
  TRY (
    Cases_on `inst.inst_operands` >> simp[result_equiv_def] >>
    Cases_on `t` >> simp[result_equiv_def] >>
    `eval_operand h s2 = eval_operand h s1` by metis_tac[eval_operand_state_equiv] >>
    simp[] >>
    Cases_on `eval_operand h s1` >> simp[result_equiv_def] >>
    Cases_on `inst.inst_output` >> simp[result_equiv_def] >>
    `tload x s1 = tload x s2` by fs[tload_def, state_equiv_def] >>
    simp[] >> irule update_var_state_equiv >> simp[] >> NO_TAC
  ) >>
  TRY (
    Cases_on `inst.inst_operands` >> simp[result_equiv_def] >>
    Cases_on `t` >> simp[result_equiv_def] >>
    `eval_operand h s2 = eval_operand h s1` by metis_tac[eval_operand_state_equiv] >>
    simp[] >>
    Cases_on `eval_operand h s1` >> simp[result_equiv_def] >>
    Cases_on `inst.inst_output` >> simp[result_equiv_def] >>
    `mload (w2n x) s1 = mload (w2n x) s2` by fs[mload_def, state_equiv_def] >>
    simp[] >> irule update_var_state_equiv >> simp[] >> NO_TAC
  ) >>
  (* Store operations: MSTORE, SSTORE, TSTORE *)
  TRY (
    Cases_on `inst.inst_operands` >> simp[result_equiv_def] >>
    Cases_on `t` >> simp[result_equiv_def] >>
    Cases_on `t'` >> simp[result_equiv_def] >>
    `eval_operand h s2 = eval_operand h s1` by metis_tac[eval_operand_state_equiv] >>
    `eval_operand h' s2 = eval_operand h' s1` by metis_tac[eval_operand_state_equiv] >>
    simp[] >>
    Cases_on `eval_operand h s1` >> simp[result_equiv_def] >>
    Cases_on `eval_operand h' s1` >> simp[result_equiv_def] >>
    metis_tac[mstore_state_equiv, sstore_state_equiv, tstore_state_equiv] >> NO_TAC
  ) >>
  (* Control flow - JMP *)
  TRY (
    Cases_on `inst.inst_operands` >> simp[result_equiv_def] >>
    Cases_on `h` >> simp[result_equiv_def] >>
    Cases_on `t` >> simp[result_equiv_def] >>
    irule jump_to_state_equiv >> simp[] >> NO_TAC
  ) >>
  (* JNZ handled above before step_inst_def unfolding *)
  (* Terminators: STOP, RETURN, SINK *)
  TRY (
    simp[result_equiv_def] >> irule halt_state_state_equiv >> simp[] >> NO_TAC
  ) >>
  (* REVERT *)
  TRY (
    simp[result_equiv_def] >> irule revert_state_state_equiv >> simp[] >> NO_TAC
  ) >>
  (* PHI - use CASE_TAC approach like JNZ, with state field substitution *)
  TRY (
    `s1.vs_prev_bb = s2.vs_prev_bb` by fs[state_equiv_def] >>
    pop_assum (fn th => SUBST_ALL_TAC (SYM th)) >>
    rpt CASE_TAC >> gvs[result_equiv_def] >>
    (* Remaining subgoal: state_equiv for OK case *)
    TRY (
      `eval_operand x' s1 = eval_operand x' s2` by metis_tac[eval_operand_state_equiv] >>
      gvs[] >>
      irule update_var_state_equiv >> simp[]
    ) >> NO_TAC
  ) >>
  (* ASSIGN *)
  TRY (
    Cases_on `inst.inst_operands` >> simp[result_equiv_def] >>
    Cases_on `t` >> simp[result_equiv_def] >>
    Cases_on `inst.inst_output` >> simp[result_equiv_def] >>
    `eval_operand h s2 = eval_operand h s1` by metis_tac[eval_operand_state_equiv] >>
    simp[] >>
    Cases_on `eval_operand h s1` >> simp[result_equiv_def] >>
    irule update_var_state_equiv >> simp[] >> NO_TAC
  ) >>
  (* NOP *)
  simp[result_equiv_def, state_equiv_refl]
QED

Theorem step_in_block_result_equiv:
  !fn bb s1 s2.
    state_equiv s1 s2 ==>
      result_equiv (FST (step_in_block fn bb s1)) (FST (step_in_block fn bb s2)) /\
      SND (step_in_block fn bb s1) = SND (step_in_block fn bb s2)
Proof
  rpt strip_tac >>
  `s1.vs_inst_idx = s2.vs_inst_idx` by fs[state_equiv_def] >>
  simp[step_in_block_def] >>
  Cases_on `get_instruction bb s1.vs_inst_idx` >> simp[] >>
  `result_equiv (step_inst x s1) (step_inst x s2)` by metis_tac[step_inst_result_equiv] >>
  Cases_on `step_inst x s1` >> Cases_on `step_inst x s2` >> gvs[] >>
  Cases_on `is_terminator x.inst_opcode` >> gvs[] >>
  gvs[next_inst_def, state_equiv_def, var_equiv_def, lookup_var_def]
QED

Theorem run_block_result_equiv:
  !fn bb s1 s2.
    state_equiv s1 s2 ==>
    result_equiv (run_block fn bb s1) (run_block fn bb s2)
Proof
  ho_match_mp_tac run_block_ind >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  (* Unfold run_block on LHS *)
  simp[Once run_block_def] >>
  (* Unfold run_block on RHS using CONV_TAC to target the argument *)
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
  (* Get step_in_block result_equiv and SND equality *)
  `result_equiv (FST (step_in_block fn bb s1)) (FST (step_in_block fn bb s2)) /\
   SND (step_in_block fn bb s1) = SND (step_in_block fn bb s2)`
    by metis_tac[step_in_block_result_equiv] >>
  Cases_on `step_in_block fn bb s1` >>
  Cases_on `step_in_block fn bb s2` >>
  fs[] >>
  (* Now case split on the result type *)
  Cases_on `q` >> Cases_on `q'` >> gvs[] >>
  (* OK/OK case: v from s1, v' from s2, both have state_equiv *)
  TRY (
    `v.vs_halted <=> v'.vs_halted` by fs[state_equiv_def] >>
    Cases_on `v.vs_halted` >> gvs[] >>
    Cases_on `r` >> gvs[] >>
    (* If not is_term, use IH - need state_equiv v v' *)
    first_x_assum irule >> simp[] >> NO_TAC
  )
QED

val _ = export_theory();
