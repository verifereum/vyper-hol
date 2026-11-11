(*
 * Moving the PC of a symbolic step.
 *
 * Apart from JUMP and JUMPI, which go to a label's index, no instruction
 * reads the PC: a step only advances it. So the same instruction run at
 * another PC gives the same result there, shifted by the same amount. The
 * splice framework (asmSplice) runs the code outside a rewritten window at
 * shifted PCs with this.
 *
 * TOP-LEVEL:
 *   asm_step_op_pc_add  — concrete opcodes, with no jump table
 *   sym_step_pc_add     — symbolic steps other than JUMP and JUMPI
 *   sym_step_pc_next    — those steps advance the PC by one
 *   sym_step_prog_cong  — and see the program only through its data headers
 *   sym_step_base_stack — sym_base.as_stack stays empty
 *)

Theory asmSymPc
Ancestors
  asmSymSem asmSem stackOpSim

(* ===== Results with a moved PC ===== *)

Definition asm_result_pc_add_def:
  asm_result_pc_add n (AsmOK s) = AsmOK (s with as_pc := s.as_pc + n) ∧
  asm_result_pc_add n (AsmHalt s) = AsmHalt (s with as_pc := s.as_pc + n) ∧
  asm_result_pc_add n (AsmRevert s) =
    AsmRevert (s with as_pc := s.as_pc + n) ∧
  asm_result_pc_add n (AsmFault s) = AsmFault (s with as_pc := s.as_pc + n) ∧
  asm_result_pc_add n (AsmError e) = AsmError e
End

Definition sym_with_pc_def:
  sym_with_pc pc ss = ss with sym_base := ss.sym_base with as_pc := pc
End

Definition sym_result_pc_add_def:
  sym_result_pc_add n (SymOK ss) =
    SymOK (sym_with_pc (ss.sym_base.as_pc + n) ss) ∧
  sym_result_pc_add n (SymHalt ss) =
    SymHalt (sym_with_pc (ss.sym_base.as_pc + n) ss) ∧
  sym_result_pc_add n (SymRevert ss) =
    SymRevert (sym_with_pc (ss.sym_base.as_pc + n) ss) ∧
  sym_result_pc_add n (SymFault ss) =
    SymFault (sym_with_pc (ss.sym_base.as_pc + n) ss) ∧
  sym_result_pc_add n (SymError e) = SymError e ∧
  sym_result_pc_add n (SymBad e) = SymBad e
End

(* ===== Concrete steps ===== *)

Theorem asm_call_request_pc_add[local]:
  asm_call_request (s with as_pc := s.as_pc + n) a v off sz st =
  asm_call_request s a v off sz st
Proof
  simp[asm_call_request_def]
QED

Theorem asm_create_request_pc_add[local]:
  asm_create_request (s with as_pc := s.as_pc + n) v off sz salt =
  asm_create_request s v off sz salt
Proof
  simp[asm_create_request_def]
QED

Theorem make_asm_delegatecall_state_pc_add[local]:
  make_asm_delegatecall_state (s with as_pc := s.as_pc + n) a g d c st =
  make_asm_delegatecall_state s a g d c st
Proof
  simp[make_asm_delegatecall_state_def, asm_to_tx_params_def]
QED

Theorem extract_asm_result_pc_add[local]:
  extract_asm_result (s with as_pc := s.as_pc + n) v ro rs rr =
  OPTION_MAP (\(output,t). (output,t with as_pc := t.as_pc + n))
    (extract_asm_result s v ro rs rr)
Proof
  Cases_on `rr` >- simp[extract_asm_result_def] >>
  rename1 `SOME res` >> PairCases_on `res` >>
  simp[extract_asm_result_def] >>
  Cases_on `res1.contexts` >- simp[] >>
  rename1 `res1.contexts = ctx :: ctxs` >>
  Cases_on `ctxs` >> simp[] >>
  PairCases_on `ctx` >>
  simp[] >> pairarg_tac >> simp[]
QED

Theorem asm_consume_call_outcome_pc_add[local]:
  asm_consume_call_outcome rq ro rs stk (s with as_pc := s.as_pc + n) =
  asm_result_pc_add n (asm_consume_call_outcome rq ro rs stk s)
Proof
  simp[asm_consume_call_outcome_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >>
  simp[asm_result_pc_add_def, asm_next_def]
QED

Theorem asm_consume_create_outcome_pc_add[local]:
  asm_consume_create_outcome rq stk (s with as_pc := s.as_pc + n) =
  asm_result_pc_add n (asm_consume_create_outcome rq stk s)
Proof
  simp[asm_consume_create_outcome_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >>
  simp[asm_result_pc_add_def, asm_next_def]
QED

Theorem asm_binop_pc_add[local]:
  asm_binop f (s with as_pc := s.as_pc + n) =
  asm_result_pc_add n (asm_binop f s)
Proof
  simp[asm_binop_def] >> Cases_on `s.as_stack` >> simp[asm_result_pc_add_def] >>
  rename1 `s.as_stack = _ :: rest` >>
  Cases_on `rest` >> simp[asm_result_pc_add_def, asm_next_def]
QED

Theorem asm_unop_pc_add[local]:
  asm_unop f (s with as_pc := s.as_pc + n) =
  asm_result_pc_add n (asm_unop f s)
Proof
  simp[asm_unop_def] >> Cases_on `s.as_stack` >>
  simp[asm_result_pc_add_def, asm_next_def]
QED

Theorem asm_ternop_pc_add[local]:
  asm_ternop f (s with as_pc := s.as_pc + n) =
  asm_result_pc_add n (asm_ternop f s)
Proof
  simp[asm_ternop_def] >> Cases_on `s.as_stack` >> simp[asm_result_pc_add_def] >>
  rename1 `s.as_stack = _ :: rest` >>
  Cases_on `rest` >> simp[asm_result_pc_add_def] >>
  rename1 `s.as_stack = _ :: _ :: rest2` >>
  Cases_on `rest2` >> simp[asm_result_pc_add_def, asm_next_def]
QED

Theorem asm_step_arith_pc_add[local]:
  asm_step_arith name (s with as_pc := s.as_pc + n) =
  OPTION_MAP (asm_result_pc_add n) (asm_step_arith name s)
Proof
  pure_rewrite_tac[asm_step_arith_def, asm_binop_pc_add, asm_ternop_pc_add] >>
  rpt IF_CASES_TAC >> simp[]
QED

Theorem asm_step_compare_pc_add[local]:
  asm_step_compare name (s with as_pc := s.as_pc + n) =
  OPTION_MAP (asm_result_pc_add n) (asm_step_compare name s)
Proof
  pure_rewrite_tac[asm_step_compare_def, asm_binop_pc_add, asm_unop_pc_add] >>
  rpt IF_CASES_TAC >> simp[]
QED

Theorem asm_step_bitwise_pc_add[local]:
  asm_step_bitwise name (s with as_pc := s.as_pc + n) =
  OPTION_MAP (asm_result_pc_add n) (asm_step_bitwise name s)
Proof
  pure_rewrite_tac[asm_step_bitwise_def, asm_binop_pc_add, asm_unop_pc_add] >>
  rpt IF_CASES_TAC >> simp[]
QED

(* Split only the result-producing spine, never values stored in a state. *)
fun asm_pc_add_spine_tac g =
  let
    fun spine tm =
      if is_comb tm andalso same_const (rator tm) ``SOME`` then spine (rand tm)
      else tm
    val tm = spine (lhs (#2 g))
  in
    case total TypeBase.dest_case tm of
      SOME (_, scrutinee, _) =>
        (Cases_on [ANTIQUOTE
           (if same_const (#1 (strip_comb scrutinee)) ``OPTION_MAP``
            then rand scrutinee else scrutinee)] >>
         simp[asm_result_pc_add_def, asm_next_def]) g
    | NONE => if is_cond tm then
        (Cases_on [ANTIQUOTE (#1 (dest_cond tm))] >>
         simp[asm_result_pc_add_def, asm_next_def]) g
      else NO_TAC g
  end;

Theorem asm_step_memory_pc_add[local]:
  asm_step_memory name (s with as_pc := s.as_pc + n) =
  OPTION_MAP (asm_result_pc_add n) (asm_step_memory name s)
Proof
  pure_rewrite_tac[asm_step_memory_def] >> rpt IF_CASES_TAC >>
  simp[asm_mload_def, asm_mstore_def, asm_mstore8_def, asm_sload_def,
       asm_sstore_def, asm_tload_def, asm_tstore_def, asm_sha3_def,
       asm_pop_def, asm_push_val_def, asm_mcopy_def,
       asm_result_pc_add_def, asm_next_def] >>
  rpt asm_pc_add_spine_tac
QED

Theorem asm_step_control_pc_add[local]:
  asm_step_control FEMPTY name (s with as_pc := s.as_pc + n) =
  OPTION_MAP (asm_result_pc_add n) (asm_step_control FEMPTY name s)
Proof
  pure_rewrite_tac[asm_step_control_def] >> rpt IF_CASES_TAC >>
  simp[asm_jump_def, asm_jumpi_def, asm_return_op_def, asm_revert_op_def,
       asm_result_pc_add_def, asm_next_def] >>
  rpt asm_pc_add_spine_tac
QED

Theorem asm_step_copy_pc_add[local]:
  asm_step_copy name (s with as_pc := s.as_pc + n) =
  OPTION_MAP (asm_result_pc_add n) (asm_step_copy name s)
Proof
  pure_rewrite_tac[asm_step_copy_def] >> rpt IF_CASES_TAC >>
  simp[asm_copy_to_mem_def, asm_returndatacopy_def, asm_extcodecopy_def,
       asm_result_pc_add_def, asm_next_def] >>
  rpt asm_pc_add_spine_tac
QED

Theorem asm_step_context_pc_add[local]:
  asm_step_context name (s with as_pc := s.as_pc + n) =
  OPTION_MAP (asm_result_pc_add n) (asm_step_context name s)
Proof
  pure_rewrite_tac[asm_step_context_def] >> rpt IF_CASES_TAC >>
  simp[asm_gas_def, asm_push_val_def, asm_state_unop_def,
       asm_result_pc_add_def, asm_next_def] >>
  rpt asm_pc_add_spine_tac
QED

Theorem asm_dup_pc_add[local]:
  asm_dup k (s with as_pc := s.as_pc + n) =
  asm_result_pc_add n (asm_dup k s)
Proof
  simp[asm_dup_def] >> IF_CASES_TAC >>
  simp[asm_result_pc_add_def, asm_next_def]
QED

Theorem asm_swap_pc_add[local]:
  asm_swap k (s with as_pc := s.as_pc + n) =
  asm_result_pc_add n (asm_swap k s)
Proof
  simp[asm_swap_def] >> IF_CASES_TAC >>
  simp[asm_result_pc_add_def, asm_next_def]
QED

Theorem asm_log_pc_add[local]:
  asm_log k (s with as_pc := s.as_pc + n) =
  asm_result_pc_add n (asm_log k s)
Proof
  simp[asm_log_def] >> IF_CASES_TAC >>
  simp[asm_result_pc_add_def, asm_next_def]
QED

Theorem asm_exec_call_pc_add[local]:
  asm_exec_call st (s with as_pc := s.as_pc + n) =
  asm_result_pc_add n (asm_exec_call st s)
Proof
  simp[asm_exec_call_def,
       ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM] asm_call_request_pc_add] >>
  rpt asm_pc_add_spine_tac >>
  qmatch_goalsub_abbrev_tac `s with as_memory := mem` >>
  qspec_then `s with as_memory := mem` (mp_tac o GEN_ALL)
    (GEN ``s:asm_state`` asm_consume_call_outcome_pc_add) >>
  simp[] >> disch_then assume_tac >> first_x_assum irule
QED

Theorem asm_exec_staticcall_pc_add[local]:
  asm_exec_staticcall (s with as_pc := s.as_pc + n) =
  asm_result_pc_add n (asm_exec_staticcall s)
Proof
  simp[asm_exec_staticcall_def,
       ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM] asm_call_request_pc_add] >>
  rpt asm_pc_add_spine_tac >>
  qmatch_goalsub_abbrev_tac `s with as_memory := mem` >>
  qspec_then `s with as_memory := mem` (mp_tac o GEN_ALL)
    (GEN ``s:asm_state`` asm_consume_call_outcome_pc_add) >>
  simp[] >> disch_then assume_tac >> first_x_assum irule
QED

Theorem asm_exec_create_pc_add[local]:
  asm_exec_create (s with as_pc := s.as_pc + n) =
  asm_result_pc_add n (asm_exec_create s)
Proof
  simp[asm_exec_create_def,
       ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM] asm_create_request_pc_add] >>
  rpt asm_pc_add_spine_tac >>
  qmatch_goalsub_abbrev_tac `s with as_memory := mem` >>
  qspec_then `s with as_memory := mem` (mp_tac o GEN_ALL)
    (GEN ``s:asm_state`` asm_consume_create_outcome_pc_add) >>
  simp[] >> disch_then assume_tac >> first_x_assum irule
QED

Theorem asm_exec_create2_pc_add[local]:
  asm_exec_create2 (s with as_pc := s.as_pc + n) =
  asm_result_pc_add n (asm_exec_create2 s)
Proof
  simp[asm_exec_create2_def,
       ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM] asm_create_request_pc_add] >>
  rpt asm_pc_add_spine_tac >>
  qmatch_goalsub_abbrev_tac `s with as_memory := mem` >>
  qspec_then `s with as_memory := mem` (mp_tac o GEN_ALL)
    (GEN ``s:asm_state`` asm_consume_create_outcome_pc_add) >>
  simp[] >> disch_then assume_tac >> first_x_assum irule
QED

Theorem asm_exec_delegatecall_pc_add[local]:
  asm_exec_delegatecall (s with as_pc := s.as_pc + n) =
  asm_result_pc_add n (asm_exec_delegatecall s)
Proof
  simp[asm_exec_delegatecall_def,
       ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM] make_asm_delegatecall_state_pc_add,
       ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM] extract_asm_result_pc_add] >>
  rpt asm_pc_add_spine_tac >>
  PairCases_on `x` >> gvs[asm_result_pc_add_def]
QED

Theorem asm_step_extcall_pc_add[local]:
  asm_step_extcall name (s with as_pc := s.as_pc + n) =
  OPTION_MAP (asm_result_pc_add n) (asm_step_extcall name s)
Proof
  pure_rewrite_tac[asm_step_extcall_def, asm_exec_call_pc_add,
       asm_exec_staticcall_pc_add, asm_exec_delegatecall_pc_add,
       asm_exec_create_pc_add, asm_exec_create2_pc_add] >>
  rpt IF_CASES_TAC >>
  simp[asm_selfdestruct_def, asm_result_pc_add_def, asm_next_def] >>
  rpt asm_pc_add_spine_tac
QED

(* With no jump table, JUMP fails and JUMPI either fails or falls through,
   so no opcode sets the PC to anything but its successor. *)
Theorem asm_step_op_pc_add:
  ∀name s n.
    asm_step_op FEMPTY name (s with as_pc := s.as_pc + n) =
    asm_result_pc_add n (asm_step_op FEMPTY name s)
Proof
  rpt gen_tac >>
  pure_rewrite_tac[asm_step_op_def, asm_step_arith_pc_add,
    asm_step_compare_pc_add, asm_step_bitwise_pc_add, asm_step_memory_pc_add,
    asm_step_control_pc_add, asm_step_extcall_pc_add, asm_step_copy_pc_add,
    asm_step_context_pc_add, asm_dup_pc_add, asm_swap_pc_add, asm_log_pc_add] >>
  Cases_on `asm_step_arith name s` >> simp[] >>
  Cases_on `asm_step_compare name s` >> simp[] >>
  Cases_on `asm_step_bitwise name s` >> simp[] >>
  Cases_on `asm_step_memory name s` >> simp[] >>
  Cases_on `asm_step_control FEMPTY name s` >> simp[] >>
  Cases_on `asm_step_extcall name s` >> simp[] >>
  Cases_on `asm_step_copy name s` >> simp[] >>
  Cases_on `asm_step_context name s` >> simp[] >>
  Cases_on `ALOOKUP dup_table name` >> simp[] >>
  Cases_on `ALOOKUP swap_table name` >> simp[] >>
  Cases_on `ALOOKUP log_table name` >> simp[asm_result_pc_add_def]
QED

Theorem asm_mstore_pc_add:
  asm_mstore (s with as_pc := s.as_pc + n) =
  asm_result_pc_add n (asm_mstore s)
Proof
  simp[asm_mstore_def] >> CASE_TAC >> simp[asm_result_pc_add_def] >>
  CASE_TAC >> simp[asm_result_pc_add_def, asm_next_def]
QED

Theorem asm_copy_to_mem_pc_add:
  asm_copy_to_mem bytes (s with as_pc := s.as_pc + n) =
  asm_result_pc_add n (asm_copy_to_mem bytes s)
Proof
  simp[asm_copy_to_mem_def] >> CASE_TAC >> simp[asm_result_pc_add_def] >>
  CASE_TAC >> simp[asm_result_pc_add_def] >>
  CASE_TAC >> simp[asm_result_pc_add_def, asm_next_def]
QED

Theorem asm_step_pc_add:
  asm_step FEMPTY FEMPTY inst (s with as_pc := s.as_pc + n) =
  asm_result_pc_add n (asm_step FEMPTY FEMPTY inst s)
Proof
  Cases_on `inst` >>
  simp[asm_step_def, asm_step_op_pc_add, asm_result_pc_add_def,
       asm_next_def]
QED

(* ===== Symbolic steps ===== *)

Theorem sym_with_pc_fields[simp]:
  (sym_with_pc q ss).sym_stack = ss.sym_stack ∧
  (sym_with_pc q ss).sym_mem_labels = ss.sym_mem_labels ∧
  (sym_with_pc q ss).sym_own_code = ss.sym_own_code
Proof
  simp[sym_with_pc_def]
QED

Theorem sym_set_stack_pc_add[local]:
  sym_set_stack stk (sym_with_pc (n + ss.sym_base.as_pc) ss) =
  sym_result_pc_add n (sym_set_stack stk ss)
Proof
  simp[sym_set_stack_def, sym_with_pc_def, sym_result_pc_add_def,
       asm_next_def]
QED

Theorem sym_push_lab_pc_add[local]:
  sym_push_lab l d stk (sym_with_pc (n + ss.sym_base.as_pc) ss) =
  sym_result_pc_add n (sym_push_lab l d stk ss)
Proof
  rw[sym_push_lab_def, sym_set_stack_pc_add, sym_result_pc_add_def]
QED

Theorem sym_lift_with_base[local]:
  sym_lift k labs (ss with sym_base := b) r = sym_lift k labs ss r
Proof
  Cases_on `r` >> simp[sym_lift_def]
QED

Theorem sym_lift_pc_add[local]:
  sym_lift k labs ss (asm_result_pc_add n r) =
  sym_result_pc_add n (sym_lift k labs ss r)
Proof
  Cases_on `r` >>
  simp[sym_lift_def, asm_result_pc_add_def, sym_result_pc_add_def,
       sym_with_pc_def]
QED

(* A lifted concrete step f that commutes with moving the PC. *)
Theorem sym_lift_step_pc_add[local]:
  (∀s. f (s with as_pc := s.as_pc + n) = asm_result_pc_add n (f s)) ∧
  q = n + ss.sym_base.as_pc ⇒
  sym_lift k labs (sym_with_pc q ss)
    (f ((sym_with_pc q ss).sym_base with as_stack := a)) =
  sym_result_pc_add n (sym_lift k labs ss (f (ss.sym_base with as_stack := a)))
Proof
  strip_tac >> gvs[] >>
  first_x_assum (qspec_then `ss.sym_base with as_stack := a` mp_tac) >>
  simp[sym_with_pc_def, sym_lift_with_base, sym_lift_pc_add]
QED

Theorem sym_step_concrete_pc_add[local]:
  sym_step_concrete name (sym_with_pc (n + ss.sym_base.as_pc) ss) =
  sym_result_pc_add n (sym_step_concrete name ss)
Proof
  rw[sym_step_concrete_def, sym_result_pc_add_def] >>
  CASE_TAC >> rw[sym_result_pc_add_def] >>
  irule sym_lift_step_pc_add >> simp[asm_step_op_pc_add]
QED

Theorem sym_add_pc_add[local]:
  sym_add p env (sym_with_pc (n + ss.sym_base.as_pc) ss) =
  sym_result_pc_add n (sym_add p env ss)
Proof
  simp[sym_add_def] >> rpt CASE_TAC >>
  rw[sym_push_lab_pc_add, sym_step_concrete_pc_add, sym_result_pc_add_def]
QED

Theorem sym_mstore_pc_add[local]:
  sym_mstore (sym_with_pc (n + ss.sym_base.as_pc) ss) =
  sym_result_pc_add n (sym_mstore ss)
Proof
  simp[sym_mstore_def] >> rpt CASE_TAC >> simp[sym_step_concrete_pc_add] >>
  irule sym_lift_step_pc_add >> simp[asm_mstore_pc_add]
QED

Theorem sym_mload_pc_add[local]:
  sym_mload (sym_with_pc (n + ss.sym_base.as_pc) ss) =
  sym_result_pc_add n (sym_mload ss)
Proof
  simp[sym_mload_def] >> rpt CASE_TAC >> simp[sym_step_concrete_pc_add] >>
  simp[sym_result_pc_add_def, sym_with_pc_def, asm_next_def]
QED

Theorem sym_codecopy_pc_add[local]:
  sym_codecopy p env (sym_with_pc (n + ss.sym_base.as_pc) ss) =
  sym_result_pc_add n (sym_codecopy p env ss)
Proof
  simp[sym_codecopy_def] >>
  Cases_on `ss.sym_stack` >- simp[sym_result_pc_add_def] >>
  rename1 `ss.sym_stack = x1 :: t1` >>
  Cases_on `t1` >- simp[sym_result_pc_add_def] >>
  rename1 `ss.sym_stack = x1 :: x2 :: t2` >>
  Cases_on `t2`
  >- (Cases_on `x1` >> Cases_on `x2` >> simp[sym_result_pc_add_def]) >>
  rename1 `ss.sym_stack = x1 :: x2 :: x3 :: t3` >>
  Cases_on `x1` >> Cases_on `x2` >> Cases_on `x3` >>
  rw[sym_result_pc_add_def] >>
  irule sym_lift_step_pc_add >> simp[asm_copy_to_mem_pc_add]
QED

Theorem sym_step_pc_add:
  inst ≠ AsmOp "JUMP" ∧ inst ≠ AsmOp "JUMPI" ⇒
  sym_step p env inst (sym_with_pc (ss.sym_base.as_pc + n) ss) =
  sym_result_pc_add n (sym_step p env inst ss)
Proof
  strip_tac >> simp[] >> Cases_on `∃name. inst = AsmOp name`
  >- (gvs[sym_step_def, sym_step_op_def] >>
      rw[sym_add_pc_add, sym_mstore_pc_add, sym_mload_pc_add,
         sym_codecopy_pc_add, sym_result_pc_add_def] >>
      rpt CASE_TAC >>
      rw[sym_set_stack_pc_add, sym_dup_def, sym_swap_def,
         sym_step_concrete_pc_add, sym_result_pc_add_def]) >>
  Cases_on `∃l. inst = AsmPushLabel l`
  >- gvs[sym_step_def, sym_set_stack_pc_add] >>
  Cases_on `∃l d. inst = AsmPushOfst l d`
  >- gvs[sym_step_def, sym_push_lab_pc_add] >>
  `sym_step p env inst = λss. sym_lift 0 ss.sym_mem_labels ss
     (asm_step FEMPTY FEMPTY inst (ss.sym_base with as_stack := []))`
    by (rw[FUN_EQ_THM] >> Cases_on `inst` >> gvs[sym_step_def]) >>
  simp[] >> irule sym_lift_step_pc_add >> simp[asm_step_pc_add]
QED

Theorem sym_lift_ok:
  sym_lift k labs ss r = SymOK ss' ⇒
  ∃s. r = AsmOK s ∧ ss'.sym_base.as_pc = s.as_pc ∧
      ss'.sym_base.as_stack = []
Proof
  Cases_on `r` >> simp[sym_lift_def] >> strip_tac >> gvs[]
QED

Theorem sym_set_stack_pc_next[local]:
  sym_set_stack stk ss = SymOK ss' ⇒
  ss'.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  simp[sym_set_stack_def, asm_next_def] >> strip_tac >> gvs[]
QED

Theorem sym_push_lab_pc_next[local]:
  sym_push_lab l d stk ss = SymOK ss' ⇒
  ss'.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  rw[sym_push_lab_def] >> drule sym_set_stack_pc_next >> simp[]
QED

Theorem sym_step_concrete_pc_next[local]:
  sym_step_concrete name ss = SymOK ss' ∧
  name ≠ "JUMP" ∧ name ≠ "JUMPI" ⇒
  ss'.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  rw[sym_step_concrete_def, AllCaseEqs()] >>
  drule sym_lift_ok >> strip_tac >>
  qspecl_then [`FEMPTY`, `FEMPTY`, `AsmOp name`,
               `ss.sym_base with as_stack := args`, `s`] mp_tac
    asm_step_pc_advance >>
  gvs[asm_step_def]
QED

Theorem sym_step_pc_next:
  inst ≠ AsmOp "JUMP" ∧ inst ≠ AsmOp "JUMPI" ∧
  sym_step p env inst ss = SymOK ss' ⇒
  ss'.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  strip_tac >> Cases_on `∃name. inst = AsmOp name`
  >- (gvs[sym_step_def, sym_step_op_def] >>
      gvs[AllCaseEqs(), sym_add_def, sym_mstore_def, sym_mload_def,
          sym_codecopy_def, sym_dup_def, sym_swap_def] >>
      imp_res_tac sym_set_stack_pc_next >>
      imp_res_tac sym_push_lab_pc_next >>
      imp_res_tac sym_step_concrete_pc_next >>
      imp_res_tac sym_lift_ok >>
      gvs[asm_mstore_def, asm_copy_to_mem_def, AllCaseEqs(), asm_next_def]) >>
  `∃r. sym_step p env inst ss =
       sym_lift 0 ss.sym_mem_labels ss r ∧
       asm_step FEMPTY FEMPTY inst (ss.sym_base with as_stack := []) = r ∨
       ∃stk. sym_step p env inst ss = sym_set_stack stk ss ∨
       ∃l d. sym_step p env inst ss = sym_push_lab l d stk ss`
    by (Cases_on `inst` >> gvs[sym_step_def] >> metis_tac[]) >>
  gvs[]
  >- (drule sym_lift_ok >> strip_tac >> drule asm_step_pc_advance >> simp[])
  >- (drule sym_set_stack_pc_next >> simp[]) >>
  drule sym_push_lab_pc_next >> simp[]
QED

Theorem sym_step_prog_cong:
  (∀l. MEM (AsmDataHeader l) p ⇔ MEM (AsmDataHeader l) p') ∧
  inst ≠ AsmOp "JUMP" ∧ inst ≠ AsmOp "JUMPI" ⇒
  sym_step p env inst ss = sym_step p' env inst ss
Proof
  rw[] >> Cases_on `inst` >> simp[sym_step_def] >> gvs[] >>
  simp[sym_step_op_def] >> rw[] >>
  simp[sym_add_def, sym_codecopy_def, sym_data_label_def]
QED

(* ===== sym_base.as_stack stays empty ===== *)

Theorem sym_set_stack_base[local]:
  sym_set_stack stk ss = SymOK ss' ⇒ ss'.sym_base = asm_next ss.sym_base
Proof
  simp[sym_set_stack_def] >> strip_tac >> gvs[]
QED

Theorem sym_push_lab_base[local]:
  sym_push_lab l d stk ss = SymOK ss' ⇒ ss'.sym_base = asm_next ss.sym_base
Proof
  rw[sym_push_lab_def] >> drule sym_set_stack_base >> simp[]
QED

Theorem sym_step_concrete_base_stack[local]:
  sym_step_concrete name ss = SymOK ss' ⇒ ss'.sym_base.as_stack = []
Proof
  rw[sym_step_concrete_def, AllCaseEqs()] >>
  drule sym_lift_ok >> simp[PULL_EXISTS]
QED

Theorem sym_step_op_base_stack[local]:
  ss.sym_base.as_stack = [] ∧ sym_step_op p env name ss = SymOK ss' ⇒
  ss'.sym_base.as_stack = []
Proof
  rw[sym_step_op_def, AllCaseEqs()] >>
  gvs[sym_jump_def, sym_jumpi_def, sym_add_def, sym_mstore_def,
      sym_mload_def, sym_codecopy_def, sym_dup_def, sym_swap_def,
      AllCaseEqs()] >>
  imp_res_tac sym_set_stack_base >> imp_res_tac sym_push_lab_base >>
  imp_res_tac sym_step_concrete_base_stack >> imp_res_tac sym_lift_ok >>
  gvs[asm_next_def]
QED

Theorem sym_step_base_stack:
  ss.sym_base.as_stack = [] ∧ sym_step p env inst ss = SymOK ss' ⇒
  ss'.sym_base.as_stack = []
Proof
  Cases_on `inst` >> rw[sym_step_def] >>
  imp_res_tac sym_step_op_base_stack >>
  imp_res_tac sym_set_stack_base >> imp_res_tac sym_push_lab_base >>
  imp_res_tac sym_lift_ok >> gvs[asm_next_def]
QED
