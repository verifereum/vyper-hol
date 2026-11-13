(*
 * Stack-frame extension for the assembly step helpers.
 *
 * Each helper of asm_step (asmSem) reads and writes only the stack entries
 * it pops and pushes, so one that succeeds on a stack top succeeds on the
 * same top above any rest, with the rest intact.  asmFrame dispatches
 * asm_step over these.
 *
 * TOP-LEVEL (one per helper):
 *   asm_<op>_frame            — helper on top ++ rest, from helper on top
 *   asm_<op>_not_ok           — RETURN, REVERT, SELFDESTRUCT never AsmOK
 *   <fn>_stack                — call setup functions ignore as_stack
 *   asm_exec_<call>_frame     — the external-call helpers
 *)

Theory asmFrameHelpers
Ancestors
  asmSem list

Theorem asm_binop_frame:
  asm_binop f (s with as_stack := top) = AsmOK t ==>
  asm_binop f (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  namedCases_on `top` ["", "a tail"] >> simp[asm_binop_def] >>
  Cases_on `tail` >>
  simp[asm_binop_def, asm_next_def] >> strip_tac >> gvs[]
QED

Theorem asm_unop_frame:
  asm_unop f (s with as_stack := top) = AsmOK t ==>
  asm_unop f (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  Cases_on `top` >> simp[asm_unop_def, asm_next_def] >> strip_tac >> gvs[]
QED

Theorem asm_ternop_frame:
  asm_ternop f (s with as_stack := top) = AsmOK t ==>
  asm_ternop f (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  namedCases_on `top` ["", "a tail"] >> simp[asm_ternop_def] >>
  namedCases_on `tail` ["", "b tail2"] >> simp[asm_ternop_def] >>
  Cases_on `tail2` >>
  simp[asm_ternop_def, asm_next_def] >> strip_tac >> gvs[]
QED

Theorem asm_push_val_frame:
  asm_push_val v (s with as_stack := top) = AsmOK t ==>
  asm_push_val v (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  simp[asm_push_val_def, asm_next_def] >> strip_tac >> gvs[]
QED

Theorem asm_pop_frame:
  asm_pop (s with as_stack := top) = AsmOK t ==>
  asm_pop (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  Cases_on `top` >> simp[asm_pop_def, asm_next_def] >> strip_tac >> gvs[]
QED

Theorem asm_state_unop_frame:
  (!a s stk. f a (s with as_stack := stk) = f a s) ==>
  asm_state_unop f (s with as_stack := top) = AsmOK t ==>
  asm_state_unop f (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  strip_tac >> Cases_on `top` >>
  simp[asm_state_unop_def, asm_next_def] >> strip_tac >> gvs[]
QED

Theorem asm_dup_frame:
  asm_dup n (s with as_stack := top) = AsmOK t ==>
  asm_dup n (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  simp[asm_dup_def, AllCaseEqs()] >> strip_tac >>
  gvs[asm_next_def, EL_APPEND_EQN]
QED

Theorem asm_swap_frame:
  asm_swap n (s with as_stack := top) = AsmOK t ==>
  asm_swap n (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  simp[asm_swap_def, AllCaseEqs()] >> strip_tac >>
  Cases_on `top` >> gvs[asm_next_def, EL_APPEND_EQN,
    rich_listTheory.LUPDATE_APPEND1]
QED

Theorem asm_gas_frame:
  asm_gas (s with as_stack := top) = AsmOK t ==>
  asm_gas (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  Cases_on `s.as_gas_readings` >>
  simp[asm_gas_def, asm_push_val_def, asm_next_def] >> strip_tac >> gvs[]
QED

Theorem asm_mload_frame:
  asm_mload (s with as_stack := top) = AsmOK t ==>
  asm_mload (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  Cases_on `top` >> simp[asm_mload_def, asm_next_def] >> strip_tac >> gvs[]
QED

Theorem asm_mstore_frame:
  asm_mstore (s with as_stack := top) = AsmOK t ==>
  asm_mstore (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  namedCases_on `top` ["", "a tail"] >> simp[asm_mstore_def] >>
  Cases_on `tail` >> simp[asm_mstore_def, asm_next_def] >> strip_tac >> gvs[]
QED

Theorem asm_mstore8_frame:
  asm_mstore8 (s with as_stack := top) = AsmOK t ==>
  asm_mstore8 (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  namedCases_on `top` ["", "a tail"] >> simp[asm_mstore8_def] >>
  Cases_on `tail` >> simp[asm_mstore8_def, asm_next_def] >> strip_tac >> gvs[]
QED

Theorem asm_sload_frame:
  asm_sload (s with as_stack := top) = AsmOK t ==>
  asm_sload (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  Cases_on `top` >> simp[asm_sload_def, asm_next_def] >> strip_tac >> gvs[]
QED

Theorem asm_sstore_frame:
  asm_sstore (s with as_stack := top) = AsmOK t ==>
  asm_sstore (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  namedCases_on `top` ["", "a tail"] >> simp[asm_sstore_def] >>
  Cases_on `tail` >> simp[asm_sstore_def, asm_next_def] >> strip_tac >> gvs[]
QED

Theorem asm_tload_frame:
  asm_tload (s with as_stack := top) = AsmOK t ==>
  asm_tload (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  Cases_on `top` >> simp[asm_tload_def, asm_next_def] >> strip_tac >> gvs[]
QED

Theorem asm_tstore_frame:
  asm_tstore (s with as_stack := top) = AsmOK t ==>
  asm_tstore (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  namedCases_on `top` ["", "a tail"] >> simp[asm_tstore_def] >>
  Cases_on `tail` >> simp[asm_tstore_def, asm_next_def] >> strip_tac >> gvs[]
QED

Theorem asm_jump_frame:
  asm_jump o2pc (s with as_stack := top) = AsmOK t ==>
  asm_jump o2pc (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  Cases_on `top` >> simp[asm_jump_def, AllCaseEqs()] >> strip_tac >> gvs[]
QED

Theorem asm_jumpi_frame:
  asm_jumpi o2pc (s with as_stack := top) = AsmOK t ==>
  asm_jumpi o2pc (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  namedCases_on `top` ["", "a tail"] >> simp[asm_jumpi_def] >>
  Cases_on `tail` >> simp[asm_jumpi_def, AllCaseEqs(), asm_next_def] >>
  strip_tac >> gvs[]
QED

Theorem asm_return_op_not_ok:
  asm_return_op s <> AsmOK t
Proof
  namedCases_on `s.as_stack` ["", "a tail"] >> simp[asm_return_op_def] >>
  Cases_on `tail` >> simp[]
QED

Theorem asm_revert_op_not_ok:
  asm_revert_op s <> AsmOK t
Proof
  namedCases_on `s.as_stack` ["", "a tail"] >> simp[asm_revert_op_def] >>
  Cases_on `tail` >> simp[]
QED

Theorem asm_selfdestruct_not_ok:
  asm_selfdestruct s <> AsmOK t
Proof
  Cases_on `s.as_stack` >> simp[asm_selfdestruct_def]
QED

Theorem asm_sha3_frame:
  asm_sha3 (s with as_stack := top) = AsmOK t ==>
  asm_sha3 (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  namedCases_on `top` ["", "a tail"] >> simp[asm_sha3_def] >>
  Cases_on `tail` >> simp[asm_sha3_def, asm_next_def] >> strip_tac >> gvs[]
QED

Theorem asm_copy_to_mem_frame:
  asm_copy_to_mem src (s with as_stack := top) = AsmOK t ==>
  asm_copy_to_mem src (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  namedCases_on `top` ["", "a tail"] >> simp[asm_copy_to_mem_def] >>
  namedCases_on `tail` ["", "b tail2"] >> simp[asm_copy_to_mem_def] >>
  Cases_on `tail2` >> simp[asm_copy_to_mem_def, asm_next_def] >> strip_tac >> gvs[]
QED

Theorem asm_returndatacopy_frame:
  asm_returndatacopy (s with as_stack := top) = AsmOK t ==>
  asm_returndatacopy (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  namedCases_on `top` ["", "a tail"] >> simp[asm_returndatacopy_def] >>
  namedCases_on `tail` ["", "b tail2"] >> simp[asm_returndatacopy_def] >>
  Cases_on `tail2` >> simp[asm_returndatacopy_def, asm_next_def, AllCaseEqs()] >>
  strip_tac >> gvs[]
QED

Theorem asm_extcodecopy_frame:
  asm_extcodecopy (s with as_stack := top) = AsmOK t ==>
  asm_extcodecopy (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  namedCases_on `top` ["", "a tail"] >> simp[asm_extcodecopy_def] >>
  namedCases_on `tail` ["", "b tail2"] >> simp[asm_extcodecopy_def] >>
  namedCases_on `tail2` ["", "c tail3"] >> simp[asm_extcodecopy_def] >>
  Cases_on `tail3` >> simp[asm_extcodecopy_def, asm_next_def] >> strip_tac >> gvs[]
QED

Theorem asm_mcopy_frame:
  asm_mcopy (s with as_stack := top) = AsmOK t ==>
  asm_mcopy (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  namedCases_on `top` ["", "a tail"] >> simp[asm_mcopy_def] >>
  namedCases_on `tail` ["", "b tail2"] >> simp[asm_mcopy_def] >>
  Cases_on `tail2` >> simp[asm_mcopy_def, asm_next_def] >> strip_tac >> gvs[]
QED

Theorem asm_log_frame:
  asm_log n (s with as_stack := top) = AsmOK t ==>
  asm_log n (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  namedCases_on `top` ["", "a tail"] >> simp[asm_log_def] >>
  namedCases_on `tail` ["", "b stk"] >> simp[asm_log_def, AllCaseEqs()] >>
  strip_tac >> gvs[asm_next_def, TAKE_APPEND1, DROP_APPEND1]
QED

(* ===== External calls and creates ===== *)

Theorem asm_to_tx_params_stack:
  asm_to_tx_params (s with as_stack := xs) = asm_to_tx_params s
Proof
  simp[asm_to_tx_params_def]
QED

Theorem make_asm_delegatecall_state_stack:
  make_asm_delegatecall_state (s with as_stack := xs) target gas calldata code is_static =
  make_asm_delegatecall_state s target gas calldata code is_static
Proof
  simp[make_asm_delegatecall_state_def, asm_to_tx_params_stack]
QED

Theorem make_asm_create_state_stack:
  make_asm_create_state (s with as_stack := xs) addr gas value code =
  make_asm_create_state s addr gas value code
Proof
  simp[make_asm_create_state_def, asm_to_tx_params_stack]
QED

Theorem asm_call_request_stack:
  asm_call_request (s with as_stack := xs) addr value ao asz is_static =
  asm_call_request s addr value ao asz is_static
Proof
  simp[asm_call_request_def]
QED

Theorem extract_asm_result_stack:
  extract_asm_result (s with as_stack := xs) v ro rs rr =
  OPTION_MAP (\(out,t). (out,t with as_stack := xs))
    (extract_asm_result s v ro rs rr)
Proof
  namedCases_on `rr` ["", "result_state"] >> simp[extract_asm_result_def] >>
  PairCases_on `result_state` >> simp[extract_asm_result_def] >>
  namedCases_on `result_state1.contexts` ["", "ctx tail"] >> simp[] >>
  Cases_on `tail` >> simp[] >> PairCases_on `ctx` >> simp[] >>
  pairarg_tac >> simp[]
QED

Theorem asm_consume_call_outcome_frame:
  asm_consume_call_outcome rq ro rs stk s = AsmOK t ==>
  asm_consume_call_outcome rq ro rs (stk ++ rest) (s with as_stack := xs) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  simp[asm_consume_call_outcome_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >>
  simp[asm_next_def] >> strip_tac >> gvs[]
QED

Theorem asm_create_request_stack[local]:
  asm_create_request (s with as_stack := xs) value off sz salt_opt =
  asm_create_request s value off sz salt_opt
Proof
  simp[asm_create_request_def]
QED

Theorem asm_consume_create_outcome_frame[local]:
  asm_consume_create_outcome rq stk s = AsmOK t ==>
  asm_consume_create_outcome rq (stk ++ rest) (s with as_stack := xs) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  simp[asm_consume_create_outcome_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >>
  simp[asm_next_def] >> strip_tac >> gvs[]
QED

Theorem asm_exec_create_frame:
  asm_exec_create (s with as_stack := top) = AsmOK t ==>
  asm_exec_create (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  namedCases_on `top` ["", "a tail"] >> simp[asm_exec_create_def] >>
  namedCases_on `tail` ["", "b tail2"] >> simp[asm_exec_create_def] >>
  namedCases_on `tail2` ["", "sz stk"] >>
  simp[asm_exec_create_def] >>
  Cases_on `w2n sz > 2 * max_code_size` >>
  simp[asm_exec_create_def, asm_create_request_stack] >>
  strip_tac >> drule asm_consume_create_outcome_frame >>
  disch_then (qspecl_then [`a::b::sz::(stk ++ rest)`, `rest`] mp_tac) >>
  simp[]
QED

Theorem asm_exec_create2_frame:
  asm_exec_create2 (s with as_stack := top) = AsmOK t ==>
  asm_exec_create2 (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  namedCases_on `top` ["", "a tail"] >> simp[asm_exec_create2_def] >>
  namedCases_on `tail` ["", "b tail2"] >> simp[asm_exec_create2_def] >>
  namedCases_on `tail2` ["", "c tail3"] >> simp[asm_exec_create2_def] >>
  namedCases_on `tail3` ["", "salt stk"] >>
  simp[asm_exec_create2_def] >>
  Cases_on `w2n c > 2 * max_code_size` >>
  simp[asm_exec_create2_def, asm_create_request_stack] >>
  strip_tac >> drule asm_consume_create_outcome_frame >>
  disch_then (qspecl_then [`a::b::c::salt::(stk ++ rest)`, `rest`] mp_tac) >>
  simp[]
QED

Theorem asm_exec_delegatecall_frame:
  asm_exec_delegatecall (s with as_stack := top) = AsmOK t ==>
  asm_exec_delegatecall (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  namedCases_on `top` ["", "a tail"] >> simp[asm_exec_delegatecall_def] >>
  namedCases_on `tail` ["", "b tail2"] >> simp[asm_exec_delegatecall_def] >>
  namedCases_on `tail2` ["", "c tail3"] >> simp[asm_exec_delegatecall_def] >>
  namedCases_on `tail3` ["", "d tail4"] >> simp[asm_exec_delegatecall_def] >>
  namedCases_on `tail4` ["", "e tail5"] >> simp[asm_exec_delegatecall_def] >>
  Cases_on `tail5` >> simp[asm_exec_delegatecall_def, asm_call_request_stack] >>
  strip_tac >> drule asm_consume_call_outcome_frame >>
  disch_then (qspecl_then [`a::b::c::d::e::h::(t' ++ rest)`, `rest`] mp_tac) >>
  simp[]
QED

Theorem asm_exec_call_frame:
  asm_exec_call is_static (s with as_stack := top) = AsmOK t ==>
  asm_exec_call is_static (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  namedCases_on `top` ["", "a tail"] >> simp[asm_exec_call_def] >>
  namedCases_on `tail` ["", "b tail2"] >> simp[asm_exec_call_def] >>
  namedCases_on `tail2` ["", "c tail3"] >> simp[asm_exec_call_def] >>
  namedCases_on `tail3` ["", "d tail4"] >> simp[asm_exec_call_def] >>
  namedCases_on `tail4` ["", "e tail5"] >> simp[asm_exec_call_def] >>
  namedCases_on `tail5` ["", "f tail6"] >> simp[asm_exec_call_def] >>
  Cases_on `tail6` >> simp[asm_exec_call_def, asm_call_request_stack] >>
  strip_tac >> drule asm_consume_call_outcome_frame >>
  disch_then (qspecl_then [`a::b::c::d::e::f::h::(t' ++ rest)`, `rest`] mp_tac) >>
  simp[]
QED

Theorem asm_exec_staticcall_frame:
  asm_exec_staticcall (s with as_stack := top) = AsmOK t ==>
  asm_exec_staticcall (s with as_stack := top ++ rest) =
    AsmOK (t with as_stack := t.as_stack ++ rest)
Proof
  namedCases_on `top` ["", "a tail"] >> simp[asm_exec_staticcall_def] >>
  namedCases_on `tail` ["", "b tail2"] >> simp[asm_exec_staticcall_def] >>
  namedCases_on `tail2` ["", "c tail3"] >> simp[asm_exec_staticcall_def] >>
  namedCases_on `tail3` ["", "d tail4"] >> simp[asm_exec_staticcall_def] >>
  namedCases_on `tail4` ["", "e tail5"] >> simp[asm_exec_staticcall_def] >>
  Cases_on `tail5` >> simp[asm_exec_staticcall_def, asm_call_request_stack] >>
  strip_tac >> drule asm_consume_call_outcome_frame >>
  disch_then (qspecl_then [`a::b::c::d::e::h::(t' ++ rest)`, `rest`] mp_tac) >>
  simp[]
QED
