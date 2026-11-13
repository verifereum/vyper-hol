(* The transaction code is observed only by the self-code slice boundary.
   These equations keep record plumbing out of interpreter congruence proofs. *)
Theory selfCodeFreeContext
Ancestors
  vyperInterpreter vyperContext vyperState vyperEvmBoundary vyperCreate

Theorem get_module_code_txn_code[simp]:
  get_module_code (cx with txn := (cx.txn with code := c)) sid =
  get_module_code cx sid
Proof simp[get_module_code_def]
QED

Theorem get_self_code_txn_code[simp]:
  get_self_code (cx with txn := (cx.txn with code := c)) = get_self_code cx
Proof simp[get_self_code_def]
QED

Theorem get_tenv_txn_code[simp]:
  get_tenv (cx with txn := (cx.txn with code := c)) = get_tenv cx
Proof simp[get_tenv_def]
QED

Theorem current_module_txn_code[simp]:
  current_module (cx with txn := (cx.txn with code := c)) = current_module cx
Proof simp[current_module_def]
QED

Theorem txn_code_stk_commute:
  (cx with txn := (cx.txn with code := c)) with stk := stk =
  (cx with stk := stk) with txn := (cx.txn with code := c)
Proof simp[evaluation_context_component_equality]
QED

Theorem push_function_txn_code:
  push_function fn sc (cx with txn := (cx.txn with code := c)) st =
  (INL ((cx with stk updated_by CONS fn) with
          txn := (cx.txn with code := c)), st with scopes := [sc])
Proof
  simp[push_function_def, return_def, txn_code_stk_commute]
QED

Theorem evaluate_block_hash_txn_code[simp]:
  evaluate_block_hash (tx with code := c) n = evaluate_block_hash tx n
Proof simp[evaluate_block_hash_def]
QED

Theorem evaluate_blob_hash_txn_code[simp]:
  evaluate_blob_hash (tx with code := c) n = evaluate_blob_hash tx n
Proof simp[evaluate_blob_hash_def]
QED

Theorem evaluate_type_builtin_case[local] = oneline evaluate_type_builtin_def;

Theorem evaluate_type_builtin_txn_code[simp]:
  evaluate_type_builtin (cx with txn := (cx.txn with code := c)) tb ty tys vs =
  evaluate_type_builtin cx tb ty tys vs
Proof
  simp[evaluate_type_builtin_case]
QED

Theorem evaluate_builtin_txn_code[simp]:
  evaluate_builtin (cx with txn := (cx.txn with code := c)) acc ty bt tys vs =
  evaluate_builtin cx acc ty bt tys vs
Proof Cases_on `bt` >> simp[evaluate_builtin_def]
QED

Theorem evaluate_code_source_txn_code:
  ~self ==>
  evaluate_code_source (cx with txn := (cx.txn with code := c)) acc self ty aty vs =
  evaluate_code_source cx acc self ty aty vs
Proof simp[evaluate_code_source_def]
QED

Theorem check_not_static_txn_code[simp]:
  check_not_static (cx with txn := (cx.txn with code := c)) = check_not_static cx
Proof simp[check_not_static_def]
QED

Theorem lock_if_nr_txn_code[simp]:
  lock_if_nr (cx with txn := (cx.txn with code := c)) nr view =
  lock_if_nr cx nr view
Proof simp[lock_if_nr_def]
QED

Theorem unlock_if_nr_txn_code[simp]:
  unlock_if_nr (cx with txn := (cx.txn with code := c)) nr view =
  unlock_if_nr cx nr view
Proof simp[unlock_if_nr_def]
QED

Theorem subscript_reads_base_txn_code[simp]:
  subscript_reads_base (cx with txn := (cx.txn with code := c)) e1 e2 =
  subscript_reads_base cx e1 e2
Proof simp[subscript_reads_base_def]
QED

Theorem get_address_immutables_txn_code[simp]:
  get_address_immutables (cx with txn := (cx.txn with code := c)) =
  get_address_immutables cx
Proof simp[FUN_EQ_THM, get_address_immutables_def]
QED

Theorem get_immutables_txn_code[simp]:
  get_immutables (cx with txn := (cx.txn with code := c)) src = get_immutables cx src
Proof simp[get_immutables_def]
QED

Theorem lookup_var_slot_from_layout_txn_code[simp]:
  lookup_var_slot_from_layout (cx with txn := (cx.txn with code := c)) tr src id =
  lookup_var_slot_from_layout cx tr src id
Proof simp[lookup_var_slot_from_layout_def]
QED

Theorem get_storage_backend_txn_code[simp]:
  get_storage_backend (cx with txn := (cx.txn with code := c)) tr =
  get_storage_backend cx tr
Proof Cases_on `tr` >> simp[get_storage_backend_def]
QED

Theorem set_storage_backend_txn_code[simp]:
  set_storage_backend (cx with txn := (cx.txn with code := c)) tr storage =
  set_storage_backend cx tr storage
Proof Cases_on `tr` >> simp[set_storage_backend_def]
QED

Theorem read_storage_slot_txn_code[simp]:
  read_storage_slot (cx with txn := (cx.txn with code := c)) tr slot tv =
  read_storage_slot cx tr slot tv
Proof simp[read_storage_slot_def]
QED

Theorem write_storage_slot_txn_code[simp]:
  write_storage_slot (cx with txn := (cx.txn with code := c)) tr slot tv v =
  write_storage_slot cx tr slot tv v
Proof simp[write_storage_slot_def]
QED

Theorem set_address_immutables_txn_code[simp]:
  set_address_immutables (cx with txn := (cx.txn with code := c)) imms =
  set_address_immutables cx imms
Proof simp[FUN_EQ_THM, set_address_immutables_def]
QED

Theorem set_immutable_txn_code[simp]:
  set_immutable (cx with txn := (cx.txn with code := c)) src id tv v =
  set_immutable cx src id tv v
Proof simp[set_immutable_def]
QED

Theorem lookup_global_txn_code[simp]:
  lookup_global (cx with txn := (cx.txn with code := c)) src id =
  lookup_global cx src id
Proof simp[lookup_global_def]
QED

Theorem lookup_flag_mem_txn_code[simp]:
  lookup_flag_mem (cx with txn := (cx.txn with code := c)) nsid id =
  lookup_flag_mem cx nsid id
Proof Cases_on `nsid` >> simp[lookup_flag_mem_def]
QED

Theorem read_place_txn_code[simp]:
  read_place (cx with txn := (cx.txn with code := c)) p = read_place cx p
Proof Cases_on `p` >> simp[read_place_def]
QED

Theorem write_place_txn_code[simp]:
  write_place (cx with txn := (cx.txn with code := c)) p v = write_place cx p v
Proof Cases_on `p` >> simp[write_place_def]
QED

Theorem place_type_value_txn_code[simp]:
  place_type_value (cx with txn := (cx.txn with code := c)) p = place_type_value cx p
Proof Cases_on `p` >> simp[place_type_value_def]
QED

Theorem read_result_txn_code[simp]:
  read_result (cx with txn := (cx.txn with code := c)) r = read_result cx r
Proof Cases_on `r` >> simp[read_result_def]
QED

Theorem read_results_txn_code[simp]:
  !rs. read_results (cx with txn := (cx.txn with code := c)) rs = read_results cx rs
Proof Induct >> simp[read_results_def]
QED

Theorem conditional_result_txn_code[simp]:
  conditional_result (cx with txn := (cx.txn with code := c)) r = conditional_result cx r
Proof Cases_on `r` >> simp[conditional_result_def]
QED

Theorem vyper_to_tx_params_txn_code[simp]:
  vyper_to_tx_params (tx with code := c) = vyper_to_tx_params tx
Proof simp[vyper_to_tx_params_def]
QED

Theorem send_call_value_txn_code[simp]:
  send_call_value mut (cx with txn := (cx.txn with code := c)) = send_call_value mut cx
Proof simp[send_call_value_def]
QED

Theorem result_array_length_case[local] = oneline result_array_length_def;

Theorem result_array_length_txn_code[simp]:
  result_array_length (cx with txn := (cx.txn with code := c)) r = result_array_length cx r
Proof simp[result_array_length_case]
QED

Theorem resolve_array_element_txn_code[simp]:
  !cx tr slot tv path.
  resolve_array_element (cx with txn := (cx.txn with code := c)) tr slot tv path =
  resolve_array_element cx tr slot tv path
Proof
  recInduct resolve_array_element_ind >>
  rpt strip_tac >> gvs[] >> simp[Once resolve_array_element_def] >>
  simp[Once resolve_array_element_def]
QED

Theorem extend_storage_place_case[local] = oneline extend_storage_place_def;

Theorem extend_storage_place_txn_code[simp]:
  extend_storage_place (cx with txn := (cx.txn with code := c)) tr slot tv sb =
  extend_storage_place cx tr slot tv sb
Proof simp[extend_storage_place_case]
QED

Theorem extend_place_case[local] = oneline extend_place_def;

Theorem extend_place_txn_code[simp]:
  extend_place (cx with txn := (cx.txn with code := c)) r sb = extend_place cx r sb
Proof simp[extend_place_case]
QED

Theorem select_result_txn_code[simp]:
  select_result (cx with txn := (cx.txn with code := c)) ty r sb = select_result cx ty r sb
Proof Cases_on `r` >> simp[select_result_def]
QED

Theorem pop_place_case[local] = oneline pop_place_def;

Theorem pop_place_txn_code[simp]:
  pop_place (cx with txn := (cx.txn with code := c)) p = pop_place cx p
Proof simp[pop_place_case]
QED

Theorem append_place_case[local] = oneline append_place_def;

Theorem append_place_txn_code[simp]:
  append_place (cx with txn := (cx.txn with code := c)) p v = append_place cx p v
Proof simp[append_place_case]
QED

Theorem switch_BoolV_txn_code[simp]:
  switch_BoolV (cx with txn := (cx.txn with code := c)) r yes no =
  switch_BoolV cx r yes no
Proof simp[switch_BoolV_def]
QED

Theorem array_iterator_results_txn_code[simp]:
  array_iterator_results (cx with txn := (cx.txn with code := c)) ty r =
  array_iterator_results cx ty r
Proof simp[array_iterator_results_def]
QED

Theorem frame_call_value_txn_code[simp]:
  frame_call_value (cx with txn := (cx.txn with code := c)) vo = frame_call_value cx vo
Proof simp[frame_call_value_def]
QED

Theorem make_delegate_call_state_txn_code[simp]:
  make_delegate_call_state (cx with txn := (cx.txn with code := c)) a data gas acc ts =
  make_delegate_call_state cx a data gas acc ts
Proof simp[make_delegate_call_state_def]
QED

Theorem run_delegate_call_txn_code[simp]:
  run_delegate_call (cx with txn := (cx.txn with code := c)) a data gas acc ts =
  run_delegate_call cx a data gas acc ts
Proof simp[run_delegate_call_def]
QED

Theorem run_raw_call_txn_code[simp]:
  run_raw_call (cx with txn := (cx.txn with code := c)) flags a data value gas acc ts =
  run_raw_call cx flags a data value gas acc ts
Proof simp[run_raw_call_def]
QED

Theorem eval_raw_call_txn_code[simp]:
  eval_raw_call (cx with txn := (cx.txn with code := c)) flags a data value gas =
  eval_raw_call cx flags a data value gas
Proof simp[eval_raw_call_def]
QED

Theorem eval_ext_call_effects_txn_code[simp]:
  eval_ext_call_effects (cx with txn := (cx.txn with code := c)) a data value gas =
  eval_ext_call_effects cx a data value gas
Proof simp[FUN_EQ_THM, eval_ext_call_effects_def]
QED

Theorem eval_ext_call_txn_code[simp]:
  eval_ext_call (cx with txn := (cx.txn with code := c)) static skip sig opts vs =
  eval_ext_call cx static skip sig opts vs
Proof
  PairCases_on `sig` >> Cases_on `vs` >> simp[eval_ext_call_def]
QED

Theorem eval_send_case[local] = oneline eval_send_def;


Theorem eval_send_txn_code[simp]:
  eval_send (cx with txn := (cx.txn with code := c)) gas vs = eval_send cx gas vs
Proof simp[eval_send_case]
QED

Theorem eval_create_txn_code[simp]:
  eval_create (cx with txn := (cx.txn with code := c)) kind salt rof tys vs bsize =
  eval_create cx kind salt rof tys vs bsize
Proof simp[eval_create_def]
QED
