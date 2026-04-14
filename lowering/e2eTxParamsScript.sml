(*
 * txParams preservation through VFM execution.
 *
 * Every VFM monadic operation modifies only contexts/rollback/msdomain,
 * never txParams. Proved compositionally: leaf operations trivially
 * preserve txParams, and bind/handle preserve it when both components do.
 *
 * Split into multiple local blocks with ref cells to allow GC between phases.
 *)
Theory e2eTxParams
Ancestors vfmExecution

(* Ref cells to pass theorem lists between local blocks *)
val ptx_simps3_ref = ref ([] : thm list);
val ptx_handle_step_ref = ref TRUTH;
val ptx_bind_ref = ref TRUTH;
val ptx_ignore_bind_ref = ref TRUTH;
val ptx_handle_ref = ref TRUTH;
val ptx_domain_check_ref = ref TRUTH;
val ptx_copy_to_memory_some_ref = ref TRUTH;
val ptx_copy_to_memory_none_ref = ref TRUTH;
val ptx_get_return_data_check_ref = ref TRUTH;
val ptx_sstore_gas_ref = ref TRUTH;
val ptx_write_transient_storage_ref = ref TRUTH;

(* ================================================================ *)
(* Block 1: Compositional rules + leaf + mid-level operations       *)
(* ================================================================ *)
local
  val bind_def = DB.fetch "vfmExecution" "bind_def"
  val handle_def = DB.fetch "vfmExecution" "handle_def"
  val ignore_bind_def = DB.fetch "vfmExecution" "ignore_bind_def"
  val domain_check_def = DB.fetch "vfmExecution" "domain_check_def"

  val ptx_bind = prove(
    ``(!st:execution_state. (SND (ggg st)).txParams = st.txParams) /\
      (!xx (st:execution_state). (SND (fff xx st)).txParams = st.txParams) ==>
      !st:execution_state. (SND (monad_bind ggg fff st)).txParams = st.txParams``,
    rpt strip_tac >> rw[bind_def] >>
    Cases_on `ggg st` >> Cases_on `q` >> gvs[] >> metis_tac[pairTheory.SND])
  val ptx_ignore_bind = prove(
    ``(!st:execution_state. (SND (ggg st)).txParams = st.txParams) /\
      (!st:execution_state. (SND (fff st)).txParams = st.txParams) ==>
      !st:execution_state. (SND (monad_unitbind ggg fff st)).txParams = st.txParams``,
    rpt strip_tac >> rw[Once ignore_bind_def, bind_def] >>
    Cases_on `ggg st` >> Cases_on `q` >> gvs[] >> metis_tac[pairTheory.SND])
  val ptx_handle = prove(
    ``(!st:execution_state. (SND (fff st)).txParams = st.txParams) /\
      (!ee (st:execution_state). (SND (hhh ee st)).txParams = st.txParams) ==>
      !st:execution_state. (SND (handle fff hhh st)).txParams = st.txParams``,
    rpt strip_tac >> rw[handle_def] >>
    Cases_on `fff st` >> Cases_on `q` >> gvs[] >> metis_tac[pairTheory.SND])
  val ptx_domain_check = prove(
    ``(!st:execution_state. (SND (my_cont st)).txParams = st.txParams) ==>
      !st:execution_state. (SND (domain_check my_err my_chk my_add my_cont st)).txParams = st.txParams``,
    rw[domain_check_def] >> CASE_TAC >> gvs[] >>
    rpt ((irule ptx_bind >> rw[]) ORELSE (irule ptx_ignore_bind >> rw[])) >>
    rw[return_def, fail_def, set_domain_def])

  val return_def = DB.fetch "vfmExecution" "return_def"
  val fail_def = DB.fetch "vfmExecution" "fail_def"
  val finish_def = DB.fetch "vfmExecution" "finish_def"
  val revert_def = DB.fetch "vfmExecution" "revert_def"
  val assert_def = DB.fetch "vfmExecution" "assert_def"
  val reraise_def = DB.fetch "vfmExecution" "reraise_def"
  val get_current_context_def = DB.fetch "vfmExecution" "get_current_context_def"
  val set_current_context_def = DB.fetch "vfmExecution" "set_current_context_def"
  val update_accounts_def = DB.fetch "vfmExecution" "update_accounts_def"
  val get_accounts_def = DB.fetch "vfmExecution" "get_accounts_def"
  val get_rollback_def = DB.fetch "vfmExecution" "get_rollback_def"
  val set_rollback_def = DB.fetch "vfmExecution" "set_rollback_def"
  val get_tx_params_def = DB.fetch "vfmExecution" "get_tx_params_def"
  val push_context_def = DB.fetch "vfmExecution" "push_context_def"
  val pop_context_def = DB.fetch "vfmExecution" "pop_context_def"
  val set_domain_def = DB.fetch "vfmExecution" "set_domain_def"
  val add_to_delete_def = DB.fetch "vfmExecution" "add_to_delete_def"
  val set_original_def = DB.fetch "vfmExecution" "set_original_def"
  val get_gas_left_def = DB.fetch "vfmExecution" "get_gas_left_def"
  val get_tStorage_def = DB.fetch "vfmExecution" "get_tStorage_def"
  val set_tStorage_def = DB.fetch "vfmExecution" "set_tStorage_def"
  val get_num_contexts_def = DB.fetch "vfmExecution" "get_num_contexts_def"
  val get_original_def = DB.fetch "vfmExecution" "get_original_def"

  val ptx_leaf_defs = [return_def, fail_def, finish_def, revert_def,
    assert_def, reraise_def, get_current_context_def, set_current_context_def,
    update_accounts_def, get_accounts_def, get_rollback_def, set_rollback_def,
    get_tx_params_def, push_context_def, pop_context_def, set_domain_def,
    add_to_delete_def, set_original_def, get_gas_left_def, get_tStorage_def,
    set_tStorage_def, get_num_contexts_def, get_original_def]

  val ptx_leaf = rw ptx_leaf_defs >> simp[COND_RAND, COND_RATOR]
  val preserves_txParams_tac = rpt (
    (irule ptx_bind >> rw[]) ORELSE (irule ptx_ignore_bind >> rw[])
  )

  val consume_gas_def = DB.fetch "vfmExecution" "consume_gas_def"
  val inc_pc_def = DB.fetch "vfmExecution" "inc_pc_def"
  val push_stack_def = DB.fetch "vfmExecution" "push_stack_def"
  val pop_stack_def = DB.fetch "vfmExecution" "pop_stack_def"
  val write_memory_def = DB.fetch "vfmExecution" "write_memory_def"
  val expand_memory_def = DB.fetch "vfmExecution" "expand_memory_def"
  val read_memory_def = DB.fetch "vfmExecution" "read_memory_def"
  val set_return_data_def = DB.fetch "vfmExecution" "set_return_data_def"
  val get_return_data_def = DB.fetch "vfmExecution" "get_return_data_def"
  val get_output_to_def = DB.fetch "vfmExecution" "get_output_to_def"
  val unuse_gas_def = DB.fetch "vfmExecution" "unuse_gas_def"
  val push_logs_def = DB.fetch "vfmExecution" "push_logs_def"
  val update_gas_refund_def = DB.fetch "vfmExecution" "update_gas_refund_def"
  val memory_expansion_info_def = DB.fetch "vfmExecution" "memory_expansion_info_def"
  val access_address_def = DB.fetch "vfmExecution" "access_address_def"
  val access_slot_def = DB.fetch "vfmExecution" "access_slot_def"
  val ensure_storage_in_domain_def = DB.fetch "vfmExecution" "ensure_storage_in_domain_def"
  val pop_and_incorporate_context_def = DB.fetch "vfmExecution" "pop_and_incorporate_context_def"
  val get_call_data_def = DB.fetch "vfmExecution" "get_call_data_def"
  val get_callee_def = DB.fetch "vfmExecution" "get_callee_def"
  val get_caller_def = DB.fetch "vfmExecution" "get_caller_def"
  val get_value_def = DB.fetch "vfmExecution" "get_value_def"
  val get_static_def = DB.fetch "vfmExecution" "get_static_def"
  val write_storage_def = DB.fetch "vfmExecution" "write_storage_def"
  val assert_not_static_def = DB.fetch "vfmExecution" "assert_not_static_def"
  val abort_unuse_def = DB.fetch "vfmExecution" "abort_unuse_def"
  val abort_create_exists_def = DB.fetch "vfmExecution" "abort_create_exists_def"
  val abort_call_value_def = DB.fetch "vfmExecution" "abort_call_value_def"
  val set_jump_dest_def = DB.fetch "vfmExecution" "set_jump_dest_def"
  val get_code_def = DB.fetch "vfmExecution" "get_code_def"
  val get_current_code_def = DB.fetch "vfmExecution" "get_current_code_def"
  val get_return_data_check_def = DB.fetch "vfmExecution" "get_return_data_check_def"
  val write_transient_storage_def = DB.fetch "vfmExecution" "write_transient_storage_def"
  val step_sstore_gas_consumption_def = DB.fetch "vfmExecution" "step_sstore_gas_consumption_def"

  fun mk_ptx defs = rw defs >> preserves_txParams_tac >> ptx_leaf

  val ptx_mid = map (fn d => prove(
    ``!st:execution_state. (SND (^(d |> SPEC_ALL |> concl |> lhs |> strip_comb |> fst) st)).txParams = st.txParams``,
    mk_ptx [d]))
    [inc_pc_def, get_return_data_def, get_output_to_def,
     get_call_data_def, get_callee_def, get_caller_def,
     get_value_def, get_static_def, get_current_code_def]

  val ptx_consume_gas = prove(
    ``!n st:execution_state. (SND (consume_gas n st)).txParams = st.txParams``,
    mk_ptx [consume_gas_def])
  val ptx_set_return_data = prove(
    ``!d st:execution_state. (SND (set_return_data d st)).txParams = st.txParams``,
    mk_ptx [set_return_data_def])
  val ptx_unuse_gas = prove(
    ``!n st:execution_state. (SND (unuse_gas n st)).txParams = st.txParams``,
    mk_ptx [unuse_gas_def])
  val ptx_push_logs = prove(
    ``!l st:execution_state. (SND (push_logs l st)).txParams = st.txParams``,
    mk_ptx [push_logs_def])
  val ptx_expand_memory = prove(
    ``!n st:execution_state. (SND (expand_memory n st)).txParams = st.txParams``,
    mk_ptx [expand_memory_def])
  val ptx_get_code = prove(
    ``!a st:execution_state. (SND (get_code a st)).txParams = st.txParams``,
    mk_ptx [get_code_def])
  val ptx_set_jump_dest = prove(
    ``!d st:execution_state. (SND (set_jump_dest d st)).txParams = st.txParams``,
    mk_ptx [set_jump_dest_def])
  val ptx_push_stack = prove(
    ``!w st:execution_state. (SND (push_stack w st)).txParams = st.txParams``,
    mk_ptx [push_stack_def])
  val ptx_pop_stack = prove(
    ``!n st:execution_state. (SND (pop_stack n st)).txParams = st.txParams``,
    mk_ptx [pop_stack_def])
  val ptx_write_memory = prove(
    ``!o' d st:execution_state. (SND (write_memory o' d st)).txParams = st.txParams``,
    mk_ptx [write_memory_def])
  val ptx_read_memory = prove(
    ``!o' l st:execution_state. (SND (read_memory o' l st)).txParams = st.txParams``,
    mk_ptx [read_memory_def])
  val ptx_update_gas_refund = prove(
    ``!p st:execution_state. (SND (update_gas_refund p st)).txParams = st.txParams``,
    Cases >> mk_ptx [update_gas_refund_def])
  val ptx_get_gas_left = prove(
    ``!st:execution_state. (SND (get_gas_left st)).txParams = st.txParams``,
    mk_ptx [get_gas_left_def])
  val ptx_memory_expansion_info = prove(
    ``!o' sz st:execution_state. (SND (memory_expansion_info o' sz st)).txParams = st.txParams``,
    rw[memory_expansion_info_def, LET_THM] >> preserves_txParams_tac >> ptx_leaf)
  val ptx_access_address = prove(
    ``!a st:execution_state. (SND (access_address a st)).txParams = st.txParams``,
    rw[access_address_def] >> irule ptx_domain_check >> rw[LET_THM, return_def])
  val ptx_access_slot = prove(
    ``!a st:execution_state. (SND (access_slot a st)).txParams = st.txParams``,
    rw[access_slot_def] >> irule ptx_domain_check >> rw[LET_THM, return_def])
  val ptx_ensure_storage = prove(
    ``!a st:execution_state. (SND (ensure_storage_in_domain a st)).txParams = st.txParams``,
    rw[ensure_storage_in_domain_def] >> irule ptx_domain_check >> rw[return_def])
  val ptx_write_storage = prove(
    ``!a k v st:execution_state. (SND (write_storage a k v st)).txParams = st.txParams``,
    rw[write_storage_def, LET_THM] >> ptx_leaf)
  val ptx_assert_not_static = prove(
    ``!st:execution_state. (SND (assert_not_static st)).txParams = st.txParams``,
    rw[assert_not_static_def, get_static_def] >> preserves_txParams_tac >> ptx_leaf)
  val ptx_get_return_data_check = prove(
    ``!o' sz st:execution_state. (SND (get_return_data_check o' sz st)).txParams = st.txParams``,
    rw[get_return_data_check_def, get_return_data_def] >> preserves_txParams_tac >> ptx_leaf)
  val ptx_write_transient_storage = prove(
    ``!a k v st:execution_state. (SND (write_transient_storage a k v st)).txParams = st.txParams``,
    rw[write_transient_storage_def, LET_THM] >> preserves_txParams_tac >> ptx_leaf)
  val ptx_sstore_gas = prove(
    ``!a k v st:execution_state. (SND (step_sstore_gas_consumption a k v st)).txParams = st.txParams``,
    rw[step_sstore_gas_consumption_def, LET_THM, GSYM get_gas_left_def] >>
    preserves_txParams_tac >> simp[ptx_access_slot, ptx_update_gas_refund,
      ptx_consume_gas, ptx_get_gas_left] >> TRY ptx_leaf)

  val ptx_simps = ptx_mid @
    [ptx_consume_gas, ptx_set_return_data, ptx_unuse_gas,
     ptx_push_logs, ptx_expand_memory, ptx_get_code, ptx_set_jump_dest,
     ptx_push_stack, ptx_pop_stack, ptx_write_memory, ptx_read_memory,
     ptx_update_gas_refund, ptx_get_gas_left, ptx_memory_expansion_info,
     ptx_access_address, ptx_access_slot, ptx_ensure_storage,
     ptx_write_storage, ptx_assert_not_static, ptx_get_return_data_check,
     ptx_write_transient_storage, ptx_sstore_gas]

  fun ptx_auto simps = rpt (CHANGED_TAC (
    (irule ptx_bind >> rw[] >> TRY ptx_leaf) ORELSE
    (irule ptx_ignore_bind >> rw[] >> TRY ptx_leaf) ORELSE
    (irule ptx_handle >> rw[] >> TRY ptx_leaf) ORELSE
    (irule ptx_domain_check >> rw[] >> TRY ptx_leaf) ORELSE
    CHANGED_TAC (simp simps) ORELSE
    (CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)) ORELSE
    (IF_CASES_TAC >> gvs[] >> TRY ptx_leaf) ORELSE
    (BasicProvers.TOP_CASE_TAC >> gvs[] >> TRY ptx_leaf) ORELSE
    ptx_leaf))

  val ptx_pop_and_inc = prove(
    ``!b st:execution_state. (SND (pop_and_incorporate_context b st)).txParams = st.txParams``,
    rw[pop_and_incorporate_context_def, GSYM get_gas_left_def] >> ptx_auto ptx_simps)
  val ptx_abort_unuse = prove(
    ``!n st:execution_state. (SND (abort_unuse n st)).txParams = st.txParams``,
    rw[abort_unuse_def] >> ptx_auto ptx_simps)
  val ptx_abort_create = prove(
    ``!a st:execution_state. (SND (abort_create_exists a st)).txParams = st.txParams``,
    rw[abort_create_exists_def] >> ptx_auto ptx_simps)
  val ptx_abort_call = prove(
    ``!n st:execution_state. (SND (abort_call_value n st)).txParams = st.txParams``,
    rw[abort_call_value_def] >> ptx_auto ptx_simps)

  val ptx_simps2 = ptx_simps @
    [ptx_pop_and_inc, ptx_abort_unuse, ptx_abort_create, ptx_abort_call]

  val handle_exception_def = DB.fetch "vfmExecution" "handle_exception_def"
  val handle_create_def = DB.fetch "vfmExecution" "handle_create_def"
  val handle_step_def = DB.fetch "vfmExecution" "handle_step_def"

  val ptx_handle_exception = prove(
    ``!e st:execution_state. (SND (handle_exception e st)).txParams = st.txParams``,
    rw[handle_exception_def, LET_THM] >>
    preserves_txParams_tac >> simp ptx_simps2 >> TRY ptx_leaf >>
    BasicProvers.TOP_CASE_TAC >>
    preserves_txParams_tac >> simp ptx_simps2 >> TRY ptx_leaf >>
    preserves_txParams_tac >> simp ptx_simps2 >> TRY ptx_leaf)
  val ptx_handle_create = prove(
    ``!e st:execution_state. (SND (handle_create e st)).txParams = st.txParams``,
    rw[handle_create_def, LET_THM] >>
    preserves_txParams_tac >> simp ptx_simps2 >> TRY ptx_leaf >>
    BasicProvers.every_case_tac >> gvs[] >>
    preserves_txParams_tac >> simp ptx_simps2 >> TRY ptx_leaf)
  val ptx_handle_step = prove(
    ``!e st:execution_state. (SND (handle_step e st)).txParams = st.txParams``,
    rw[handle_step_def] >>
    BasicProvers.every_case_tac >> gvs[] >>
    TRY (ptx_auto (ptx_simps2 @ [ptx_handle_create, ptx_handle_exception])) >>
    TRY ptx_leaf)

  val ptx_simps3 = ptx_simps2 @
    [ptx_handle_exception, ptx_handle_create, ptx_handle_step]

  val copy_to_memory_def = DB.fetch "vfmExecution" "copy_to_memory_def"

  val ptx_copy_to_memory_some = prove(
    ``(!st:execution_state. (SND (gs' st)).txParams = st.txParams) ==>
      !g o' so' sz st:execution_state. (SND (copy_to_memory g o' so' sz (SOME gs') st)).txParams = st.txParams``,
    rw[copy_to_memory_def, LET_THM] >>
    CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >> ptx_auto ptx_simps3)
  val ptx_copy_to_memory_none = prove(
    ``!g o' so' sz st:execution_state. (SND (copy_to_memory g o' so' sz NONE st)).txParams = st.txParams``,
    rw[copy_to_memory_def, LET_THM] >>
    CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >> ptx_auto ptx_simps3)

in
  (* Store into ref cells for Block 2 *)
  val _ = ptx_simps3_ref := ptx_simps3
  val _ = ptx_handle_step_ref := ptx_handle_step
  val _ = ptx_bind_ref := ptx_bind
  val _ = ptx_ignore_bind_ref := ptx_ignore_bind
  val _ = ptx_handle_ref := ptx_handle
  val _ = ptx_domain_check_ref := ptx_domain_check
  val _ = ptx_copy_to_memory_some_ref := ptx_copy_to_memory_some
  val _ = ptx_copy_to_memory_none_ref := ptx_copy_to_memory_none
  val _ = ptx_get_return_data_check_ref := ptx_get_return_data_check
  val _ = ptx_sstore_gas_ref := ptx_sstore_gas
  val _ = ptx_write_transient_storage_ref := ptx_write_transient_storage
end (* Block 1 *)

(* ================================================================ *)
(* Block 2: step sub-operations + step_inst + final theorems        *)
(* ================================================================ *)
local
  (* Retrieve from ref cells *)
  val ptx_simps3 = !ptx_simps3_ref
  val ptx_handle_step = !ptx_handle_step_ref
  val ptx_bind = !ptx_bind_ref
  val ptx_ignore_bind = !ptx_ignore_bind_ref
  val ptx_handle = !ptx_handle_ref
  val ptx_domain_check = !ptx_domain_check_ref
  val ptx_copy_to_memory_some = !ptx_copy_to_memory_some_ref
  val ptx_copy_to_memory_none = !ptx_copy_to_memory_none_ref
  val ptx_get_return_data_check = !ptx_get_return_data_check_ref
  val ptx_sstore_gas = !ptx_sstore_gas_ref
  val ptx_write_transient_storage = !ptx_write_transient_storage_ref

  (* Rebuild leaf infrastructure *)
  val return_def = DB.fetch "vfmExecution" "return_def"
  val fail_def = DB.fetch "vfmExecution" "fail_def"
  val finish_def = DB.fetch "vfmExecution" "finish_def"
  val revert_def = DB.fetch "vfmExecution" "revert_def"
  val assert_def = DB.fetch "vfmExecution" "assert_def"
  val reraise_def = DB.fetch "vfmExecution" "reraise_def"
  val get_current_context_def = DB.fetch "vfmExecution" "get_current_context_def"
  val set_current_context_def = DB.fetch "vfmExecution" "set_current_context_def"
  val update_accounts_def = DB.fetch "vfmExecution" "update_accounts_def"
  val get_accounts_def = DB.fetch "vfmExecution" "get_accounts_def"
  val get_rollback_def = DB.fetch "vfmExecution" "get_rollback_def"
  val set_rollback_def = DB.fetch "vfmExecution" "set_rollback_def"
  val get_tx_params_def = DB.fetch "vfmExecution" "get_tx_params_def"
  val push_context_def = DB.fetch "vfmExecution" "push_context_def"
  val pop_context_def = DB.fetch "vfmExecution" "pop_context_def"
  val set_domain_def = DB.fetch "vfmExecution" "set_domain_def"
  val add_to_delete_def = DB.fetch "vfmExecution" "add_to_delete_def"
  val set_original_def = DB.fetch "vfmExecution" "set_original_def"
  val get_gas_left_def = DB.fetch "vfmExecution" "get_gas_left_def"
  val get_tStorage_def = DB.fetch "vfmExecution" "get_tStorage_def"
  val set_tStorage_def = DB.fetch "vfmExecution" "set_tStorage_def"
  val get_num_contexts_def = DB.fetch "vfmExecution" "get_num_contexts_def"
  val get_original_def = DB.fetch "vfmExecution" "get_original_def"

  val ptx_leaf_defs = [return_def, fail_def, finish_def, revert_def,
    assert_def, reraise_def, get_current_context_def, set_current_context_def,
    update_accounts_def, get_accounts_def, get_rollback_def, set_rollback_def,
    get_tx_params_def, push_context_def, pop_context_def, set_domain_def,
    add_to_delete_def, set_original_def, get_gas_left_def, get_tStorage_def,
    set_tStorage_def, get_num_contexts_def, get_original_def]

  val ptx_leaf = rw ptx_leaf_defs >> simp[COND_RAND, COND_RATOR]
  val preserves_txParams_tac = rpt (
    (irule ptx_bind >> rw[]) ORELSE (irule ptx_ignore_bind >> rw[])
  )

  fun ptx_auto simps = rpt (CHANGED_TAC (
    (irule ptx_bind >> rw[] >> TRY ptx_leaf) ORELSE
    (irule ptx_ignore_bind >> rw[] >> TRY ptx_leaf) ORELSE
    (irule ptx_handle >> rw[] >> TRY ptx_leaf) ORELSE
    (irule ptx_domain_check >> rw[] >> TRY ptx_leaf) ORELSE
    CHANGED_TAC (simp simps) ORELSE
    (CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)) ORELSE
    (IF_CASES_TAC >> gvs[] >> TRY ptx_leaf) ORELSE
    (BasicProvers.TOP_CASE_TAC >> gvs[] >> TRY ptx_leaf) ORELSE
    ptx_leaf))

  (* Fast decomposition: solves each leaf immediately after irule, avoiding
     exponential blowup from accumulating unsolved goals with large simp sets *)
  fun solve_leaf simps = TRY (simp simps) >> TRY ptx_leaf
  fun decomp simps = rpt (CHANGED_TAC (
    (irule ptx_bind >> rw[] >> TRY (conj_tac >- solve_leaf simps)) ORELSE
    (irule ptx_ignore_bind >> rw[] >> TRY (conj_tac >- solve_leaf simps)) ORELSE
    (irule ptx_handle >> rw[] >> TRY (conj_tac >- solve_leaf simps)) ORELSE
    (irule ptx_domain_check >> rw[] >> TRY (conj_tac >- solve_leaf simps)) ORELSE
    CHANGED_TAC (CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)) ORELSE
    (BasicProvers.TOP_CASE_TAC >> gvs[] >> TRY (solve_leaf simps)) ORELSE
    (IF_CASES_TAC >> gvs[] >> TRY (solve_leaf simps)) ORELSE
    (solve_leaf simps)
    ))

  val step_binop_def = DB.fetch "vfmExecution" "step_binop_def"
  val step_monop_def = DB.fetch "vfmExecution" "step_monop_def"
  val step_modop_def = DB.fetch "vfmExecution" "step_modop_def"
  val step_exp_def = DB.fetch "vfmExecution" "step_exp_def"
  val step_keccak256_def = DB.fetch "vfmExecution" "step_keccak256_def"
  val step_msgParams_def = DB.fetch "vfmExecution" "step_msgParams_def"
  val step_txParams_def = DB.fetch "vfmExecution" "step_txParams_def"
  val step_context_def = DB.fetch "vfmExecution" "step_context_def"
  val step_balance_def = DB.fetch "vfmExecution" "step_balance_def"
  val step_call_data_load_def = DB.fetch "vfmExecution" "step_call_data_load_def"
  val step_copy_to_memory_def = DB.fetch "vfmExecution" "step_copy_to_memory_def"
  val step_ext_code_size_def = DB.fetch "vfmExecution" "step_ext_code_size_def"
  val step_ext_code_copy_def = DB.fetch "vfmExecution" "step_ext_code_copy_def"
  val step_return_data_copy_def = DB.fetch "vfmExecution" "step_return_data_copy_def"
  val step_ext_code_hash_def = DB.fetch "vfmExecution" "step_ext_code_hash_def"
  val step_block_hash_def = DB.fetch "vfmExecution" "step_block_hash_def"
  val step_self_balance_def = DB.fetch "vfmExecution" "step_self_balance_def"
  val step_blob_hash_def = DB.fetch "vfmExecution" "step_blob_hash_def"
  val step_pop_def = DB.fetch "vfmExecution" "step_pop_def"
  val step_mload_def = DB.fetch "vfmExecution" "step_mload_def"
  val step_mstore_def = DB.fetch "vfmExecution" "step_mstore_def"
  val step_sload_def = DB.fetch "vfmExecution" "step_sload_def"
  val step_sstore_def = DB.fetch "vfmExecution" "step_sstore_def"
  val step_jump_def = DB.fetch "vfmExecution" "step_jump_def"
  val step_jumpi_def = DB.fetch "vfmExecution" "step_jumpi_def"
  val step_push_def = DB.fetch "vfmExecution" "step_push_def"
  val step_dup_def = DB.fetch "vfmExecution" "step_dup_def"
  val step_swap_def = DB.fetch "vfmExecution" "step_swap_def"
  val step_log_def = DB.fetch "vfmExecution" "step_log_def"
  val step_create_def = DB.fetch "vfmExecution" "step_create_def"
  val step_call_def = DB.fetch "vfmExecution" "step_call_def"
  val step_return_def = DB.fetch "vfmExecution" "step_return_def"
  val step_self_destruct_def = DB.fetch "vfmExecution" "step_self_destruct_def"
  val proceed_create_def = DB.fetch "vfmExecution" "proceed_create_def"
  val proceed_call_def = DB.fetch "vfmExecution" "proceed_call_def"
  val dispatch_precompiles_def = DB.fetch "vfmExecution" "dispatch_precompiles_def"
  val inc_pc_or_jump_def = DB.fetch "vfmExecution" "inc_pc_or_jump_def"
  val get_code_def = DB.fetch "vfmExecution" "get_code_def"

  val ptx_step_context = prove(
    ``!n f st:execution_state. (SND (step_context n f st)).txParams = st.txParams``,
    rw[step_context_def, LET_THM] >> ptx_auto ptx_simps3)
  val ptx_simps3a = ptx_simps3 @ [ptx_step_context]

  val ptx_step_ops = map (fn d => prove(
    ``!st:execution_state. (SND (^(d |> SPEC_ALL |> concl |> lhs |> strip_comb |> fst) st)).txParams = st.txParams``,
    rw[d, LET_THM] >> ptx_auto ptx_simps3a))
    [step_exp_def, step_keccak256_def, step_balance_def,
     step_call_data_load_def, step_ext_code_size_def, step_ext_code_hash_def,
     step_block_hash_def, step_self_balance_def, step_blob_hash_def,
     step_pop_def, step_mload_def, step_jump_def, step_jumpi_def]

  val ptx_step_binop = prove(
    ``!n f st:execution_state. (SND (step_binop n f st)).txParams = st.txParams``,
    rw[step_binop_def, LET_THM] >> ptx_auto ptx_simps3)
  val ptx_step_monop = prove(
    ``!n f st:execution_state. (SND (step_monop n f st)).txParams = st.txParams``,
    rw[step_monop_def, LET_THM] >> ptx_auto ptx_simps3)
  val ptx_step_modop = prove(
    ``!n f st:execution_state. (SND (step_modop n f st)).txParams = st.txParams``,
    rw[step_modop_def, LET_THM] >> ptx_auto ptx_simps3)
  val ptx_step_msgParams = prove(
    ``!n f st:execution_state. (SND (step_msgParams n f st)).txParams = st.txParams``,
    rw[step_msgParams_def, LET_THM] >> ptx_auto ptx_simps3a)
  val ptx_step_txParams = prove(
    ``!n f st:execution_state. (SND (step_txParams n f st)).txParams = st.txParams``,
    rw[step_txParams_def, LET_THM] >> ptx_auto ptx_simps3a)
  val ptx_step_mstore = prove(
    ``!op st:execution_state. (SND (step_mstore op st)).txParams = st.txParams``,
    rw[step_mstore_def, LET_THM] >> ptx_auto ptx_simps3)
  val ptx_step_sload = prove(
    ``!b st:execution_state. (SND (step_sload b st)).txParams = st.txParams``,
    rw[step_sload_def, LET_THM] >> ptx_auto ptx_simps3)
  val ptx_step_sstore = prove(
    ``!b st:execution_state. (SND (step_sstore b st)).txParams = st.txParams``,
    rw[step_sstore_def, LET_THM] >> ptx_auto (ptx_simps3 @ [ptx_sstore_gas, ptx_write_transient_storage]))
  val ptx_step_push = prove(
    ``!n ws st:execution_state. (SND (step_push n ws st)).txParams = st.txParams``,
    rw[step_push_def, LET_THM] >> ptx_auto ptx_simps3)
  val ptx_step_dup = prove(
    ``!n st:execution_state. (SND (step_dup n st)).txParams = st.txParams``,
    rw[step_dup_def, LET_THM] >> ptx_auto ptx_simps3)
  val ptx_step_swap = prove(
    ``!n st:execution_state. (SND (step_swap n st)).txParams = st.txParams``,
    rw[step_swap_def, LET_THM] >> ptx_auto ptx_simps3)
  val ptx_step_log = prove(
    ``!n st:execution_state. (SND (step_log n st)).txParams = st.txParams``,
    rw[step_log_def, LET_THM] >> ptx_auto ptx_simps3)
  val ptx_step_return = prove(
    ``!b st:execution_state. (SND (step_return b st)).txParams = st.txParams``,
    rw[step_return_def, LET_THM] >> ptx_auto ptx_simps3)
  val ptx_step_self_destruct = prove(
    ``!st:execution_state. (SND (step_self_destruct st)).txParams = st.txParams``,
    rw[step_self_destruct_def, LET_THM] >> ptx_auto ptx_simps3)
  val ptx_step_ext_code_copy = prove(
    ``!st:execution_state. (SND (step_ext_code_copy st)).txParams = st.txParams``,
    rw[step_ext_code_copy_def, LET_THM] >>
    ptx_auto ptx_simps3 >>
    irule ptx_copy_to_memory_some >> simp ptx_simps3 >>
    rw[get_code_def] >> preserves_txParams_tac >> ptx_leaf)
  val ptx_step_return_data_copy = prove(
    ``!st:execution_state. (SND (step_return_data_copy st)).txParams = st.txParams``,
    rw[step_return_data_copy_def, LET_THM] >>
    ptx_auto ptx_simps3 >>
    irule ptx_copy_to_memory_some >> simp (ptx_get_return_data_check :: ptx_simps3))

  val ptx_proceed_create = prove(
    ``!sa a v c g st:execution_state. (SND (proceed_create sa a v c g st)).txParams = st.txParams``,
    rw[proceed_create_def, LET_THM] >> ptx_auto ptx_simps3)

  val precompile_defs = List.mapPartial (fn n =>
    SOME (DB.fetch "vfmExecution" n) handle HOL_ERR _ => NONE)
    ["precompile_ecrecover_def", "precompile_sha2_256_def",
     "precompile_ripemd_160_def", "precompile_identity_def",
     "precompile_modexp_def", "precompile_ecadd_def",
     "precompile_ecmul_def", "precompile_ecpairing_def",
     "precompile_blake2f_def", "precompile_point_eval_def",
     "precompile_bls_g1add_def", "precompile_bls_g1msm_def",
     "precompile_bls_g2add_def", "precompile_bls_g2msm_def",
     "precompile_bls_pairing_def", "precompile_bls_map_fp_to_g1_def",
     "precompile_bls_map_fp2_to_g2_def", "precompile_p256verify_def"]

  val ptx_proceed_call = prove(
    ``!op s a v ao as' c sp ot st:execution_state. (SND (proceed_call op s a v ao as' c sp ot st)).txParams = st.txParams``,
    rw[proceed_call_def, LET_THM] >>
    decomp ptx_simps3 >>
    rw (dispatch_precompiles_def :: precompile_defs @ [LET_THM]) >>
    rpt IF_CASES_TAC >> gvs[] >>
    TRY (decomp ptx_simps3) >>
    TRY (BasicProvers.every_case_tac >> gvs[] >>
         TRY (decomp ptx_simps3) >> TRY ptx_leaf) >>
    TRY ptx_leaf)

  val ptx_simps4 = ptx_simps3a @ ptx_step_ops @
    [ptx_step_binop, ptx_step_monop, ptx_step_modop,
     ptx_step_msgParams, ptx_step_txParams,
     ptx_step_mstore, ptx_step_sload, ptx_step_sstore, ptx_step_push,
     ptx_step_dup, ptx_step_swap, ptx_step_log, ptx_step_return,
     ptx_step_self_destruct, ptx_step_ext_code_copy,
     ptx_step_return_data_copy, ptx_proceed_create, ptx_proceed_call]

  (* Use ptx_simps3 (38 rules) + proceed defs; decomp is fast because it
     solves each leaf immediately via conj_tac, avoiding goal accumulation *)
  val ptx_create_call_simps = ptx_simps3 @ [ptx_proceed_create, ptx_proceed_call]

  val ptx_step_create = prove(
    ``!b st:execution_state. (SND (step_create b st)).txParams = st.txParams``,
    rw[step_create_def, LET_THM] >>
    CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >> decomp ptx_create_call_simps)
  val ptx_step_call = prove(
    ``!op st:execution_state. (SND (step_call op st)).txParams = st.txParams``,
    rw[step_call_def, LET_THM] >>
    CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >> decomp ptx_create_call_simps)

  val ptx_simps5 = ptx_simps4 @ [ptx_step_create, ptx_step_call]

  val ptx_step_copy_to_memory_inline = prove(
    ``(!st:execution_state. (SND (gs' st)).txParams = st.txParams) ==>
      !op st:execution_state. (SND (step_copy_to_memory op (SOME gs') st)).txParams = st.txParams``,
    rw[step_copy_to_memory_def, LET_THM] >>
    ptx_auto ptx_simps3 >>
    irule ptx_copy_to_memory_some >> simp ptx_simps3)
  val ptx_step_copy_to_memory_none = prove(
    ``!op st:execution_state. (SND (step_copy_to_memory op NONE st)).txParams = st.txParams``,
    rw[step_copy_to_memory_def, LET_THM] >>
    ptx_auto ptx_simps3 >>
    simp[ptx_copy_to_memory_none])

  val ptx_simps6 = ptx_simps5 @ [ptx_step_copy_to_memory_none]

  val vfm_step_inst_def = DB.fetch "vfmExecution" "step_inst_def"
  val ptx_step_inst = prove(
    ``!op st:execution_state. (SND (step_inst op st)).txParams = st.txParams``,
    Cases >> rw[vfm_step_inst_def] >> simp ptx_simps6 >>
    TRY (decomp ptx_simps6) >>
    TRY (irule ptx_step_copy_to_memory_inline >> simp ptx_simps6) >>
    TRY ptx_leaf)

  val ptx_inc_pc_or_jump = prove(
    ``!op st:execution_state. (SND (inc_pc_or_jump op st)).txParams = st.txParams``,
    rw[inc_pc_or_jump_def, LET_THM] >> decomp ptx_simps6)

  val ptx_simps_all = ptx_simps6 @ [ptx_step_inst, ptx_inc_pc_or_jump]

  val step_def = DB.fetch "vfmExecution" "step_def"
in

Theorem step_preserves_txParams:
  !s. (SND (step s)).txParams = s.txParams
Proof
  gen_tac >> simp[step_def] >>
  irule ptx_handle >> rw[] >>
  simp[ptx_handle_step] >>
  decomp ptx_simps_all
QED

end (* Block 2 *)

(* Clear ref cells *)
val _ = ptx_simps3_ref := [];
val _ = ptx_handle_step_ref := TRUTH;
val _ = ptx_bind_ref := TRUTH;
val _ = ptx_ignore_bind_ref := TRUTH;
val _ = ptx_handle_ref := TRUTH;
val _ = ptx_domain_check_ref := TRUTH;
val _ = ptx_copy_to_memory_some_ref := TRUTH;
val _ = ptx_copy_to_memory_none_ref := TRUTH;
val _ = ptx_get_return_data_check_ref := TRUTH;
val _ = ptx_sstore_gas_ref := TRUTH;
val _ = ptx_write_transient_storage_ref := TRUTH;

Theorem run_preserves_txParams:
  !es rs. run es = SOME rs ==> (SND rs).txParams = es.txParams
Proof
  rpt strip_tac >> gvs[run_def] >>
  qsuff_tac
    `!s s'. OWHILE (ISL o FST) (step o SND) s = SOME s' ==>
            (SND s').txParams = (SND s).txParams`
  >- (disch_then drule >> simp[]) >>
  ho_match_mp_tac WhileTheory.OWHILE_IND >> rw[] >>
  Cases_on `step (SND s1)` >> gvs[] >>
  metis_tac[step_preserves_txParams, pairTheory.SND]
QED
