(*
 * A step that pushes no context, taken in a nested frame, is the same
 * step taken with the head context alone, up to the outer contexts: one
 * that continues keeps them below the new head, and one that ends the
 * frame (INR in the single-context run) returns to the parent as
 * frame_outcome says.
 *
 * TOP-LEVEL:
 *   step_transplant_continue - a continuing step
 *   step_transplant_end      - a step that ends the frame
 *)

Theory evmStepTransplant
Ancestors
  callTrace frameOutcome vfmExecution vfmExecutionProp vfmSameFrame
  vfmStepLength vfmHandleStep vfmContextLength vfmRunCall

Definition transplant_local_def:
  transplant_local (m : 'a execution) <=>
    !s c rb r t.
      s.contexts = [(c, rb)] /\ m s = (r, t) ==>
      ?c'. t.contexts = [(c', rb)] /\
        !rest. m (s with contexts := (c, rb) :: rest) =
          (r, t with contexts := (c', rb) :: rest)
End

Theorem transplant_local_return[simp]:
  transplant_local (return x)
Proof
  rw[transplant_local_def, return_def] >> gvs[]
QED

Theorem transplant_local_reraise[simp]:
  transplant_local (reraise e)
Proof
  rw[transplant_local_def, reraise_def] >> gvs[]
QED

Theorem transplant_local_fail[simp]:
  transplant_local (fail e)
Proof
  rw[transplant_local_def, fail_def] >> gvs[]
QED

Theorem transplant_local_bind[simp]:
  transplant_local m /\ (!x. transplant_local (f x)) ==>
  transplant_local (bind m f)
Proof
  rw[transplant_local_def, bind_def] >>
  Cases_on `m s` >> rename1 `m s = (res, u)` >>
  qpat_x_assum `!s c rb r t. _` (drule_all_then strip_assume_tac) >>
  Cases_on `res` >> gvs[]
QED

Theorem transplant_local_ignore_bind[simp]:
  transplant_local m /\ transplant_local n ==>
  transplant_local (ignore_bind m n)
Proof
  simp[ignore_bind_def] >> strip_tac >>
  irule transplant_local_bind >> simp[]
QED

Theorem transplant_local_finish[simp]:
  transplant_local finish
Proof
  rw[transplant_local_def, finish_def] >> gvs[]
QED

Theorem transplant_local_revert[simp]:
  transplant_local revert
Proof
  rw[transplant_local_def, revert_def] >> gvs[]
QED

Theorem transplant_local_assert[simp]:
  transplant_local (assert b e)
Proof
  Cases_on `b` >> rw[transplant_local_def, assert_def] >> gvs[]
QED

Theorem transplant_local_cond[simp]:
  (b ==> transplant_local m) /\ (~b ==> transplant_local n) ==>
  transplant_local (if b then m else n)
Proof
  Cases_on `b` >> simp[]
QED

Theorem transplant_local_get_current_context[simp]:
  transplant_local get_current_context
Proof
  rw[transplant_local_def, get_current_context_def, return_def] >> gvs[]
QED

Theorem transplant_local_set_current_context[simp]:
  transplant_local (set_current_context d)
Proof
  rw[transplant_local_def, set_current_context_def, return_def] >> gvs[]
QED

Theorem transplant_local_get_tx_params[simp]:
  transplant_local get_tx_params
Proof
  rw[transplant_local_def, get_tx_params_def, return_def] >> gvs[]
QED

Theorem transplant_local_get_rollback[simp]:
  transplant_local get_rollback
Proof
  rw[transplant_local_def, get_rollback_def, return_def] >> gvs[]
QED

Theorem transplant_local_set_rollback[simp]:
  transplant_local (set_rollback rb)
Proof
  rw[transplant_local_def, set_rollback_def, return_def] >> gvs[]
QED

Theorem transplant_local_get_accounts[simp]:
  transplant_local get_accounts
Proof
  rw[transplant_local_def, get_accounts_def, return_def] >> gvs[]
QED

Theorem transplant_local_update_accounts[simp]:
  transplant_local (update_accounts f)
Proof
  rw[transplant_local_def, update_accounts_def, return_def] >> gvs[]
QED

Theorem transplant_local_get_tStorage[simp]:
  transplant_local get_tStorage
Proof
  rw[transplant_local_def, get_tStorage_def, return_def] >> gvs[]
QED

Theorem transplant_local_set_tStorage[simp]:
  transplant_local (set_tStorage ts)
Proof
  rw[transplant_local_def, set_tStorage_def, return_def] >> gvs[]
QED

Theorem transplant_local_get_original[simp]:
  transplant_local get_original
Proof
  rw[transplant_local_def, get_original_def, return_def] >> gvs[]
QED

Theorem transplant_local_set_original[simp]:
  transplant_local (set_original a)
Proof
  rw[transplant_local_def, set_original_def, return_def] >> gvs[]
QED

Theorem transplant_local_add_to_delete[simp]:
  transplant_local (add_to_delete a)
Proof
  rw[transplant_local_def, add_to_delete_def, return_def] >> gvs[]
QED

Theorem transplant_local_set_domain[simp]:
  transplant_local (set_domain d)
Proof
  rw[transplant_local_def, set_domain_def, return_def] >> gvs[]
QED

Theorem transplant_local_domain_check:
  transplant_local cont ==>
  transplant_local (domain_check err check upd cont)
Proof
  rw[transplant_local_def] >>
  qpat_x_assum `domain_check _ _ _ _ _ = _` mp_tac >>
  Cases_on `s.msdomain` >>
  simp[domain_check_def, ignore_bind_def, bind_def,
       set_domain_def, return_def, fail_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  gvs[domain_check_def, ignore_bind_def, bind_def,
      set_domain_def, return_def, fail_def]
QED

Theorem transplant_local_access_address[simp]:
  transplant_local (access_address a)
Proof
  rewrite_tac[access_address_def] >>
  irule transplant_local_domain_check >>
  rw[transplant_local_def, return_def] >> gvs[]
QED

Theorem transplant_local_access_slot[simp]:
  transplant_local (access_slot a)
Proof
  rewrite_tac[access_slot_def] >>
  irule transplant_local_domain_check >>
  rw[transplant_local_def, return_def] >> gvs[]
QED

Theorem transplant_local_ensure_storage_in_domain[simp]:
  transplant_local (ensure_storage_in_domain a)
Proof
  simp[ensure_storage_in_domain_def, transplant_local_domain_check]
QED

Theorem transplant_local_option[simp]:
  (!x. transplant_local (f x)) /\ transplant_local n ==>
  transplant_local (case z of NONE => n | SOME x => f x)
Proof
  Cases_on `z` >> simp[]
QED

Theorem transplant_local_pair[simp]:
  (!x y. transplant_local (f x y)) ==>
  transplant_local (case z of (x, y) => f x y)
Proof
  Cases_on `z` >> simp[]
QED

Theorem transplant_local_get_gas_left[simp]:
  transplant_local get_gas_left
Proof
  simp[get_gas_left_def]
QED

Theorem transplant_local_get_callee[simp]:
  transplant_local get_callee
Proof
  simp[get_callee_def]
QED

Theorem transplant_local_get_caller[simp]:
  transplant_local get_caller
Proof
  simp[get_caller_def]
QED

Theorem transplant_local_get_value[simp]:
  transplant_local get_value
Proof
  simp[get_value_def]
QED

Theorem transplant_local_get_output_to[simp]:
  transplant_local get_output_to
Proof
  simp[get_output_to_def]
QED

Theorem transplant_local_get_return_data[simp]:
  transplant_local get_return_data
Proof
  simp[get_return_data_def]
QED

Theorem transplant_local_get_return_data_check[simp]:
  transplant_local (get_return_data_check off sz)
Proof
  simp[get_return_data_check_def]
QED

Theorem transplant_local_set_return_data[simp]:
  transplant_local (set_return_data bs)
Proof
  simp[set_return_data_def]
QED

Theorem transplant_local_get_static[simp]:
  transplant_local get_static
Proof
  simp[get_static_def]
QED

Theorem transplant_local_get_code[simp]:
  transplant_local (get_code a)
Proof
  simp[get_code_def]
QED

Theorem transplant_local_get_current_code[simp]:
  transplant_local get_current_code
Proof
  simp[get_current_code_def]
QED

Theorem transplant_local_get_call_data[simp]:
  transplant_local get_call_data
Proof
  simp[get_call_data_def]
QED

Theorem transplant_local_set_jump_dest[simp]:
  transplant_local (set_jump_dest dest)
Proof
  simp[set_jump_dest_def]
QED

Theorem transplant_local_push_logs[simp]:
  transplant_local (push_logs ls)
Proof
  simp[push_logs_def]
QED

Theorem transplant_local_update_gas_refund[simp]:
  transplant_local (update_gas_refund r)
Proof
  Cases_on `r` >> simp[update_gas_refund_def]
QED

Theorem transplant_local_consume_gas[simp]:
  transplant_local (consume_gas n)
Proof
  simp[consume_gas_def]
QED

Theorem transplant_local_pop_stack[simp]:
  transplant_local (pop_stack n)
Proof
  simp[pop_stack_def]
QED

Theorem transplant_local_push_stack[simp]:
  transplant_local (push_stack w)
Proof
  simp[push_stack_def]
QED

Theorem transplant_local_memory_expansion_info[simp]:
  transplant_local (memory_expansion_info off sz)
Proof
  simp[memory_expansion_info_def]
QED

Theorem transplant_local_expand_memory[simp]:
  transplant_local (expand_memory info)
Proof
  simp[expand_memory_def]
QED

Theorem transplant_local_read_memory[simp]:
  transplant_local (read_memory off sz)
Proof
  simp[read_memory_def]
QED

Theorem transplant_local_write_memory[simp]:
  transplant_local (write_memory off bs)
Proof
  simp[write_memory_def]
QED

Theorem transplant_local_write_storage[simp]:
  transplant_local (write_storage a k v)
Proof
  simp[write_storage_def]
QED

Theorem transplant_local_write_transient_storage[simp]:
  transplant_local (write_transient_storage a k v)
Proof
  simp[write_transient_storage_def]
QED

Theorem transplant_local_assert_not_static[simp]:
  transplant_local assert_not_static
Proof
  simp[assert_not_static_def]
QED

Theorem transplant_local_inc_pc[simp]:
  transplant_local inc_pc
Proof
  simp[inc_pc_def]
QED

Theorem transplant_local_copy_to_memory[simp]:
  (!f. src = SOME f ==> transplant_local f) ==>
  transplant_local (copy_to_memory gas off srcOff sz src)
Proof
  Cases_on `max_expansion_range (off,sz) (srcOff,sz)` >>
  Cases_on `src` >> simp[copy_to_memory_def] >>
  strip_tac >> rpt (FIRST [irule transplant_local_bind,
              irule transplant_local_ignore_bind] >> rw[])
QED

Theorem transplant_local_step_binop[simp]:
  transplant_local (step_binop op f)
Proof
  simp[step_binop_def]
QED

Theorem transplant_local_step_monop[simp]:
  transplant_local (step_monop op f)
Proof
  simp[step_monop_def]
QED

Theorem transplant_local_step_modop[simp]:
  transplant_local (step_modop op f)
Proof
  simp[step_modop_def]
QED

Theorem transplant_local_step_context[simp]:
  transplant_local (step_context op f)
Proof
  simp[step_context_def]
QED

Theorem transplant_local_step_msgParams[simp]:
  transplant_local (step_msgParams op f)
Proof
  simp[step_msgParams_def]
QED

Theorem transplant_local_step_txParams[simp]:
  transplant_local (step_txParams op f)
Proof
  simp[step_txParams_def]
QED

Theorem transplant_local_step_exp[simp]:
  transplant_local step_exp
Proof
  simp[step_exp_def]
QED

Theorem transplant_local_step_keccak256[simp]:
  transplant_local step_keccak256
Proof
  simp[step_keccak256_def] >> rpt (FIRST [irule transplant_local_bind,
              irule transplant_local_ignore_bind] >> rw[])
QED

Theorem transplant_local_step_sload[simp]:
  transplant_local (step_sload transient)
Proof
  simp[step_sload_def] >> rpt (FIRST [irule transplant_local_bind,
              irule transplant_local_ignore_bind] >> rw[])
QED

Theorem transplant_local_step_sstore_gas_consumption[simp]:
  transplant_local (step_sstore_gas_consumption a k v)
Proof
  simp[step_sstore_gas_consumption_def] >>
  rpt (FIRST [irule transplant_local_bind,
              irule transplant_local_ignore_bind] >> rw[])
QED

Theorem transplant_local_step_sstore[simp]:
  transplant_local (step_sstore transient)
Proof
  simp[step_sstore_def] >> rpt (FIRST [irule transplant_local_bind,
              irule transplant_local_ignore_bind] >> rw[])
QED

Theorem transplant_local_step_balance[simp]:
  transplant_local step_balance
Proof
  simp[step_balance_def] >> rpt (FIRST [irule transplant_local_bind,
              irule transplant_local_ignore_bind] >> rw[])
QED

Theorem transplant_local_step_call_data_load[simp]:
  transplant_local step_call_data_load
Proof
  simp[step_call_data_load_def]
QED

Theorem transplant_local_step_copy_to_memory[simp]:
  (!f. src = SOME f ==> transplant_local f) ==>
  transplant_local (step_copy_to_memory op src)
Proof
  strip_tac >> simp[step_copy_to_memory_def] >>
  irule transplant_local_bind >> simp[] >> gen_tac >>
  irule transplant_local_copy_to_memory >> first_assum ACCEPT_TAC
QED

Theorem transplant_local_step_return_data_copy[simp]:
  transplant_local step_return_data_copy
Proof
  simp[step_return_data_copy_def]
QED

Theorem transplant_local_step_ext_code_size[simp]:
  transplant_local step_ext_code_size
Proof
  simp[step_ext_code_size_def]
QED

Theorem transplant_local_step_ext_code_copy[simp]:
  transplant_local step_ext_code_copy
Proof
  simp[step_ext_code_copy_def]
QED

Theorem transplant_local_step_ext_code_hash[simp]:
  transplant_local step_ext_code_hash
Proof
  simp[step_ext_code_hash_def]
QED

Theorem transplant_local_step_block_hash[simp]:
  transplant_local step_block_hash
Proof
  simp[step_block_hash_def]
QED

Theorem transplant_local_step_blob_hash[simp]:
  transplant_local step_blob_hash
Proof
  simp[step_blob_hash_def]
QED

Theorem transplant_local_step_self_balance[simp]:
  transplant_local step_self_balance
Proof
  simp[step_self_balance_def]
QED

Theorem transplant_local_step_mload[simp]:
  transplant_local step_mload
Proof
  simp[step_mload_def] >>
  rpt (FIRST [irule transplant_local_bind,
              irule transplant_local_ignore_bind] >> rw[])
QED

Theorem transplant_local_step_mstore[simp]:
  transplant_local (step_mstore byte)
Proof
  simp[step_mstore_def]
QED

Theorem transplant_local_step_jump[simp]:
  transplant_local step_jump
Proof
  simp[step_jump_def]
QED

Theorem transplant_local_step_jumpi[simp]:
  transplant_local step_jumpi
Proof
  simp[step_jumpi_def]
QED

Theorem transplant_local_step_push[simp]:
  transplant_local (step_push n bs)
Proof
  simp[step_push_def]
QED

Theorem transplant_local_step_pop[simp]:
  transplant_local step_pop
Proof
  simp[step_pop_def]
QED

Theorem transplant_local_step_dup[simp]:
  transplant_local (step_dup n)
Proof
  simp[step_dup_def]
QED

Theorem transplant_local_step_swap[simp]:
  transplant_local (step_swap n)
Proof
  simp[step_swap_def]
QED

Theorem transplant_local_step_log[simp]:
  transplant_local (step_log n)
Proof
  simp[step_log_def] >>
  rpt (FIRST [irule transplant_local_bind,
              irule transplant_local_ignore_bind] >> rw[])
QED

Theorem transplant_local_step_return[simp]:
  transplant_local (step_return success)
Proof
  simp[step_return_def] >>
  rpt (FIRST [irule transplant_local_bind,
              irule transplant_local_ignore_bind] >> rw[])
QED

Theorem transplant_local_step_self_destruct[simp]:
  transplant_local step_self_destruct
Proof
  simp[step_self_destruct_def] >>
  rpt (FIRST [irule transplant_local_bind,
              irule transplant_local_ignore_bind] >> rw[])
QED

Theorem transplant_local_inc_pc_or_jump[simp]:
  transplant_local (inc_pc_or_jump op)
Proof
  simp[inc_pc_or_jump_def]
QED

Theorem transplant_local_step_inst:
  ~MEM op [Call; CallCode; DelegateCall; StaticCall; Create; Create2] ==>
  transplant_local (step_inst op)
Proof
  Cases_on `op` >> simp[step_inst_def]
QED

Definition transplant_raw_def:
  transplant_raw c =
    case FLOOKUP c.msgParams.parsed c.pc of
    | SOME op => ignore_bind (step_inst op) (inc_pc_or_jump op)
    | NONE => if LENGTH c.msgParams.code <= c.pc
              then step_inst Stop else step_inst Invalid
End

Theorem transplant_step_inner_eq:
  s.contexts = (c, rb) :: rest ==>
  step_inner s = transplant_raw c s
Proof
  simp[step_inner_def, transplant_raw_def, bind_def,
       get_current_context_def, return_def]
QED

Theorem transplant_lookup_allowed:
  wf_context c /\ FLOOKUP c.msgParams.parsed c.pc = SOME op /\
  (!op. next_opcode c = SOME op ==>
    ~MEM op [Call; CallCode; DelegateCall; StaticCall; Create; Create2]) ==>
  ~MEM op [Call; CallCode; DelegateCall; StaticCall; Create; Create2]
Proof
  strip_tac >>
  `c.pc < LENGTH c.msgParams.code` by
    (gvs[wf_context_def] >>
     drule FLOOKUP_parse_code_SOME_less_LENGTH >> simp[]) >>
  fs[next_opcode_def]
QED

Theorem transplant_raw_local:
  wf_context c /\
  (!op. next_opcode c = SOME op ==>
    ~MEM op [Call; CallCode; DelegateCall; StaticCall; Create; Create2]) ==>
  transplant_local (transplant_raw c)
Proof
  strip_tac >> rewrite_tac[transplant_raw_def] >>
  Cases_on `FLOOKUP c.msgParams.parsed c.pc` >> simp[]
  >- (Cases_on `LENGTH c.msgParams.code <= c.pc` >>
      simp[transplant_local_step_inst]) >>
  drule_all transplant_lookup_allowed >> strip_tac >>
  simp[transplant_local_step_inst]
QED

Theorem transplant_raw_boundary:
  s.contexts = [(c, rb)] /\ wf_context c /\
  (!op. next_opcode c = SOME op ==>
    ~MEM op [Call; CallCode; DelegateCall; StaticCall; Create; Create2]) /\
  step_inner s = (r, t) ==>
  ?d lgs. t.contexts = [(d, rb)] /\
    d.msgParams = c.msgParams /\ d.logs = c.logs ++ lgs /\
    wf_context d /\
    d.msgParams.gasLimit - d.gasUsed <= c.msgParams.gasLimit - c.gasUsed /\
    (!rest. step_inner (s with contexts := (c, rb) :: rest) =
      (r, t with contexts := (d, rb) :: rest))
Proof
  strip_tac >>
  `transplant_local (transplant_raw c)` by
    (irule transplant_raw_local >> simp[]) >>
  `transplant_raw c s = (r,t)` by
    (drule transplant_step_inner_eq >> simp[]) >>
  drule_all (iffLR transplant_local_def) >> strip_tac >>
  `same_frame_rel s t` by
    (metis_tac[same_frame_or_grow_eq_length,
       same_frame_or_grow_step_inner_named,
       listTheory.LENGTH, listTheory.NOT_CONS_NIL]) >>
  mp_tac vfmDecreasesGasTheory.decreases_gas_cred_step_inner >>
  rewrite_tac[vfmDecreasesGasTheory.decreases_gas_cred_def] >>
  disch_then (qspec_then `s` mp_tac) >>
  simp[vfmDecreasesGasTheory.contexts_weight_def, unused_gas_def,
       pairTheory.LEX_DEF] >>
  gvs[same_frame_rel_def, rich_listTheory.IS_PREFIX_APPEND] >>
  strip_tac >> conj_tac
  >- (Cases_on `ISL r` >> gvs[wf_context_def]) >>
  gen_tac >>
  `step_inner (s with contexts := (c,rb)::rest) =
   transplant_raw c (s with contexts := (c,rb)::rest)` by
    (irule transplant_step_inner_eq >> simp[]) >> simp[]
QED

Theorem transplant_handle_exception_memory_total[local]:
  s.contexts = (d, rb) :: (p, prb) :: rest /\
  d.msgParams.outputTo = Memory mr /\
  d.gasUsed <= d.msgParams.gasLimit /\
  d.msgParams.gasLimit - d.gasUsed <= p.gasUsed /\
  LENGTH p.stack < stack_limit ==>
  ?s'. handle_exception e s = (INL (), s') /\
       frame_outcome s (INL ()) s' e
         (if e = NONE \/ e = SOME Reverted then d.returnData else []) [] /\
       (e = NONE ==> s'.rollback = s.rollback)
Proof
  strip_tac >>
  Cases_on `e = NONE` >>
  Cases_on `e = SOME Reverted` >>
  gvs[handle_exception_def, bind_def, ignore_bind_def,
       get_gas_left_def, get_current_context_def, return_def,
       consume_gas_def, set_return_data_def, set_current_context_def,
       get_num_contexts_def, get_return_data_def, get_output_to_def,
       reraise_def, assert_def, fail_def,
       inc_pc_def, push_stack_def, write_memory_def,
       pop_and_incorporate_context_def, pop_context_def,
       set_rollback_def, unuse_gas_def,
       update_gas_refund_def, push_logs_def, frame_outcome_def]
QED

Theorem transplant_handle_exception_singleton[local]:
  s.contexts = [(d, rb)] /\ d.gasUsed <= d.msgParams.gasLimit ==>
  handle_exception e s =
    (INR e, if e = NONE \/ e = SOME Reverted then s else
       s with contexts :=
         [(d with <|gasUsed := d.msgParams.gasLimit; returnData := []|>, rb)])
Proof
  strip_tac >> Cases_on `e = NONE` >> Cases_on `e = SOME Reverted` >>
  gvs[handle_exception_def, bind_def, ignore_bind_def,
      get_gas_left_def, get_current_context_def, return_def,
      consume_gas_def, set_return_data_def, set_current_context_def,
      get_num_contexts_def, reraise_def, assert_def, fail_def]
QED

Theorem transplant_handler_wf_bounds[local]:
  wf_state s /\ s.contexts = (d, rb) :: (p, prb) :: rest ==>
  d.gasUsed <= d.msgParams.gasLimit /\
  d.msgParams.gasLimit - d.gasUsed <= p.gasUsed /\
  LENGTH p.stack < stack_limit
Proof
  simp[wf_state_def, wf_context_def, stack_room_ok_def,
       gas_stack_ok_def, unused_gas_def] >>
  strip_tac >> first_x_assum (qspec_then `0` mp_tac) >>
  gvs[wf_context_def]
QED

Theorem transplant_handle_step_memory[local]:
  s.contexts = (d, rb) :: rest /\
  d.msgParams.outputTo = Memory mr /\ ~vfm_abort e ==>
  handle_step e s = handle_exception e s
Proof
  strip_tac >>
  `s.contexts <> [] /\
   (!a. (FST (HD s.contexts)).msgParams.outputTo <> Code a)` by simp[] >>
  drule_all (INST_TYPE [alpha |-> ``:unit``]
    vfmStaticCallsTheory.handle_create_reraises) >>
  strip_tac >> simp[handle_step_def, handle_def, reraise_def]
QED

Theorem transplant_handle_step_boundary[local]:
  s.contexts = (d, rb) :: (p, prb) :: rest /\
  d.gasUsed <= d.msgParams.gasLimit /\
  d.msgParams.gasLimit - d.gasUsed <= p.gasUsed /\
  LENGTH p.stack < stack_limit /\
  d.msgParams.outputTo = Memory mr /\ ~vfm_abort e ==>
  ?d' t s'.
    handle_step e (s with contexts := [(d, rb)]) = (INR e, t) /\
    t.contexts = [(d', rb)] /\ d'.logs = d.logs /\
    handle_step e s = (INL (), s') /\
    frame_outcome s (INL ()) s' e d'.returnData [] /\
    (e = NONE ==> s'.rollback = t.rollback)
Proof
  strip_tac >>
  `handle_step e s = handle_exception e s` by
    (irule transplant_handle_step_memory >> simp[] >> metis_tac[]) >>
  `handle_step e (s with contexts := [(d, rb)]) =
   handle_exception e (s with contexts := [(d, rb)])` by
    (irule transplant_handle_step_memory >> simp[] >> metis_tac[]) >>
  drule_all transplant_handle_exception_memory_total >>
  disch_then (qspec_then `e` strip_assume_tac) >>
  `handle_exception e (s with contexts := [(d, rb)]) =
     (INR e, if e = NONE \/ e = SOME Reverted then
       s with contexts := [(d, rb)] else
       (s with contexts := [(d, rb)]) with contexts :=
         [(d with <|gasUsed := d.msgParams.gasLimit; returnData := []|>, rb)])` by
    (irule transplant_handle_exception_singleton >> simp[]) >>
  Cases_on `e = NONE \/ e = SOME Reverted` >> gvs[]
QED

Theorem transplant_finalization_boundary:
  es.contexts = (c,rb)::rest /\ rest <> [] /\ wf_state es /\
  u.contexts = [(d,rb)] /\ u.txParams = es.txParams /\
  d.msgParams = c.msgParams /\ d.logs = c.logs ++ lgs /\
  wf_context d /\
  d.msgParams.gasLimit - d.gasUsed <= c.msgParams.gasLimit - c.gasUsed /\
  (!a. c.msgParams.outputTo <> Code a) /\ ~vfm_abort e ==>
  ?d' t es'.
    handle_step e u = (INR e,t) /\ t.contexts = [(d',rb)] /\
    d'.logs = c.logs ++ lgs /\
    handle_step e (u with contexts := (d,rb)::rest) = (INL (),es') /\
    frame_outcome es (INL ()) es' e d'.returnData lgs /\
    (e = NONE ==> es'.rollback = t.rollback)
Proof
  strip_tac >> Cases_on `rest` >> gvs[] >>
  PairCases_on `h` >>
  `c.gasUsed <= c.msgParams.gasLimit /\
   c.msgParams.gasLimit - c.gasUsed <= h0.gasUsed /\
   LENGTH h0.stack < stack_limit` by
    (irule transplant_handler_wf_bounds >> simp[] >> metis_tac[]) >>
  Cases_on `c.msgParams.outputTo` >> gvs[] >>
  `d.gasUsed <= d.msgParams.gasLimit` by fs[wf_context_def] >>
  `d.msgParams.gasLimit - d.gasUsed <= h0.gasUsed` by simp[] >>
  `(u with contexts := (d,rb)::(h0,h1)::t).contexts =
   (d,rb)::(h0,h1)::t` by simp[] >>
  drule transplant_handle_step_boundary >> simp[] >>
  disch_then (qspec_then `e` mp_tac) >> simp[] >> strip_tac >>
  rename1 `handle_step e (u with contexts := [(d,rb)]) = (INR e,v)` >>
  rename1 `v.contexts = [(head,rb)]` >>
  rename1 `handle_step e (u with contexts := (d,rb)::(h0,h1)::t) = (INL (),w)` >>
  qexistsl_tac [`head`, `v`, `w`] >> simp[] >>
  gvs[frame_outcome_def] >>
  `u with contexts := [(d,rb)] = u` by
    (simp[vfmContextTheory.execution_state_component_equality]) >> metis_tac[]
QED

Theorem transplant_step_eq:
  step s = handle step_inner handle_step s
Proof
  simp[step_def, step_inner_def]
QED

Theorem transplant_singleton_handler_not_inl[local]:
  s.contexts = [(d,rb)] ==> handle_step e s <> (INL (),t)
Proof
  strip_tac >> strip_tac >>
  `LENGTH s.contexts = 1` by simp[] >>
  drule_all handle_step_preserves_length_1 >> strip_tac >>
  `s.contexts <> []` by simp[] >>
  drule_all handle_step_inl_pops >> simp[]
QED

Theorem step_transplant_continue:
  es.contexts = (c, rb) :: rest /\ rest <> [] /\ wf_state es /\
  (!op. next_opcode c = SOME op ==>
        ~MEM op [Call; CallCode; DelegateCall; StaticCall; Create; Create2]) /\
  step (es with contexts := [(c, rb)]) = (INL (), t) ==>
  ?c'. t.contexts = [(c', rb)] /\
       step es = (INL (), t with contexts := (c', rb) :: rest)
Proof
  strip_tac >>
  `wf_context c` by gvs[wf_state_def] >>
  Cases_on `step_inner (es with contexts := [(c,rb)])` >>
  rename1 `step_inner (es with contexts := [(c,rb)]) = (res,u)` >>
  drule_at (Pat `step_inner _ = _`) transplant_raw_boundary >> simp[] >>
  (impl_tac >- gvs[]) >> strip_tac >>
  Cases_on `res` >>
  gvs[transplant_step_eq, handle_def]
  >- (rename1 `u.contexts = [(d,rb)]` >>
      `es with contexts := (c,rb)::rest = es` by
        simp[vfmContextTheory.execution_state_component_equality] >>
      first_x_assum (qspec_then `rest` mp_tac) >> simp[]) >>
  metis_tac[transplant_singleton_handler_not_inl]
QED

(* c' is the head as the single-context run leaves it; the frame's
   logs grow from c.logs by lgs. *)
Theorem step_transplant_end:
  es.contexts = (c, rb) :: rest /\ rest <> [] /\ wf_state es /\
  (!a. c.msgParams.outputTo <> Code a) /\
  (!op. next_opcode c = SOME op ==>
        ~MEM op [Call; CallCode; DelegateCall; StaticCall; Create; Create2]) /\
  step (es with contexts := [(c, rb)]) = (INR e, t) /\ ~vfm_abort e ==>
  ?c' rb' es' lgs.
    t.contexts = [(c', rb')] /\ c'.logs = c.logs ++ lgs /\
    step es = (INL (), es') /\
    frame_outcome es (INL ()) es' e c'.returnData lgs /\
    (e = NONE ==> es'.rollback = t.rollback)
Proof
  strip_tac >>
  `wf_context c` by gvs[wf_state_def] >>
  Cases_on `step_inner (es with contexts := [(c,rb)])` >>
  rename1 `step_inner (es with contexts := [(c,rb)]) = (res,u)` >>
  drule_at (Pat `step_inner _ = _`) transplant_raw_boundary >> simp[] >>
  (impl_tac >- gvs[]) >> strip_tac >>
  Cases_on `res` >> gvs[transplant_step_eq, handle_def] >>
  rename1 `handle_step err u = (INR e,t)` >>
  `~vfm_abort err` by
    (Cases_on `vfm_abort err` >>
     gvs[handle_step_def, reraise_def]) >>
  `step_inner (es with contexts := [(c,rb)]) = (INR err,u)` by
    (first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `same_frame_rel (es with contexts := [(c,rb)]) u` by
    (drule_at (Pat `m s = _`) same_frame_or_grow_eq_length >> simp[]) >>
  `u.txParams = es.txParams` by fs[same_frame_rel_def] >>
  drule_at (Pat `wf_state _`) transplant_finalization_boundary >>
  simp[] >>
  disch_then (qspecl_then [`u`, `lgs`, `err`, `d`] mp_tac) >>
  simp[] >> strip_tac >>
  `es with contexts := (c,rb)::rest = es` by
    simp[vfmContextTheory.execution_state_component_equality] >>
  gvs[] >>
  qpat_x_assum `!rest'. step_inner _ = _`
    (qspec_then `rest` mp_tac) >> simp[] >>
  strip_tac >> simp[] >> metis_tac[]
QED
