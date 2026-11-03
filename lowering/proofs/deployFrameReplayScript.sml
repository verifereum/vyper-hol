(* Replay after intrinsic charging; normal root halt keeps its real handler. *)
Theory deployFrameReplay
Ancestors
  vfmExecution vfmExecutionProp vfmContext vfmState callTrace frameOutcome
  e2eDeployFrame evmStepSim list rich_list pair

Definition shadow_root_contexts_def:
  shadow_root_contexts [] = [] /\
  shadow_root_contexts ((ctxt, rb)::rest) =
    if rest = [] then
      [(ctxt with msgParams updated_by
          (\mp. mp with outputTo := Memory <| offset := 0; size := 0 |>), rb)]
    else (ctxt, rb)::shadow_root_contexts rest
End

Definition shadow_root_def:
  shadow_root es = es with contexts := shadow_root_contexts es.contexts
End

Definition root_output_to_def:
  root_output_to es = (FST (LAST es.contexts)).msgParams.outputTo
End

Theorem shadow_root_contexts_cons:
  rest <> [] ==>
  shadow_root_contexts ((ctxt, rb)::rest) =
    (ctxt, rb)::shadow_root_contexts rest
Proof
  simp[shadow_root_contexts_def]
QED

Theorem shadow_root_contexts_length:
  !cs. LENGTH (shadow_root_contexts cs) = LENGTH cs
Proof
  Induct >> simp[shadow_root_contexts_def] >>
  Cases_on `h` >> simp[shadow_root_contexts_def] >>
  Cases_on `cs = []` >> gvs[]
QED

Theorem shadow_root_contexts_nil:
  !cs. shadow_root_contexts cs = [] <=> cs = []
Proof
  metis_tac[shadow_root_contexts_length, LENGTH_NIL,
            shadow_root_contexts_def]
QED

Definition root_replay_rel_def:
  root_replay_rel d s t <=>
    s.contexts <> [] /\ root_output_to s = d /\ shadow_root s = t
End

Definition root_replay_judgement_def:
  root_replay_judgement d P Q f g <=>
    !s t. P s t ==>
      case (f s, g t) of
        ((INL x, s'), (INL y, t')) => Q x s' y t'
      | ((INR e, s'), (INR e', t')) =>
          e = e' /\ root_replay_rel d s' t'
      | _ => F
End

Theorem root_replay_return:
  (!s t. P s t ==> Q x s y t) ==>
  root_replay_judgement d P Q (return x) (return y)
Proof
  simp[root_replay_judgement_def, return_def]
QED

Theorem root_replay_reraise:
  (!s t. P s t ==> root_replay_rel d s t) ==>
  root_replay_judgement d P Q (reraise e) (reraise e)
Proof
  simp[root_replay_judgement_def, reraise_def]
QED

Theorem root_replay_bind:
  root_replay_judgement d P Q f g /\
  (!x y. root_replay_judgement d (\s t. Q x s y t) V (k x) (l y)) ==>
  root_replay_judgement d P V (bind f k) (bind g l)
Proof
  simp[root_replay_judgement_def] >> rpt strip_tac >>
  first_x_assum drule >>
  Cases_on `f s` >> Cases_on `g t` >>
  Cases_on `q` >> Cases_on `q'` >>
  simp[bind_def] >> metis_tac[]
QED

Theorem root_replay_consequence:
  root_replay_judgement d P Q f g /\
  (!s t. P' s t ==> P s t) /\
  (!x s y t. Q x s y t ==> Q' x s y t) ==>
  root_replay_judgement d P' Q' f g
Proof
  simp[root_replay_judgement_def] >> rpt strip_tac >>
  qpat_x_assum `!s t. P s t ==> _`
    (qspecl_then [`s`, `t`] mp_tac) >>
  Cases_on `f s` >> Cases_on `g t` >>
  Cases_on `q` >> Cases_on `q'` >> simp[] >> metis_tac[]
QED

Theorem root_replay_success_frame:
  root_replay_judgement d P Q f g /\
  (!s t. P s t ==> invariant_ok s) /\
  (!s x s'. invariant_ok s /\ f s = (INL x, s') ==> invariant_ok s') ==>
  root_replay_judgement d P (\x s y t. Q x s y t /\ invariant_ok s) f g
Proof
  strip_tac >> pure_rewrite_tac[root_replay_judgement_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `root_replay_judgement _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[root_replay_judgement_def] >>
  disch_then (qspecl_then [`s`, `t`] mp_tac) >>
  asm_rewrite_tac[] >>
  Cases_on `f s` >> Cases_on `g t` >>
  Cases_on `q` >> Cases_on `q'` >> simp[] >> metis_tac[]
QED

Theorem root_replay_handle_invariant:
  root_replay_judgement d P Q f g /\
  (!s t r s'. P s t /\ f s = (r, s') ==> invariant_ok s') /\
  (!e. root_replay_judgement d
    (\s t. root_replay_rel d s t /\ invariant_ok s) Q (h e) (k e)) ==>
  root_replay_judgement d P Q (handle f h) (handle g k)
Proof
  simp[root_replay_judgement_def] >> rpt strip_tac >>
  qpat_x_assum `!s t. P s t ==> _` drule >>
  Cases_on `f s` >> Cases_on `g t` >>
  Cases_on `q` >> Cases_on `q'` >> simp[handle_def] >> metis_tac[]
QED

Theorem root_replay_context_read:
  (!c. f (c with msgParams updated_by
          (\mp. mp with outputTo := Memory <| offset := 0; size := 0 |>)) = f c) ==>
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (bind get_current_context (\c. return (f c)))
    (bind get_current_context (\c. return (f c)))
Proof
  strip_tac >>
  simp[root_replay_judgement_def, root_replay_rel_def] >>
  rpt strip_tac >>
  Cases_on `s.contexts` >> gvs[] >> Cases_on `h` >>
  Cases_on `t = []` >>
  gvs[bind_def, get_current_context_def, shadow_root_def,
      shadow_root_contexts_def, return_def]
QED

Theorem root_replay_get_current_code:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    get_current_code get_current_code
Proof
  pure_rewrite_tac[get_current_code_def] >>
  ho_match_mp_tac root_replay_context_read >> simp[]
QED

Theorem root_replay_context_update:
  (!c. f (c with msgParams updated_by
          (\mp. mp with outputTo := Memory <| offset := 0; size := 0 |>)) =
        (f c) with msgParams updated_by
          (\mp. mp with outputTo := Memory <| offset := 0; size := 0 |>)) /\
  (!c. (f c).msgParams.outputTo = c.msgParams.outputTo) ==>
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (bind get_current_context (\c. set_current_context (f c)))
    (bind get_current_context (\c. set_current_context (f c)))
Proof
  strip_tac >>
  simp[root_replay_judgement_def, root_replay_rel_def] >>
  rpt strip_tac >>
  Cases_on `s.contexts` >> gvs[] >> Cases_on `h` >>
  Cases_on `t = []` >>
  gvs[bind_def, get_current_context_def, set_current_context_def,
      shadow_root_def, shadow_root_contexts_def, return_def,
      root_output_to_def, LAST_DEF]
QED

Theorem root_replay_set_return_data:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (set_return_data rd) (set_return_data rd)
Proof
  pure_rewrite_tac[set_return_data_def, LET_THM] >> BETA_TAC >>
  ho_match_mp_tac root_replay_context_update >>
  simp[context_component_equality, combinTheory.o_DEF]
QED

Theorem root_replay_get_num_contexts:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    get_num_contexts get_num_contexts
Proof
  simp[root_replay_judgement_def, root_replay_rel_def,
       get_num_contexts_def, return_def, shadow_root_def,
       shadow_root_contexts_length]
QED

Theorem root_replay_get_tx_params:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    get_tx_params get_tx_params
Proof
  simp[root_replay_judgement_def, root_replay_rel_def,
       get_tx_params_def, return_def, shadow_root_def]
QED

Theorem root_replay_get_accounts:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    get_accounts get_accounts
Proof
  simp[root_replay_judgement_def, root_replay_rel_def,
       get_accounts_def, return_def, shadow_root_def]
QED

Theorem root_replay_get_tStorage:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    get_tStorage get_tStorage
Proof
  simp[root_replay_judgement_def, root_replay_rel_def,
       get_tStorage_def, return_def, shadow_root_def]
QED

Theorem root_replay_get_rollback:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    get_rollback get_rollback
Proof
  simp[root_replay_judgement_def, root_replay_rel_def,
       get_rollback_def, return_def, shadow_root_def]
QED

Theorem root_replay_get_original:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    get_original get_original
Proof
  simp[root_replay_judgement_def, root_replay_rel_def] >>
  rpt strip_tac >>
  simp[get_original_def, return_def, shadow_root_def,
       shadow_root_contexts_nil]
QED

Theorem root_replay_update_accounts:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (update_accounts f) (update_accounts f)
Proof
  simp[root_replay_judgement_def, root_replay_rel_def,
       update_accounts_def, return_def, shadow_root_def,
       root_output_to_def, execution_state_component_equality]
QED

Theorem root_replay_set_rollback:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (set_rollback rb) (set_rollback rb)
Proof
  simp[root_replay_judgement_def, root_replay_rel_def,
       set_rollback_def, return_def, shadow_root_def,
       root_output_to_def, execution_state_component_equality]
QED

Theorem root_replay_set_original:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (set_original a) (set_original a)
Proof
  simp[root_replay_judgement_def, root_replay_rel_def] >>
  rpt strip_tac >>
  gvs[set_original_def, return_def, shadow_root_def,
       shadow_root_contexts_nil, root_output_to_def,
       execution_state_component_equality]
QED

Theorem root_replay_push_context:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (push_context crb) (push_context crb)
Proof
  simp[root_replay_judgement_def, root_replay_rel_def] >>
  rpt strip_tac >> Cases_on `crb` >>
  gvs[push_context_def, return_def, shadow_root_def,
       shadow_root_contexts_cons, root_output_to_def, LAST_DEF,
       execution_state_component_equality]
QED

Theorem root_replay_get_gas_left:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    get_gas_left get_gas_left
Proof
  pure_rewrite_tac[get_gas_left_def] >>
  ho_match_mp_tac root_replay_context_read >> simp[]
QED

Theorem root_replay_get_callee:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    get_callee get_callee
Proof
  pure_rewrite_tac[get_callee_def] >>
  ho_match_mp_tac root_replay_context_read >> simp[]
QED

Theorem root_replay_get_caller:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    get_caller get_caller
Proof
  pure_rewrite_tac[get_caller_def] >>
  ho_match_mp_tac root_replay_context_read >> simp[]
QED

Theorem root_replay_get_value:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    get_value get_value
Proof
  pure_rewrite_tac[get_value_def] >>
  ho_match_mp_tac root_replay_context_read >> simp[]
QED

Theorem root_replay_get_return_data:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    get_return_data get_return_data
Proof
  pure_rewrite_tac[get_return_data_def] >>
  ho_match_mp_tac root_replay_context_read >> simp[]
QED

Theorem root_replay_get_static:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    get_static get_static
Proof
  pure_rewrite_tac[get_static_def] >>
  ho_match_mp_tac root_replay_context_read >> simp[]
QED

Theorem root_replay_get_call_data:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    get_call_data get_call_data
Proof
  pure_rewrite_tac[get_call_data_def] >>
  ho_match_mp_tac root_replay_context_read >> simp[]
QED

Theorem root_replay_set_jump_dest:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (set_jump_dest jd) (set_jump_dest jd)
Proof
  pure_rewrite_tac[set_jump_dest_def] >>
  ho_match_mp_tac root_replay_context_update >>
  simp[context_component_equality, combinTheory.o_DEF]
QED

Theorem root_replay_push_logs:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (push_logs ls) (push_logs ls)
Proof
  pure_rewrite_tac[push_logs_def] >>
  ho_match_mp_tac root_replay_context_update >>
  simp[context_component_equality, combinTheory.o_DEF]
QED

Theorem root_replay_update_gas_refund:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (update_gas_refund refund) (update_gas_refund refund)
Proof
  Cases_on `refund` >> pure_rewrite_tac[update_gas_refund_def] >>
  ho_match_mp_tac root_replay_context_update >>
  simp[context_component_equality, combinTheory.o_DEF]
QED

Theorem root_replay_expand_memory:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (expand_memory n) (expand_memory n)
Proof
  pure_rewrite_tac[expand_memory_def] >>
  ho_match_mp_tac root_replay_context_update >>
  simp[context_component_equality, combinTheory.o_DEF]
QED

Theorem root_replay_write_memory:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (write_memory off bs) (write_memory off bs)
Proof
  pure_rewrite_tac[write_memory_def] >>
  ho_match_mp_tac root_replay_context_update >>
  simp[context_component_equality, combinTheory.o_DEF]
QED

Theorem root_replay_read_memory:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (read_memory off n) (read_memory off n)
Proof
  pure_rewrite_tac[read_memory_def] >>
  ho_match_mp_tac root_replay_context_read >> simp[]
QED

Theorem root_replay_memory_expansion_info:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (memory_expansion_info off n) (memory_expansion_info off n)
Proof
  pure_rewrite_tac[memory_expansion_info_def, LET_THM] >> BETA_TAC >>
  ho_match_mp_tac root_replay_context_read >> simp[]
QED

Theorem root_replay_consume_gas:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (consume_gas n) (consume_gas n)
Proof
  simp[root_replay_judgement_def, root_replay_rel_def] >>
  rpt strip_tac >>
  Cases_on `s.contexts` >> gvs[] >> Cases_on `h` >>
  Cases_on `t = []` >>
  gvs[consume_gas_def, bind_def, ignore_bind_def, get_current_context_def,
      set_current_context_def, shadow_root_def, shadow_root_contexts_def,
      return_def, assert_def, fail_def, root_output_to_def, LAST_DEF,
      execution_state_component_equality, context_component_equality,
      combinTheory.o_DEF] >>
  rpt IF_CASES_TAC >>
  gvs[shadow_root_contexts_def, root_output_to_def, LAST_DEF,
      context_component_equality, combinTheory.o_DEF]
QED

Theorem root_replay_unuse_gas:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (unuse_gas n) (unuse_gas n)
Proof
  simp[root_replay_judgement_def, root_replay_rel_def] >>
  rpt strip_tac >>
  Cases_on `s.contexts` >> gvs[] >> Cases_on `h` >>
  Cases_on `t = []` >>
  gvs[unuse_gas_def, bind_def, ignore_bind_def, get_current_context_def,
      set_current_context_def, shadow_root_def, shadow_root_contexts_def,
      return_def, assert_def, fail_def, root_output_to_def, LAST_DEF,
      execution_state_component_equality, context_component_equality,
      combinTheory.o_DEF] >>
  rpt IF_CASES_TAC >>
  gvs[shadow_root_contexts_def, root_output_to_def, LAST_DEF,
      context_component_equality, combinTheory.o_DEF]
QED

Theorem root_replay_pop_stack:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (pop_stack n) (pop_stack n)
Proof
  simp[root_replay_judgement_def, root_replay_rel_def] >>
  rpt strip_tac >>
  Cases_on `s.contexts` >> gvs[] >> Cases_on `h` >>
  Cases_on `t = []` >>
  gvs[pop_stack_def, bind_def, ignore_bind_def, get_current_context_def,
      set_current_context_def, shadow_root_def, shadow_root_contexts_def,
      return_def, assert_def, fail_def, root_output_to_def, LAST_DEF,
      execution_state_component_equality, context_component_equality,
      combinTheory.o_DEF] >>
  rpt IF_CASES_TAC >>
  gvs[shadow_root_contexts_def, root_output_to_def, LAST_DEF,
      context_component_equality, combinTheory.o_DEF]
QED

Theorem root_replay_push_stack:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (push_stack v) (push_stack v)
Proof
  simp[root_replay_judgement_def, root_replay_rel_def] >>
  rpt strip_tac >>
  Cases_on `s.contexts` >> gvs[] >> Cases_on `h` >>
  Cases_on `t = []` >>
  gvs[push_stack_def, bind_def, ignore_bind_def, get_current_context_def,
      set_current_context_def, shadow_root_def, shadow_root_contexts_def,
      return_def, assert_def, fail_def, root_output_to_def, LAST_DEF,
      execution_state_component_equality, context_component_equality,
      combinTheory.o_DEF] >>
  rpt IF_CASES_TAC >>
  gvs[shadow_root_contexts_def, root_output_to_def, LAST_DEF,
      context_component_equality, combinTheory.o_DEF]
QED

Theorem root_replay_add_to_delete:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (add_to_delete a) (add_to_delete a)
Proof
  simp[root_replay_judgement_def, root_replay_rel_def,
       add_to_delete_def, return_def, shadow_root_def,
       root_output_to_def, execution_state_component_equality]
QED

Theorem root_replay_access_address:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (access_address a) (access_address a)
Proof
  simp[root_replay_judgement_def, root_replay_rel_def] >>
  rpt strip_tac >> Cases_on `s.msdomain` >>
  gvs[access_address_def, domain_check_def, set_domain_def,
      ignore_bind_def, bind_def, return_def, fail_def, shadow_root_def,
      root_output_to_def, execution_state_component_equality] >>
  rpt IF_CASES_TAC >> simp[shadow_root_def]
QED

Theorem root_replay_access_slot:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (access_slot a) (access_slot a)
Proof
  simp[root_replay_judgement_def, root_replay_rel_def] >>
  rpt strip_tac >> Cases_on `s.msdomain` >>
  gvs[access_slot_def, domain_check_def, set_domain_def,
      ignore_bind_def, bind_def, return_def, fail_def, shadow_root_def,
      root_output_to_def, execution_state_component_equality] >>
  rpt IF_CASES_TAC >> simp[shadow_root_def]
QED

Theorem root_replay_ensure_storage_in_domain:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (ensure_storage_in_domain a) (ensure_storage_in_domain a)
Proof
  simp[root_replay_judgement_def, root_replay_rel_def] >>
  rpt strip_tac >> Cases_on `s.msdomain` >>
  gvs[ensure_storage_in_domain_def, domain_check_def, set_domain_def,
      ignore_bind_def, bind_def, return_def, fail_def, shadow_root_def,
      root_output_to_def, execution_state_component_equality] >>
  rpt IF_CASES_TAC >> simp[shadow_root_def]
QED

Theorem root_replay_get_code:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (get_code a) (get_code a)
Proof
  pure_rewrite_tac[get_code_def] >>
  irule root_replay_bind >>
  qexists_tac `\x s y t. x = y /\ root_replay_rel d s t` >>
  conj_tac
  >- (rpt gen_tac >> BETA_TAC >> irule root_replay_return >> simp[]) >>
  irule root_replay_get_accounts
QED

Theorem root_replay_write_storage:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (write_storage a k v) (write_storage a k v)
Proof
  pure_rewrite_tac[write_storage_def] >>
  irule root_replay_update_accounts
QED

Theorem root_replay_write_transient_storage:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (write_transient_storage a k v) (write_transient_storage a k v)
Proof
  pure_rewrite_tac[write_transient_storage_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind >>
  qexists_tac `\x s y t. x = y /\ root_replay_rel d s t` >>
  conj_tac
  >- (rpt gen_tac >>
      simp[root_replay_judgement_def, root_replay_rel_def] >>
      rpt strip_tac >> gvs[] >>
      simp[set_tStorage_def, return_def, shadow_root_def,
           root_output_to_def, execution_state_component_equality]) >>
  irule root_replay_get_tStorage
QED

Theorem root_replay_get_return_data_check:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (get_return_data_check off n) (get_return_data_check off n)
Proof
  simp[root_replay_judgement_def, root_replay_rel_def] >>
  rpt strip_tac >>
  Cases_on `s.contexts` >> gvs[] >> Cases_on `h` >>
  Cases_on `t = []` >>
  gvs[get_return_data_check_def, get_return_data_def, bind_def,
      ignore_bind_def, get_current_context_def,
      shadow_root_def, shadow_root_contexts_def,
      return_def, assert_def, fail_def, root_output_to_def, LAST_DEF] >>
  rpt IF_CASES_TAC >> simp[shadow_root_def, shadow_root_contexts_def, LAST_DEF]
QED

Theorem root_replay_assert_not_static:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    assert_not_static assert_not_static
Proof
  simp[root_replay_judgement_def, root_replay_rel_def] >>
  rpt strip_tac >>
  Cases_on `s.contexts` >> gvs[] >> Cases_on `h` >>
  Cases_on `t = []` >>
  gvs[assert_not_static_def, get_static_def, bind_def,
      get_current_context_def, shadow_root_def, shadow_root_contexts_def,
      return_def, assert_def, fail_def, root_output_to_def, LAST_DEF] >>
  rpt IF_CASES_TAC >> simp[shadow_root_def, shadow_root_contexts_def, LAST_DEF]
QED

Theorem root_replay_bind_exact:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t) f f /\
  (!x. root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t) (k x) (k x)) ==>
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (bind f k) (bind f k)
Proof
  strip_tac >> irule root_replay_bind >>
  qexists_tac `\x s y t. x = y /\ root_replay_rel d s t` >>
  simp[] >>
  qpat_x_assum `!x. _` mp_tac >>
  simp[root_replay_judgement_def]
QED

Theorem root_replay_ignore_bind_exact:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t) f f /\
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t) g g ==>
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (ignore_bind f g) (ignore_bind f g)
Proof
  pure_rewrite_tac[ignore_bind_def] >>
  strip_tac >> irule root_replay_bind_exact >> simp[]
QED

Theorem root_replay_step_binop:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (step_binop op f) (step_binop op f)
Proof
  pure_rewrite_tac[step_binop_def] >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule root_replay_ignore_bind_exact >>
      simp[root_replay_consume_gas, root_replay_push_stack]) >>
  irule root_replay_pop_stack
QED

Theorem root_replay_step_monop:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (step_monop op f) (step_monop op f)
Proof
  pure_rewrite_tac[step_monop_def] >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule root_replay_ignore_bind_exact >>
      simp[root_replay_consume_gas, root_replay_push_stack]) >>
  irule root_replay_pop_stack
QED

Theorem root_replay_step_modop:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (step_modop op f) (step_modop op f)
Proof
  pure_rewrite_tac[step_modop_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule root_replay_ignore_bind_exact >>
      simp[root_replay_consume_gas, root_replay_push_stack]) >>
  irule root_replay_pop_stack
QED

Theorem root_replay_step_exp:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    step_exp step_exp
Proof
  pure_rewrite_tac[step_exp_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule root_replay_ignore_bind_exact >>
      simp[root_replay_consume_gas, root_replay_push_stack]) >>
  irule root_replay_pop_stack
QED

Theorem root_replay_step_txParams:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (step_txParams op f) (step_txParams op f)
Proof
  pure_rewrite_tac[step_txParams_def] >>
  irule root_replay_ignore_bind_exact >> conj_tac
  >- irule root_replay_consume_gas >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule root_replay_push_stack) >>
  irule root_replay_get_tx_params
QED

Theorem root_replay_context_apply:
  !f. (!c. f (c with msgParams updated_by
          (\mp. mp with outputTo := Memory <| offset := 0; size := 0 |>)) = f c) /\
  (!x. root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t) (k x) (k x)) ==>
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (bind get_current_context (\c. k (f c)))
    (bind get_current_context (\c. k (f c)))
Proof
  gen_tac >> strip_tac >>
  `bind get_current_context (\c. k (f c)) =
   bind (bind get_current_context (\c. return (f c))) k`
    by simp[bind_assoc] >>
  pop_assum SUBST1_TAC >>
  irule root_replay_bind_exact >>
  conj_tac >- simp[] >>
  irule root_replay_context_read >> simp[]
QED

Theorem root_replay_step_context:
  (!c. f (c with msgParams updated_by
          (\mp. mp with outputTo := Memory <| offset := 0; size := 0 |>)) = f c) ==>
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (step_context op f) (step_context op f)
Proof
  strip_tac >> pure_rewrite_tac[step_context_def] >>
  irule root_replay_ignore_bind_exact >> conj_tac
  >- irule root_replay_consume_gas >>
  ho_match_mp_tac root_replay_context_apply >>
  conj_tac >- simp[] >> gen_tac >> irule root_replay_push_stack
QED

Theorem root_replay_step_msgParams:
  (!mp. f (mp with outputTo := Memory <| offset := 0; size := 0 |>) = f mp) ==>
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (step_msgParams op f) (step_msgParams op f)
Proof
  strip_tac >> pure_rewrite_tac[step_msgParams_def] >>
  irule root_replay_step_context >> simp[]
QED

Theorem root_replay_step_keccak256:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    step_keccak256 step_keccak256
Proof
  pure_rewrite_tac[step_keccak256_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_bind_exact >> conj_tac
      >- (gen_tac >> BETA_TAC >>
          irule root_replay_ignore_bind_exact >> conj_tac
          >- irule root_replay_consume_gas >>
          irule root_replay_ignore_bind_exact >> conj_tac
          >- irule root_replay_expand_memory >>
          irule root_replay_bind_exact >> conj_tac
          >- (gen_tac >> BETA_TAC >> irule root_replay_push_stack) >>
          irule root_replay_read_memory) >>
      irule root_replay_memory_expansion_info) >>
  irule root_replay_pop_stack
QED

Theorem root_replay_inc_pc:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    inc_pc inc_pc
Proof
  pure_rewrite_tac[inc_pc_def] >>
  ho_match_mp_tac root_replay_context_update >>
  simp[context_component_equality, combinTheory.o_DEF]
QED

Theorem root_replay_inc_pc_or_jump:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (inc_pc_or_jump op) (inc_pc_or_jump op)
Proof
  Cases_on `is_call op`
  >- (pure_rewrite_tac[inc_pc_or_jump_def] >> simp[] >>
      irule root_replay_return >> simp[]) >>
  simp[root_replay_judgement_def, root_replay_rel_def] >>
  rpt strip_tac >>
  Cases_on `s.contexts` >> gvs[] >> Cases_on `h` >>
  Cases_on `t = []` >> Cases_on `q.jumpDest` >>
  gvs[inc_pc_or_jump_def, bind_def, ignore_bind_def, get_current_context_def,
      set_current_context_def, shadow_root_def, shadow_root_contexts_def,
      return_def, assert_def, fail_def, root_output_to_def, LAST_DEF,
      execution_state_component_equality, context_component_equality,
      combinTheory.o_DEF] >>
  rpt IF_CASES_TAC >>
  gvs[shadow_root_contexts_def, root_output_to_def, LAST_DEF,
      context_component_equality, combinTheory.o_DEF]
QED

Theorem root_replay_step_mload:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    step_mload step_mload
Proof
  pure_rewrite_tac[step_mload_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_bind_exact >> conj_tac
      >- (gen_tac >> BETA_TAC >>
          irule root_replay_ignore_bind_exact >> conj_tac
          >- irule root_replay_consume_gas >>
          irule root_replay_ignore_bind_exact >> conj_tac
          >- irule root_replay_expand_memory >>
          irule root_replay_bind_exact >> conj_tac
          >- (gen_tac >> BETA_TAC >> irule root_replay_push_stack) >>
          irule root_replay_read_memory) >>
      irule root_replay_memory_expansion_info) >>
  irule root_replay_pop_stack
QED

Theorem root_replay_step_mstore:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (step_mstore op) (step_mstore op)
Proof
  pure_rewrite_tac[step_mstore_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_bind_exact >> conj_tac
      >- (gen_tac >> BETA_TAC >>
          irule root_replay_ignore_bind_exact >> conj_tac
          >- irule root_replay_consume_gas >>
          irule root_replay_ignore_bind_exact >> conj_tac
          >- irule root_replay_expand_memory >>
          irule root_replay_write_memory) >>
      irule root_replay_memory_expansion_info) >>
  irule root_replay_pop_stack
QED

Theorem root_replay_step_jump:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    step_jump step_jump
Proof
  pure_rewrite_tac[step_jump_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule root_replay_ignore_bind_exact >>
      simp[root_replay_consume_gas, root_replay_set_jump_dest]) >>
  irule root_replay_pop_stack
QED

Theorem root_replay_step_jumpi:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    step_jumpi step_jumpi
Proof
  pure_rewrite_tac[step_jumpi_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule root_replay_ignore_bind_exact >>
      simp[root_replay_consume_gas, root_replay_set_jump_dest]) >>
  irule root_replay_pop_stack
QED

Theorem root_replay_step_push:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (step_push n ws) (step_push n ws)
Proof
  pure_rewrite_tac[step_push_def] >>
  irule root_replay_ignore_bind_exact >>
  simp[root_replay_consume_gas, root_replay_push_stack]
QED

Theorem root_replay_step_pop:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    step_pop step_pop
Proof
  pure_rewrite_tac[step_pop_def] >>
  irule root_replay_ignore_bind_exact >>
  simp[root_replay_pop_stack, root_replay_consume_gas]
QED

Theorem root_replay_assert:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (assert b e) (assert b e)
Proof
  Cases_on `b` >>
  simp[root_replay_judgement_def, assert_def, return_def, fail_def]
QED

Theorem root_replay_finish:
  root_replay_judgement d (root_replay_rel d) Q finish finish
Proof
  simp[root_replay_judgement_def, finish_def]
QED

Theorem root_replay_revert:
  root_replay_judgement d (root_replay_rel d) Q revert revert
Proof
  simp[root_replay_judgement_def, revert_def]
QED

Theorem root_replay_fail:
  root_replay_judgement d (root_replay_rel d) Q (fail e) (fail e)
Proof
  simp[root_replay_judgement_def, fail_def]
QED

Theorem root_replay_step_return:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (step_return b) (step_return b)
Proof
  pure_rewrite_tac[step_return_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_bind_exact >> conj_tac
      >- (gen_tac >> BETA_TAC >>
          irule root_replay_ignore_bind_exact >> conj_tac
          >- irule root_replay_consume_gas >>
          irule root_replay_ignore_bind_exact >> conj_tac
          >- irule root_replay_expand_memory >>
          irule root_replay_bind_exact >> conj_tac
          >- (gen_tac >> BETA_TAC >>
              irule root_replay_ignore_bind_exact >> conj_tac
              >- irule root_replay_set_return_data >>
              Cases_on `b` >> simp[root_replay_finish, root_replay_revert]) >>
          irule root_replay_read_memory) >>
      irule root_replay_memory_expansion_info) >>
  irule root_replay_pop_stack
QED

Theorem step_dup_stack_factor[local]:
  step_dup n =
    ignore_bind (consume_gas (static_gas (Dup n)))
      (bind (bind get_current_context (\c. return c.stack))
        (\stack. ignore_bind (assert (n < LENGTH stack) StackUnderflow)
                            (push_stack (EL n stack))))
Proof
  simp[step_dup_def, bind_assoc, LET_THM]
QED

Theorem root_replay_step_dup:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (step_dup n) (step_dup n)
Proof
  pure_rewrite_tac[step_dup_stack_factor] >>
  irule root_replay_ignore_bind_exact >> conj_tac
  >- irule root_replay_consume_gas >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_assert >> irule root_replay_push_stack) >>
  ho_match_mp_tac root_replay_context_read >> simp[]
QED

Theorem step_swap_stack_factor[local]:
  step_swap n =
    ignore_bind (consume_gas (static_gas (Swap n)))
      (bind (bind get_current_context (\c. return c.stack))
        (\stack. ignore_bind (assert (SUC n < LENGTH stack) StackUnderflow)
          (bind get_current_context (\c. set_current_context
            (c with stack :=
              [EL n (TL c.stack)] ++ TAKE n (TL c.stack) ++
              [HD c.stack] ++ DROP (SUC n) (TL c.stack))))))
Proof
  pure_rewrite_tac[step_swap_def, LET_THM] >> BETA_TAC >>
  AP_TERM_TAC >>
  simp[FUN_EQ_THM, bind_def, ignore_bind_def, get_current_context_def,
       return_def, assert_def, fail_def] >>
  gen_tac >> Cases_on `x.contexts` >> simp[] >>
  Cases_on `h` >> simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem root_replay_step_swap:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (step_swap n) (step_swap n)
Proof
  pure_rewrite_tac[step_swap_stack_factor] >>
  irule root_replay_ignore_bind_exact >> conj_tac
  >- irule root_replay_consume_gas >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_assert >>
      ho_match_mp_tac root_replay_context_update >>
      simp[context_component_equality, combinTheory.o_DEF]) >>
  ho_match_mp_tac root_replay_context_read >> simp[]
QED

Theorem root_replay_step_call_data_load:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    step_call_data_load step_call_data_load
Proof
  pure_rewrite_tac[step_call_data_load_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_consume_gas >>
      irule root_replay_bind_exact >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule root_replay_push_stack) >>
      irule root_replay_get_call_data) >>
  irule root_replay_pop_stack
QED

Theorem root_replay_step_block_hash:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    step_block_hash step_block_hash
Proof
  pure_rewrite_tac[step_block_hash_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_consume_gas >>
      irule root_replay_bind_exact >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule root_replay_push_stack) >>
      irule root_replay_get_tx_params) >>
  irule root_replay_pop_stack
QED

Theorem root_replay_step_blob_hash:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    step_blob_hash step_blob_hash
Proof
  pure_rewrite_tac[step_blob_hash_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_consume_gas >>
      irule root_replay_bind_exact >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule root_replay_push_stack) >>
      irule root_replay_get_tx_params) >>
  irule root_replay_pop_stack
QED

Theorem root_replay_step_balance:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    step_balance step_balance
Proof
  pure_rewrite_tac[step_balance_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_bind_exact >> conj_tac
      >- (gen_tac >> BETA_TAC >>
          irule root_replay_ignore_bind_exact >> conj_tac
          >- irule root_replay_consume_gas >>
          irule root_replay_bind_exact >> conj_tac
          >- (gen_tac >> BETA_TAC >> irule root_replay_push_stack) >>
          irule root_replay_get_accounts) >>
      irule root_replay_access_address) >>
  irule root_replay_pop_stack
QED

Theorem root_replay_step_ext_code_size:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    step_ext_code_size step_ext_code_size
Proof
  pure_rewrite_tac[step_ext_code_size_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_bind_exact >> conj_tac
      >- (gen_tac >> BETA_TAC >>
          irule root_replay_ignore_bind_exact >> conj_tac
          >- irule root_replay_consume_gas >>
          irule root_replay_bind_exact >> conj_tac
          >- (gen_tac >> BETA_TAC >> irule root_replay_push_stack) >>
          irule root_replay_get_accounts) >>
      irule root_replay_access_address) >>
  irule root_replay_pop_stack
QED

Theorem root_replay_step_ext_code_hash:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    step_ext_code_hash step_ext_code_hash
Proof
  pure_rewrite_tac[step_ext_code_hash_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_bind_exact >> conj_tac
      >- (gen_tac >> BETA_TAC >>
          irule root_replay_ignore_bind_exact >> conj_tac
          >- irule root_replay_consume_gas >>
          irule root_replay_bind_exact >> conj_tac
          >- (gen_tac >> BETA_TAC >> irule root_replay_push_stack) >>
          irule root_replay_get_accounts) >>
      irule root_replay_access_address) >>
  irule root_replay_pop_stack
QED

Theorem root_replay_step_self_balance:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    step_self_balance step_self_balance
Proof
  pure_rewrite_tac[step_self_balance_def, LET_THM] >> BETA_TAC >>
  irule root_replay_ignore_bind_exact >> conj_tac
  >- irule root_replay_consume_gas >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_bind_exact >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule root_replay_push_stack) >>
      irule root_replay_get_callee) >>
  irule root_replay_get_accounts
QED

Theorem root_replay_copy_to_memory:
  (!f. source = SOME f ==>
    root_replay_judgement d (root_replay_rel d)
      (\x s y t. x = y /\ root_replay_rel d s t) f f) ==>
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (copy_to_memory gas off srcOff sz source)
    (copy_to_memory gas off srcOff sz source)
Proof
  strip_tac >> Cases_on `source`
  >- (Cases_on `max_expansion_range (off,sz) (srcOff,sz)` >>
      pure_rewrite_tac[copy_to_memory_def, LET_THM,
        REFL_CLAUSE, COND_CLAUSES, optionTheory.option_case_def] >>
      asm_rewrite_tac[] >> CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >> BETA_TAC >>
      irule root_replay_bind_exact >> conj_tac
      >- (gen_tac >> BETA_TAC >>
          irule root_replay_ignore_bind_exact >> conj_tac
          >- irule root_replay_consume_gas >>
          irule root_replay_bind_exact >> conj_tac
          >- (gen_tac >> BETA_TAC >> irule root_replay_write_memory) >>
          irule root_replay_ignore_bind_exact >> conj_tac
          >- irule root_replay_expand_memory >>
          irule root_replay_read_memory) >>
      irule root_replay_memory_expansion_info) >>
  pure_rewrite_tac[copy_to_memory_def, LET_THM,
    optionTheory.NOT_SOME_NONE, COND_CLAUSES,
    optionTheory.option_case_def] >>
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_consume_gas >>
      irule root_replay_bind_exact >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule root_replay_write_memory) >>
      irule root_replay_bind_exact >> conj_tac
      >- (gen_tac >> BETA_TAC >>
          irule root_replay_ignore_bind_exact >> conj_tac
          >- irule root_replay_expand_memory >>
          irule root_replay_return >> simp[]) >>
      first_x_assum irule >> simp[]) >>
  irule root_replay_memory_expansion_info
QED

Theorem root_replay_step_copy_to_memory:
  (!f. source = SOME f ==>
    root_replay_judgement d (root_replay_rel d)
      (\x s y t. x = y /\ root_replay_rel d s t) f f) ==>
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (step_copy_to_memory op source) (step_copy_to_memory op source)
Proof
  strip_tac >> pure_rewrite_tac[step_copy_to_memory_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule root_replay_copy_to_memory >> simp[]) >>
  irule root_replay_pop_stack
QED

Theorem root_replay_step_return_data_copy:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    step_return_data_copy step_return_data_copy
Proof
  pure_rewrite_tac[step_return_data_copy_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule root_replay_copy_to_memory >>
      gen_tac >> strip_tac >> gvs[] >>
      irule root_replay_get_return_data_check) >>
  irule root_replay_pop_stack
QED

Theorem root_replay_step_ext_code_copy:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    step_ext_code_copy step_ext_code_copy
Proof
  pure_rewrite_tac[step_ext_code_copy_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_bind_exact >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule root_replay_copy_to_memory >>
          gen_tac >> strip_tac >> gvs[] >> irule root_replay_get_code) >>
      irule root_replay_access_address) >>
  irule root_replay_pop_stack
QED

Theorem root_replay_step_sload:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (step_sload transient) (step_sload transient)
Proof
  pure_rewrite_tac[step_sload_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_bind_exact >> conj_tac
      >- (gen_tac >> BETA_TAC >>
          irule root_replay_bind_exact >> conj_tac
          >- (gen_tac >> BETA_TAC >>
              irule root_replay_ignore_bind_exact >> conj_tac
              >- irule root_replay_consume_gas >>
              irule root_replay_bind_exact >> conj_tac
              >- (gen_tac >> BETA_TAC >> irule root_replay_push_stack) >>
              Cases_on `transient` >> pure_rewrite_tac[COND_CLAUSES]
              >- (irule root_replay_bind_exact >> conj_tac
                  >- (gen_tac >> BETA_TAC >> irule root_replay_return >> simp[]) >>
                  irule root_replay_get_tStorage) >>
              irule root_replay_bind_exact >> conj_tac
              >- (gen_tac >> BETA_TAC >> irule root_replay_return >> simp[]) >>
              irule root_replay_get_accounts) >>
          Cases_on `transient` >> pure_rewrite_tac[COND_CLAUSES]
          >- (irule root_replay_return >> simp[]) >>
          irule root_replay_access_slot) >>
      irule root_replay_get_callee) >>
  irule root_replay_pop_stack
QED

Theorem root_replay_step_sstore_gas_consumption:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (step_sstore_gas_consumption address key value)
    (step_sstore_gas_consumption address key value)
Proof
  pure_rewrite_tac[step_sstore_gas_consumption_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_assert >>
      irule root_replay_bind_exact >> conj_tac
      >- (gen_tac >> BETA_TAC >>
          irule root_replay_bind_exact >> conj_tac
          >- (gen_tac >> BETA_TAC >>
              irule root_replay_bind_exact >> conj_tac
              >- (gen_tac >> BETA_TAC >>
                  irule root_replay_ignore_bind_exact >> conj_tac
                  >- irule root_replay_update_gas_refund >>
                  irule root_replay_consume_gas) >>
              irule root_replay_access_slot) >>
          irule root_replay_get_original) >>
      irule root_replay_get_accounts) >>
  irule root_replay_get_gas_left
QED

Theorem root_replay_step_sstore:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (step_sstore transient) (step_sstore transient)
Proof
  pure_rewrite_tac[step_sstore_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_bind_exact >> conj_tac
      >- (gen_tac >> BETA_TAC >>
          irule root_replay_ignore_bind_exact >> conj_tac
          >- (Cases_on `transient` >> pure_rewrite_tac[COND_CLAUSES]
              >- irule root_replay_consume_gas >>
              irule root_replay_step_sstore_gas_consumption) >>
          irule root_replay_ignore_bind_exact >> conj_tac
          >- irule root_replay_assert_not_static >>
          Cases_on `transient` >> pure_rewrite_tac[COND_CLAUSES]
          >- irule root_replay_write_transient_storage >>
          irule root_replay_write_storage) >>
      irule root_replay_get_callee) >>
  irule root_replay_pop_stack
QED

Theorem root_replay_step_log:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (step_log n) (step_log n)
Proof
  pure_rewrite_tac[step_log_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_bind_exact >> conj_tac
      >- (gen_tac >> BETA_TAC >>
          irule root_replay_ignore_bind_exact >> conj_tac
          >- irule root_replay_consume_gas >>
          irule root_replay_ignore_bind_exact >> conj_tac
          >- irule root_replay_expand_memory >>
          irule root_replay_ignore_bind_exact >> conj_tac
          >- irule root_replay_assert_not_static >>
          irule root_replay_bind_exact >> conj_tac
          >- (gen_tac >> BETA_TAC >>
              irule root_replay_bind_exact >> conj_tac
              >- (gen_tac >> BETA_TAC >> irule root_replay_push_logs) >>
              irule root_replay_read_memory) >>
          irule root_replay_get_callee) >>
      irule root_replay_memory_expansion_info) >>
  irule root_replay_pop_stack
QED

Theorem root_replay_step_self_destruct:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    step_self_destruct step_self_destruct
Proof
  pure_rewrite_tac[step_self_destruct_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_bind_exact >> conj_tac
      >- (gen_tac >> BETA_TAC >>
          irule root_replay_bind_exact >> conj_tac
          >- (gen_tac >> BETA_TAC >>
              irule root_replay_ignore_bind_exact >> conj_tac
              >- irule root_replay_set_return_data >>
              irule root_replay_bind_exact >> conj_tac
              >- (gen_tac >> BETA_TAC >>
                  irule root_replay_ignore_bind_exact >> conj_tac
                  >- irule root_replay_consume_gas >>
                  irule root_replay_ignore_bind_exact >> conj_tac
                  >- irule root_replay_assert_not_static >>
                  irule root_replay_ignore_bind_exact >> conj_tac
                  >- irule root_replay_update_accounts >>
                  irule root_replay_bind_exact >> conj_tac
                  >- (gen_tac >> BETA_TAC >>
                      irule root_replay_ignore_bind_exact >> conj_tac
                      >- (IF_CASES_TAC >> pure_rewrite_tac[COND_CLAUSES]
                          >- (irule root_replay_ignore_bind_exact >> conj_tac
                              >- irule root_replay_update_accounts >>
                              irule root_replay_add_to_delete) >>
                          irule root_replay_return >> simp[]) >>
                      irule root_replay_finish) >>
                  irule root_replay_get_original) >>
              irule root_replay_get_accounts) >>
          irule root_replay_get_callee) >>
      irule root_replay_access_address) >>
  irule root_replay_pop_stack
QED

Theorem root_replay_abort_unuse:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (abort_unuse n) (abort_unuse n)
Proof
  pure_rewrite_tac[abort_unuse_def] >>
  irule root_replay_ignore_bind_exact >> conj_tac
  >- irule root_replay_unuse_gas >>
  irule root_replay_ignore_bind_exact >> conj_tac
  >- irule root_replay_push_stack >> irule root_replay_inc_pc
QED

Theorem root_replay_abort_create_exists:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (abort_create_exists address) (abort_create_exists address)
Proof
  pure_rewrite_tac[abort_create_exists_def] >>
  irule root_replay_ignore_bind_exact >> conj_tac
  >- irule root_replay_update_accounts >>
  irule root_replay_ignore_bind_exact >> conj_tac
  >- irule root_replay_push_stack >> irule root_replay_inc_pc
QED

Theorem root_replay_abort_call_value:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (abort_call_value stipend) (abort_call_value stipend)
Proof
  pure_rewrite_tac[abort_call_value_def] >>
  irule root_replay_ignore_bind_exact >> conj_tac
  >- irule root_replay_push_stack >>
  irule root_replay_ignore_bind_exact >> conj_tac
  >- irule root_replay_set_return_data >>
  irule root_replay_ignore_bind_exact >> conj_tac
  >- irule root_replay_unuse_gas >> irule root_replay_inc_pc
QED

Theorem root_replay_proceed_create:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (proceed_create sender address value code gas)
    (proceed_create sender address value code gas)
Proof
  pure_rewrite_tac[proceed_create_def, LET_THM] >> BETA_TAC >>
  irule root_replay_ignore_bind_exact >> conj_tac
  >- irule root_replay_update_accounts >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_bind_exact >> conj_tac
      >- (gen_tac >> BETA_TAC >>
          irule root_replay_ignore_bind_exact >> conj_tac
          >- irule root_replay_set_original >>
          irule root_replay_ignore_bind_exact >> conj_tac
          >- irule root_replay_update_accounts >>
          irule root_replay_push_context) >>
      irule root_replay_get_original) >>
  irule root_replay_get_rollback
QED

Theorem root_replay_step_create:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (step_create two) (step_create two)
Proof
  pure_rewrite_tac[step_create_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_bind_exact >> conj_tac
      >- (gen_tac >> BETA_TAC >>
          irule root_replay_ignore_bind_exact >> conj_tac
          >- irule root_replay_consume_gas >>
          irule root_replay_ignore_bind_exact >> conj_tac
          >- irule root_replay_expand_memory >>
          irule root_replay_bind_exact >> conj_tac
          >- (gen_tac >> BETA_TAC >>
              irule root_replay_bind_exact >> conj_tac
              >- (gen_tac >> BETA_TAC >>
                  irule root_replay_bind_exact >> conj_tac
                  >- (gen_tac >> BETA_TAC >> suspend "setup") >>
                  irule root_replay_get_accounts) >>
              irule root_replay_get_callee) >>
          irule root_replay_read_memory) >>
      irule root_replay_memory_expansion_info) >>
  irule root_replay_pop_stack
QED

Resume root_replay_step_create[setup]:
  irule root_replay_ignore_bind_exact >> conj_tac
  >- irule root_replay_assert >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_consume_gas >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_assert_not_static >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_set_return_data >>
      irule root_replay_bind_exact >> conj_tac
      >- (gen_tac >> BETA_TAC >>
          IF_CASES_TAC >> pure_rewrite_tac[COND_CLAUSES]
          >- irule root_replay_abort_unuse >>
          irule root_replay_ignore_bind_exact >> conj_tac
          >- irule root_replay_access_address >>
          irule root_replay_ignore_bind_exact >> conj_tac
          >- irule root_replay_ensure_storage_in_domain >>
          IF_CASES_TAC >> pure_rewrite_tac[COND_CLAUSES]
          >- irule root_replay_abort_create_exists >>
          irule root_replay_proceed_create) >>
      irule root_replay_get_num_contexts) >>
  irule root_replay_get_gas_left
QED

Finalise root_replay_step_create

Theorem root_replay_precompile_bls_g1add:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    precompile_bls_g1add precompile_bls_g1add
Proof
  pure_rewrite_tac[precompile_bls_g1add_def] >>
  irule root_replay_bind_exact >> conj_tac
  >- (qx_gen_tac `input` >> BETA_TAC >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_consume_gas >>
      Cases_on `bls12381$bls_g1add input` >>
      pure_rewrite_tac[optionTheory.option_case_def] >> BETA_TAC
      >- irule root_replay_fail >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_set_return_data >> irule root_replay_finish) >>
  irule root_replay_get_call_data
QED

Theorem root_replay_precompile_bls_g1msm:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    precompile_bls_g1msm precompile_bls_g1msm
Proof
  pure_rewrite_tac[precompile_bls_g1msm_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (qx_gen_tac `input` >> BETA_TAC >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_consume_gas >>
      Cases_on `bls12381$bls_g1msm input` >>
      pure_rewrite_tac[optionTheory.option_case_def] >> BETA_TAC
      >- irule root_replay_fail >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_set_return_data >> irule root_replay_finish) >>
  irule root_replay_get_call_data
QED

Theorem root_replay_precompile_bls_g2add:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    precompile_bls_g2add precompile_bls_g2add
Proof
  pure_rewrite_tac[precompile_bls_g2add_def] >>
  irule root_replay_bind_exact >> conj_tac
  >- (qx_gen_tac `input` >> BETA_TAC >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_consume_gas >>
      Cases_on `bls12381$bls_g2add input` >>
      pure_rewrite_tac[optionTheory.option_case_def] >> BETA_TAC
      >- irule root_replay_fail >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_set_return_data >> irule root_replay_finish) >>
  irule root_replay_get_call_data
QED

Theorem root_replay_precompile_bls_g2msm:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    precompile_bls_g2msm precompile_bls_g2msm
Proof
  pure_rewrite_tac[precompile_bls_g2msm_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (qx_gen_tac `input` >> BETA_TAC >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_consume_gas >>
      Cases_on `bls12381$bls_g2msm input` >>
      pure_rewrite_tac[optionTheory.option_case_def] >> BETA_TAC
      >- irule root_replay_fail >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_set_return_data >> irule root_replay_finish) >>
  irule root_replay_get_call_data
QED

Theorem root_replay_precompile_bls_pairing:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    precompile_bls_pairing precompile_bls_pairing
Proof
  pure_rewrite_tac[precompile_bls_pairing_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (qx_gen_tac `input` >> BETA_TAC >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_consume_gas >>
      Cases_on `bls12381$bls_pairing input` >>
      pure_rewrite_tac[optionTheory.option_case_def] >> BETA_TAC
      >- irule root_replay_fail >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_set_return_data >> irule root_replay_finish) >>
  irule root_replay_get_call_data
QED

Theorem root_replay_precompile_bls_map_fp_to_g1:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    precompile_bls_map_fp_to_g1 precompile_bls_map_fp_to_g1
Proof
  pure_rewrite_tac[precompile_bls_map_fp_to_g1_def] >>
  irule root_replay_bind_exact >> conj_tac
  >- (qx_gen_tac `input` >> BETA_TAC >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_consume_gas >>
      Cases_on `bls12381$bls_map_fp_to_g1 input` >>
      pure_rewrite_tac[optionTheory.option_case_def] >> BETA_TAC
      >- irule root_replay_fail >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_set_return_data >> irule root_replay_finish) >>
  irule root_replay_get_call_data
QED

Theorem root_replay_precompile_bls_map_fp2_to_g2:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    precompile_bls_map_fp2_to_g2 precompile_bls_map_fp2_to_g2
Proof
  pure_rewrite_tac[precompile_bls_map_fp2_to_g2_def] >>
  irule root_replay_bind_exact >> conj_tac
  >- (qx_gen_tac `input` >> BETA_TAC >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_consume_gas >>
      Cases_on `bls12381$bls_map_fp2_to_g2 input` >>
      pure_rewrite_tac[optionTheory.option_case_def] >> BETA_TAC
      >- irule root_replay_fail >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_set_return_data >> irule root_replay_finish) >>
  irule root_replay_get_call_data
QED

Theorem root_replay_precompile_identity:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    precompile_identity precompile_identity
Proof
  pure_rewrite_tac[precompile_identity_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_consume_gas >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_set_return_data >> irule root_replay_finish) >>
  irule root_replay_get_call_data
QED

Theorem root_replay_precompile_sha2_256:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    precompile_sha2_256 precompile_sha2_256
Proof
  pure_rewrite_tac[precompile_sha2_256_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_consume_gas >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_set_return_data >> irule root_replay_finish) >>
  irule root_replay_get_call_data
QED

Theorem root_replay_precompile_modexp:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    precompile_modexp precompile_modexp
Proof
  pure_rewrite_tac[precompile_modexp_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_assert >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_consume_gas >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_set_return_data >> irule root_replay_finish) >>
  irule root_replay_get_call_data
QED

Theorem root_replay_precompile_ripemd_160:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    precompile_ripemd_160 precompile_ripemd_160
Proof
  pure_rewrite_tac[precompile_ripemd_160_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (qx_gen_tac `input` >> BETA_TAC >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_consume_gas >>
      Cases_on `ripemd160$RIPEMD_160_bytes input` >>
      pure_rewrite_tac[optionTheory.option_case_def] >> BETA_TAC
      >- irule root_replay_fail >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_set_return_data >> irule root_replay_finish) >>
  irule root_replay_get_call_data
QED

Theorem root_replay_precompile_ecrecover:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    precompile_ecrecover precompile_ecrecover
Proof
  pure_rewrite_tac[precompile_ecrecover_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_consume_gas >>
      qmatch_goalsub_abbrev_tac `option_CASE answer _ _` >>
      Cases_on `answer` >> pure_rewrite_tac[optionTheory.option_case_def] >> BETA_TAC
      >- irule root_replay_finish >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_set_return_data >> irule root_replay_finish) >>
  irule root_replay_get_call_data
QED

Theorem root_replay_precompile_ecadd:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    precompile_ecadd precompile_ecadd
Proof
  pure_rewrite_tac[precompile_ecadd_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_consume_gas >>
      qmatch_goalsub_abbrev_tac `option_CASE answer _ _` >>
      Cases_on `answer` >> pure_rewrite_tac[optionTheory.option_case_def] >> BETA_TAC
      >- irule root_replay_fail >>
      qmatch_goalsub_abbrev_tac `pair_CASE coords _` >> Cases_on `coords` >>
      pure_rewrite_tac[pairTheory.pair_case_def] >> BETA_TAC >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_set_return_data >> irule root_replay_finish) >>
  irule root_replay_get_call_data
QED

Theorem root_replay_precompile_ecmul:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    precompile_ecmul precompile_ecmul
Proof
  pure_rewrite_tac[precompile_ecmul_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_consume_gas >>
      qmatch_goalsub_abbrev_tac `option_CASE answer _ _` >>
      Cases_on `answer` >> pure_rewrite_tac[optionTheory.option_case_def] >> BETA_TAC
      >- irule root_replay_fail >>
      qmatch_goalsub_abbrev_tac `pair_CASE coords _` >> Cases_on `coords` >>
      pure_rewrite_tac[pairTheory.pair_case_def] >> BETA_TAC >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_set_return_data >> irule root_replay_finish) >>
  irule root_replay_get_call_data
QED

Theorem root_replay_precompile_ecpairing:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    precompile_ecpairing precompile_ecpairing
Proof
  pure_rewrite_tac[precompile_ecpairing_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_consume_gas >>
      IF_CASES_TAC >> pure_rewrite_tac[COND_CLAUSES]
      >- irule root_replay_fail >>
      qmatch_goalsub_abbrev_tac `option_CASE answer _ _` >>
      Cases_on `answer` >> pure_rewrite_tac[optionTheory.option_case_def] >> BETA_TAC
      >- irule root_replay_fail >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_set_return_data >> irule root_replay_finish) >>
  irule root_replay_get_call_data
QED

Theorem root_replay_precompile_blake2f:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    precompile_blake2f precompile_blake2f
Proof
  pure_rewrite_tac[precompile_blake2f_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      IF_CASES_TAC >> pure_rewrite_tac[COND_CLAUSES]
      >- irule root_replay_fail >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_consume_gas >>
      IF_CASES_TAC >> pure_rewrite_tac[COND_CLAUSES]
      >- irule root_replay_fail >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_set_return_data >> irule root_replay_finish) >>
  irule root_replay_get_call_data
QED

Theorem root_replay_precompile_p256verify:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    precompile_p256verify precompile_p256verify
Proof
  pure_rewrite_tac[precompile_p256verify_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_consume_gas >>
      IF_CASES_TAC >> pure_rewrite_tac[COND_CLAUSES]
      >- irule root_replay_finish >>
      IF_CASES_TAC >> pure_rewrite_tac[COND_CLAUSES]
      >- (irule root_replay_ignore_bind_exact >> conj_tac
          >- irule root_replay_set_return_data >> irule root_replay_finish) >>
      irule root_replay_finish) >>
  irule root_replay_get_call_data
QED

Theorem root_replay_precompile_point_eval:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    precompile_point_eval precompile_point_eval
Proof
  pure_rewrite_tac[precompile_point_eval_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      IF_CASES_TAC >> pure_rewrite_tac[COND_CLAUSES]
      >- irule root_replay_fail >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_consume_gas >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_assert >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_assert >>
      qmatch_goalsub_abbrev_tac `pair_CASE options _` >> Cases_on `options` >>
      pure_rewrite_tac[pairTheory.pair_case_def] >> BETA_TAC >>
      qmatch_goalsub_abbrev_tac `option_CASE first _ _` >>
      Cases_on `first` >> pure_rewrite_tac[optionTheory.option_case_def] >> BETA_TAC
      >- irule root_replay_fail >>
      qmatch_goalsub_abbrev_tac `option_CASE second _ _` >>
      Cases_on `second` >> pure_rewrite_tac[optionTheory.option_case_def] >> BETA_TAC
      >- irule root_replay_fail >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_assert >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_set_return_data >> irule root_replay_finish) >>
  irule root_replay_get_call_data
QED

Theorem root_replay_dispatch_precompiles:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (dispatch_precompiles address) (dispatch_precompiles address)
Proof
  pure_rewrite_tac[dispatch_precompiles_def] >> rpt IF_CASES_TAC >>
  simp[root_replay_precompile_ecrecover, root_replay_precompile_sha2_256,
       root_replay_precompile_ripemd_160, root_replay_precompile_identity,
       root_replay_precompile_modexp, root_replay_precompile_ecadd,
       root_replay_precompile_ecmul, root_replay_precompile_ecpairing,
       root_replay_precompile_blake2f, root_replay_precompile_point_eval,
       root_replay_precompile_bls_g1add, root_replay_precompile_bls_g1msm,
       root_replay_precompile_bls_g2add, root_replay_precompile_bls_g2msm,
       root_replay_precompile_bls_pairing, root_replay_precompile_bls_map_fp_to_g1,
       root_replay_precompile_bls_map_fp2_to_g2, root_replay_precompile_p256verify,
       root_replay_fail]
QED

Theorem root_replay_proceed_call:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (proceed_call op sender address value off sz code gas output)
    (proceed_call op sender address value off sz code gas output)
Proof
  pure_rewrite_tac[proceed_call_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_bind_exact >> conj_tac
      >- (gen_tac >> BETA_TAC >>
          irule root_replay_ignore_bind_exact >> conj_tac
          >- (IF_CASES_TAC >> pure_rewrite_tac[COND_CLAUSES]
              >- irule root_replay_update_accounts >>
              irule root_replay_return >> simp[]) >>
          irule root_replay_bind_exact >> conj_tac
          >- (gen_tac >> BETA_TAC >>
              irule root_replay_bind_exact >> conj_tac
              >- (gen_tac >> BETA_TAC >>
                  irule root_replay_bind_exact >> conj_tac
                  >- (gen_tac >> BETA_TAC >>
                      irule root_replay_ignore_bind_exact >> conj_tac
                      >- irule root_replay_push_context >>
                      IF_CASES_TAC >> pure_rewrite_tac[COND_CLAUSES]
                      >- irule root_replay_dispatch_precompiles >>
                      irule root_replay_return >> simp[]) >>
                  irule root_replay_get_static) >>
              irule root_replay_get_value) >>
          irule root_replay_get_caller) >>
      irule root_replay_read_memory) >>
  irule root_replay_get_rollback
QED

Theorem root_replay_step_call:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (step_call op) (step_call op)
Proof
  pure_rewrite_tac[step_call_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      qmatch_goalsub_abbrev_tac `max_expansion_range args_range ret_range` >>
      qabbrev_tac `xr = max_expansion_range args_range ret_range` >>
      Cases_on `xr` >>
      CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >> BETA_TAC >>
      suspend "memory") >>
  irule root_replay_pop_stack
QED

Resume root_replay_step_call[memory]:
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule root_replay_bind_exact >> conj_tac
      >- (gen_tac >> BETA_TAC >>
          irule root_replay_bind_exact >> conj_tac
          >- (gen_tac >> BETA_TAC >>
              irule root_replay_bind_exact >> conj_tac
              >- (gen_tac >> pairarg_tac >> asm_rewrite_tac[] >>
                  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >> BETA_TAC >>
                  suspend "gas") >>
              qmatch_goalsub_abbrev_tac `option_CASE delegate _ _` >>
              Cases_on `delegate` >>
              pure_rewrite_tac[optionTheory.option_case_def] >> BETA_TAC
              >- (irule root_replay_return >> simp[]) >>
              irule root_replay_bind_exact >> conj_tac
              >- (gen_tac >> BETA_TAC >> irule root_replay_return >> simp[]) >>
              irule root_replay_access_address) >>
          irule root_replay_get_accounts) >>
      irule root_replay_access_address) >>
  irule root_replay_memory_expansion_info
QED

Resume root_replay_step_call[gas]:
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      qmatch_goalsub_abbrev_tac `call_gas val gas_left gas_avail mem_cost rest_cost` >>
      qabbrev_tac `cg = call_gas val gas_left gas_avail mem_cost rest_cost` >>
      Cases_on `cg` >>
      CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >> BETA_TAC >>
      suspend "effects") >>
  irule root_replay_get_gas_left
QED

Resume root_replay_step_call[effects]:
  irule root_replay_ignore_bind_exact >> conj_tac
  >- irule root_replay_consume_gas >>
  irule root_replay_ignore_bind_exact >> conj_tac
  >- (IF_CASES_TAC >> pure_rewrite_tac[COND_CLAUSES]
      >- irule root_replay_assert_not_static >>
      irule root_replay_return >> simp[]) >>
  irule root_replay_ignore_bind_exact >> conj_tac
  >- irule root_replay_expand_memory >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      IF_CASES_TAC >> pure_rewrite_tac[COND_CLAUSES]
      >- irule root_replay_abort_call_value >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_set_return_data >>
      irule root_replay_bind_exact >> conj_tac
      >- (gen_tac >> BETA_TAC >>
          IF_CASES_TAC >> pure_rewrite_tac[COND_CLAUSES]
          >- irule root_replay_abort_unuse >>
          irule root_replay_proceed_call) >>
      irule root_replay_get_num_contexts) >>
  irule root_replay_get_callee
QED

Finalise root_replay_step_call

Theorem root_replay_step_inst:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (step_inst op) (step_inst op)
Proof
  Cases_on `op` >> pure_rewrite_tac[step_inst_def] >>
  simp_tac bool_ss [root_replay_step_binop, root_replay_step_monop,
       root_replay_step_modop, root_replay_step_exp,
       root_replay_step_txParams, root_replay_step_keccak256,
       root_replay_step_balance, root_replay_step_call_data_load,
       root_replay_step_ext_code_size, root_replay_step_ext_code_copy,
       root_replay_step_return_data_copy, root_replay_step_ext_code_hash,
       root_replay_step_block_hash, root_replay_step_self_balance,
       root_replay_step_blob_hash, root_replay_step_pop,
       root_replay_step_mload, root_replay_step_mstore,
       root_replay_step_sload, root_replay_step_sstore,
       root_replay_step_jump, root_replay_step_jumpi,
       root_replay_consume_gas, root_replay_step_push,
       root_replay_step_dup, root_replay_step_swap, root_replay_step_log,
       root_replay_step_create, root_replay_step_call,
       root_replay_step_return, root_replay_fail,
       root_replay_step_self_destruct]
  >- (irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_set_return_data >> irule root_replay_finish) >>
  FIRST [irule root_replay_step_msgParams, irule root_replay_step_context,
         irule root_replay_step_copy_to_memory] >>
  simp[root_replay_get_call_data, root_replay_get_current_code]
QED

Theorem root_step_body_fetch_factor[local]:
  step_inner =
    bind (bind get_current_context
      (\c. return (c.msgParams.code, c.msgParams.parsed, c.pc)))
      (\(code, parsed, pc).
        case FLOOKUP parsed pc of
        | SOME op => ignore_bind (step_inst op) (inc_pc_or_jump op)
        | NONE => if LENGTH code <= pc then step_inst Stop else step_inst Invalid)
Proof
  simp[step_inner_def, bind_assoc, LET_THM]
QED

Theorem root_replay_step_body:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    step_inner step_inner
Proof
  pure_rewrite_tac[root_step_body_fetch_factor] >>
  irule root_replay_bind_exact >> conj_tac
  >- (gen_tac >> PairCases_on `x` >>
      CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >> BETA_TAC >>
      Cases_on `FLOOKUP x1 x2` >>
      pure_asm_rewrite_tac[optionTheory.option_CLAUSES] >> BETA_TAC
      >- (IF_CASES_TAC >> irule root_replay_step_inst) >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_step_inst >> irule root_replay_inc_pc_or_jump) >>
  ho_match_mp_tac root_replay_context_read >> simp[]
QED

Theorem root_replay_exact_elim[local]:
  root_replay_judgement (root_output_to es)
    (root_replay_rel (root_output_to es))
    (\x s y t. x = y /\ root_replay_rel (root_output_to es) s t) f f /\
  es.contexts <> [] ==>
  ?r es'. f es = (r, es') /\ f (shadow_root es) = (r, shadow_root es') /\
          es'.contexts <> [] /\ root_output_to es' = root_output_to es
Proof
  strip_tac >>
  qpat_x_assum `root_replay_judgement _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[root_replay_judgement_def] >>
  disch_then (qspecl_then [`es`, `shadow_root es`] mp_tac) >>
  pure_rewrite_tac[root_replay_rel_def] >> simp[] >>
  Cases_on `f es` >> Cases_on `f (shadow_root es)` >>
  Cases_on `q` >> Cases_on `q'` >> gvs[] >> metis_tac[]
QED

Theorem shadow_root_step_body_raw:
  es.contexts <> [] ==>
  ?r es'. step_inner es = (r, es') /\
          step_inner (shadow_root es) = (r, shadow_root es') /\
          es'.contexts <> [] /\ root_output_to es' = root_output_to es
Proof
  strip_tac >> irule root_replay_exact_elim >>
  pure_rewrite_tac[root_replay_step_body, AND_CLAUSES] >> simp[]
QED

Theorem shadow_root_handle_halt_singleton:
  mid.contexts = [(ctxt, rb)] ==>
  handle_step NONE (shadow_root mid) = (INR NONE, shadow_root mid)
Proof
  strip_tac >>
  simp[handle_step_def, handle_def, handle_create_def, handle_exception_def,
       get_return_data_def, get_output_to_def, get_num_contexts_def,
       get_current_context_def, bind_def, ignore_bind_def, return_def,
       reraise_def, shadow_root_def, shadow_root_contexts_def]
QED

Theorem handle_create_exception_nonempty:
  es.contexts <> [] ==>
  handle_create (SOME exc) es = (INR (SOME exc), es)
Proof
  strip_tac >>
  Cases_on `es.contexts` >> gvs[] >> PairCases_on `h` >>
  simp[handle_create_def, get_return_data_def, get_output_to_def,
       get_current_context_def, bind_def, return_def, reraise_def] >>
  Cases_on `h0.msgParams.outputTo` >> simp[reraise_def]
QED
Theorem root_replay_nested_get_output_to:
  root_replay_judgement d
    (\s t. root_replay_rel d s t /\ 1 < LENGTH s.contexts)
    (\x s y t. x = y /\ root_replay_rel d s t /\ 1 < LENGTH s.contexts)
    get_output_to get_output_to
Proof
  simp[root_replay_judgement_def, root_replay_rel_def] >> rpt strip_tac >>
  Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >>
  rename1 `s.contexts = (h0,h1)::cs` >>
  `cs <> []` by (Cases_on `cs` >> gvs[]) >>
  simp[get_output_to_def, get_current_context_def, bind_def, return_def,
       shadow_root_def, shadow_root_contexts_def]
QED

Theorem root_replay_nested_pop_context:
  root_replay_judgement d
    (\s t. root_replay_rel d s t /\ 1 < LENGTH s.contexts)
    (\x s y t. x = y /\ root_replay_rel d s t)
    pop_context pop_context
Proof
  simp[root_replay_judgement_def, root_replay_rel_def] >> rpt strip_tac >>
  Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >>
  rename1 `s.contexts = (h0,h1)::cs` >>
  `cs <> []` by (Cases_on `cs` >> gvs[]) >>
  simp[pop_context_def, return_def, shadow_root_def, shadow_root_contexts_def,
       root_output_to_def, LAST_DEF]
QED

Theorem root_replay_nested_frame[local]:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t) f f /\
  (!s x s'. f s = (INL x, s') ==> LENGTH s'.contexts = LENGTH s.contexts) ==>
  root_replay_judgement d
    (\s t. root_replay_rel d s t /\ 1 < LENGTH s.contexts)
    (\x s y t. (x = y /\ root_replay_rel d s t) /\ 1 < LENGTH s.contexts) f f
Proof
  strip_tac >> ho_match_mp_tac root_replay_success_frame >> rpt conj_tac
  >- (irule root_replay_consequence >> goal_assum (drule_at Any) >> simp[])
  >- simp[] >> metis_tac[]
QED

Theorem get_gas_left_context_length[local]:
  get_gas_left s = (r, s') ==> LENGTH s'.contexts = LENGTH s.contexts
Proof
  simp[get_gas_left_def, get_current_context_def, bind_def, return_def,
       fail_def, AllCaseEqs()] >> rw[]
QED

Theorem root_replay_nested_get_gas_left:
  root_replay_judgement d
    (\s t. root_replay_rel d s t /\ 1 < LENGTH s.contexts)
    (\x s y t. (x = y /\ root_replay_rel d s t) /\ 1 < LENGTH s.contexts)
    get_gas_left get_gas_left
Proof
  irule root_replay_nested_frame >>
  simp[root_replay_get_gas_left, get_gas_left_context_length]
QED


Theorem consume_gas_context_length[local]:
  consume_gas n s = (r, s') ==> LENGTH s'.contexts = LENGTH s.contexts
Proof
  simp[consume_gas_def, get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, assert_def, fail_def, AllCaseEqs()] >> rw[] >>
  gvs[assert_def, ignore_bind_def, bind_def, set_current_context_def,
      return_def, fail_def, AllCaseEqs()] >> Cases_on `s.contexts` >> gvs[]
QED

Theorem set_return_data_context_length[local]:
  set_return_data rd s = (r, s') ==> LENGTH s'.contexts = LENGTH s.contexts
Proof
  Cases_on `s.contexts` >>
  simp[set_return_data_def, get_current_context_def, set_current_context_def,
       bind_def, return_def, fail_def, AllCaseEqs()] >> rw[] >> gvs[]
QED

Theorem get_return_data_context_length[local]:
  get_return_data s = (r, s') ==> LENGTH s'.contexts = LENGTH s.contexts
Proof
  simp[get_return_data_def, get_current_context_def, bind_def, return_def,
       fail_def, AllCaseEqs()] >> rw[]
QED

Theorem root_replay_nested_consume_gas:
  root_replay_judgement d
    (\s t. root_replay_rel d s t /\ 1 < LENGTH s.contexts)
    (\x s y t. (x = y /\ root_replay_rel d s t) /\ 1 < LENGTH s.contexts)
    (consume_gas n) (consume_gas n)
Proof
  irule root_replay_nested_frame >>
  simp[root_replay_consume_gas] >> metis_tac[consume_gas_context_length]
QED

Theorem root_replay_nested_set_return_data:
  root_replay_judgement d
    (\s t. root_replay_rel d s t /\ 1 < LENGTH s.contexts)
    (\x s y t. (x = y /\ root_replay_rel d s t) /\ 1 < LENGTH s.contexts)
    (set_return_data rd) (set_return_data rd)
Proof
  irule root_replay_nested_frame >>
  simp[root_replay_set_return_data] >> metis_tac[set_return_data_context_length]
QED

Theorem root_replay_nested_get_return_data:
  root_replay_judgement d
    (\s t. root_replay_rel d s t /\ 1 < LENGTH s.contexts)
    (\x s y t. (x = y /\ root_replay_rel d s t) /\ 1 < LENGTH s.contexts)
    get_return_data get_return_data
Proof
  irule root_replay_nested_frame >>
  simp[root_replay_get_return_data, get_return_data_context_length]
QED

Theorem root_replay_bind_through[local]:
  root_replay_judgement d P (\x s y t. x = y /\ Pnext s t) f f /\
  (!x. root_replay_judgement d Pnext Q (k x) (k x)) ==>
  root_replay_judgement d P Q (bind f k) (bind f k)
Proof
  strip_tac >> irule root_replay_bind >>
  qexists_tac `\x s y t. x = y /\ Pnext s t` >> simp[] >>
  qpat_x_assum `!x. _` mp_tac >> simp[root_replay_judgement_def]
QED

Theorem root_replay_nested_pop_and_incorporate:
  root_replay_judgement d
    (\s t. root_replay_rel d s t /\ 1 < LENGTH s.contexts)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (pop_and_incorporate_context success) (pop_and_incorporate_context success)
Proof
  pure_rewrite_tac[pop_and_incorporate_context_def, LET_THM] >> BETA_TAC >>
  irule root_replay_bind_through >>
  qexists_tac `\s t. root_replay_rel d s t /\ 1 < LENGTH s.contexts` >>
  reverse conj_tac
  >- (BETA_TAC >> pure_rewrite_tac[CONJ_ASSOC] >>
      irule root_replay_nested_get_gas_left) >>
  gen_tac >> BETA_TAC >>
  irule root_replay_bind_through >> qexists_tac `root_replay_rel d` >>
  reverse conj_tac >- irule root_replay_nested_pop_context >>
  gen_tac >> BETA_TAC >>
  irule root_replay_ignore_bind_exact >> conj_tac
  >- irule root_replay_unuse_gas >>
  Cases_on `success` >> pure_rewrite_tac[COND_CLAUSES]
  >- (irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_push_logs >> irule root_replay_update_gas_refund) >>
  irule root_replay_set_rollback
QED

Theorem root_replay_nested_num_contexts_bind[local]:
  (!n. 1 < n ==> root_replay_judgement d
    (\s t. root_replay_rel d s t /\ 1 < LENGTH s.contexts) Q (k n) (k n)) ==>
  root_replay_judgement d
    (\s t. root_replay_rel d s t /\ 1 < LENGTH s.contexts) Q
    (bind get_num_contexts k) (bind get_num_contexts k)
Proof
  simp_tac bool_ss[root_replay_judgement_def] >> rpt strip_tac >>
  simp[get_num_contexts_def, bind_def, return_def] >>
  `LENGTH t.contexts = LENGTH s.contexts` by
    gvs[root_replay_rel_def, shadow_root_def, shadow_root_contexts_length] >>
  asm_rewrite_tac[] >>
  first_x_assum (qspec_then `LENGTH s.contexts` mp_tac) >>
  simp[] >> disch_then (qspecl_then [`s`, `t`] mp_tac) >>
  simp[] >> Cases_on `k (LENGTH s.contexts) s` >>
  Cases_on `k (LENGTH s.contexts) t` >> simp[]
QED

Theorem root_replay_exception_caller[local]:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (do inc_pc;
        case outputTo of
        | Code address => if success then do set_return_data []; push_stack (w2w address) od
                          else do set_return_data output; push_stack (b2w F) od
        | Memory r => do set_return_data output; push_stack (b2w success);
                         write_memory r.offset (TAKE r.size output) od od)
    (do inc_pc;
        case outputTo of
        | Code address => if success then do set_return_data []; push_stack (w2w address) od
                          else do set_return_data output; push_stack (b2w F) od
        | Memory r => do set_return_data output; push_stack (b2w success);
                         write_memory r.offset (TAKE r.size output) od od)
Proof
  irule root_replay_ignore_bind_exact >> conj_tac
  >- irule root_replay_inc_pc >>
  Cases_on `outputTo` >> pure_rewrite_tac[return_destination_case_def] >> BETA_TAC
  >- (irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_set_return_data >>
      irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_push_stack >> irule root_replay_write_memory) >>
  Cases_on `success` >> simp_tac bool_ss[] >>
  (irule root_replay_ignore_bind_exact >> conj_tac
   >- irule root_replay_set_return_data >> irule root_replay_push_stack)
QED

Theorem root_replay_nested_exception_finish[local]:
  root_replay_judgement d
    (\s t. root_replay_rel d s t /\ 1 < LENGTH s.contexts)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (do output <- get_return_data; outputTo <- get_output_to;
        pop_and_incorporate_context success; inc_pc;
        case outputTo of
        | Code address => if success then do set_return_data []; push_stack (w2w address) od
                          else do set_return_data output; push_stack (b2w F) od
        | Memory r => do set_return_data output; push_stack (b2w success);
                         write_memory r.offset (TAKE r.size output) od od)
    (do output <- get_return_data; outputTo <- get_output_to;
        pop_and_incorporate_context success; inc_pc;
        case outputTo of
        | Code address => if success then do set_return_data []; push_stack (w2w address) od
                          else do set_return_data output; push_stack (b2w F) od
        | Memory r => do set_return_data output; push_stack (b2w success);
                         write_memory r.offset (TAKE r.size output) od od)
Proof
  irule root_replay_bind_through >>
  qexists_tac `\s t. root_replay_rel d s t /\ 1 < LENGTH s.contexts` >>
  reverse conj_tac
  >- (BETA_TAC >> pure_rewrite_tac[CONJ_ASSOC] >> irule root_replay_nested_get_return_data) >>
  gen_tac >> BETA_TAC >> irule root_replay_bind_through >>
  qexists_tac `\s t. root_replay_rel d s t /\ 1 < LENGTH s.contexts` >>
  reverse conj_tac >- (BETA_TAC >> irule root_replay_nested_get_output_to) >>
  gen_tac >> BETA_TAC >> pure_rewrite_tac[ignore_bind_def] >>
  irule root_replay_bind_through >> qexists_tac `root_replay_rel d` >>
  reverse conj_tac >- irule root_replay_nested_pop_and_incorporate >>
  gen_tac >> BETA_TAC >>
  pure_rewrite_tac[GSYM ignore_bind_def] >> irule root_replay_exception_caller
QED

Theorem root_replay_nested_exception_prepare[local]:
  root_replay_judgement d
    (\s t. root_replay_rel d s t /\ 1 < LENGTH s.contexts)
    (\x s y t. x = y /\ root_replay_rel d s t /\ 1 < LENGTH s.contexts)
    (if ~success /\ e <> SOME Reverted then
       do gasLeft <- get_gas_left; consume_gas gasLeft; set_return_data [] od
     else return ())
    (if ~success /\ e <> SOME Reverted then
       do gasLeft <- get_gas_left; consume_gas gasLeft; set_return_data [] od
     else return ())
Proof
  Cases_on `~success /\ e <> SOME Reverted` >> asm_rewrite_tac[]
  >- (irule root_replay_bind_through >>
      qexists_tac `\s t. root_replay_rel d s t /\ 1 < LENGTH s.contexts` >>
      reverse conj_tac
      >- (BETA_TAC >> pure_rewrite_tac[CONJ_ASSOC] >> irule root_replay_nested_get_gas_left) >>
      gen_tac >> BETA_TAC >> pure_rewrite_tac[ignore_bind_def] >>
      irule root_replay_bind_through >>
      qexists_tac `\s t. root_replay_rel d s t /\ 1 < LENGTH s.contexts` >>
      reverse conj_tac
      >- (BETA_TAC >> pure_rewrite_tac[CONJ_ASSOC] >> irule root_replay_nested_consume_gas) >>
      gen_tac >> BETA_TAC >> pure_rewrite_tac[CONJ_ASSOC] >>
      irule root_replay_nested_set_return_data) >>
  irule root_replay_return >> simp[]
QED

Theorem root_replay_nested_handle_exception:
  root_replay_judgement d
    (\s t. root_replay_rel d s t /\ 1 < LENGTH s.contexts)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (handle_exception e) (handle_exception e)
Proof
  pure_rewrite_tac[handle_exception_def, LET_THM] >> BETA_TAC >>
  pure_rewrite_tac[ignore_bind_def] >>
  irule root_replay_bind_through >>
  qexists_tac `\s t. root_replay_rel d s t /\ 1 < LENGTH s.contexts` >>
  reverse conj_tac
  >- (BETA_TAC >> pure_rewrite_tac[GSYM ignore_bind_def] >>
      irule root_replay_nested_exception_prepare) >>
  gen_tac >> BETA_TAC >> irule root_replay_nested_num_contexts_bind >>
  rpt strip_tac >> `~(n <= 1)` by decide_tac >>
  BETA_TAC >> asm_rewrite_tac[] >>
  pure_rewrite_tac[GSYM ignore_bind_def] >>
  irule root_replay_nested_exception_finish
QED

Theorem replay_bind_no_halt[local]:
  (!s t. f s <> (INR NONE,t)) /\
  (!x s t. k x s <> (INR NONE,t)) ==>
  !s t. bind f k s <> (INR NONE,t)
Proof
  rpt strip_tac >> Cases_on `f s` >> Cases_on `q` >>
  gvs[bind_def] >> metis_tac[]
QED

Theorem replay_context_read_no_halt[local]:
  !s t. get_current_context s <> (INR NONE,t)
Proof
  simp[get_current_context_def, return_def, fail_def, AllCaseEqs()]
QED

Theorem replay_context_write_no_halt[local]:
  !s t. set_current_context c s <> (INR NONE,t)
Proof
  simp[set_current_context_def, return_def, fail_def, AllCaseEqs()]
QED

Theorem replay_get_gas_left_no_halt[local]:
  !s t. get_gas_left s <> (INR NONE,t)
Proof
  pure_rewrite_tac[get_gas_left_def] >> irule replay_bind_no_halt >>
  simp[replay_context_read_no_halt, return_def]
QED

Theorem replay_consume_gas_no_halt[local]:
  !s t. consume_gas n s <> (INR NONE,t)
Proof
  pure_rewrite_tac[consume_gas_def] >> irule replay_bind_no_halt >>
  conj_tac >- simp[replay_context_read_no_halt] >>
  gen_tac >> BETA_TAC >> pure_rewrite_tac[LET_THM, ignore_bind_def] >> BETA_TAC >>
  irule replay_bind_no_halt >> simp[assert_def, return_def, fail_def,
    replay_context_write_no_halt, AllCaseEqs()]
QED

Theorem replay_set_return_data_no_halt[local]:
  !s t. set_return_data rd s <> (INR NONE,t)
Proof
  pure_rewrite_tac[set_return_data_def] >> irule replay_bind_no_halt >>
  conj_tac >- simp[replay_context_read_no_halt] >>
  gen_tac >> BETA_TAC >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  simp[replay_context_write_no_halt]
QED

Theorem replay_get_return_data_no_halt[local]:
  !s t. get_return_data s <> (INR NONE,t)
Proof
  pure_rewrite_tac[get_return_data_def] >> irule replay_bind_no_halt >>
  simp[replay_context_read_no_halt, return_def]
QED

Theorem replay_get_output_to_no_halt[local]:
  !s t. get_output_to s <> (INR NONE,t)
Proof
  pure_rewrite_tac[get_output_to_def] >> irule replay_bind_no_halt >>
  simp[replay_context_read_no_halt, return_def]
QED

Theorem replay_inc_pc_no_halt[local]:
  !s t. inc_pc s <> (INR NONE,t)
Proof
  pure_rewrite_tac[inc_pc_def] >> irule replay_bind_no_halt >>
  simp[replay_context_read_no_halt, replay_context_write_no_halt]
QED

Theorem replay_push_stack_no_halt[local]:
  !s t. push_stack w s <> (INR NONE,t)
Proof
  simp[push_stack_def, get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, fail_def, assert_def, AllCaseEqs()]
QED

Theorem replay_write_memory_no_halt[local]:
  !s t. write_memory offset bytes s <> (INR NONE,t)
Proof
  simp[write_memory_def, get_current_context_def, set_current_context_def,
       bind_def, return_def, fail_def, AllCaseEqs()]
QED

Theorem replay_pop_context_no_halt[local]:
  !s t. pop_context s <> (INR NONE,t)
Proof
  simp[pop_context_def, return_def, fail_def, AllCaseEqs()]
QED

Theorem replay_unuse_gas_no_halt[local]:
  !s t. unuse_gas n s <> (INR NONE,t)
Proof
  pure_rewrite_tac[unuse_gas_def] >> irule replay_bind_no_halt >>
  conj_tac >- simp[replay_context_read_no_halt] >>
  gen_tac >> BETA_TAC >> pure_rewrite_tac[ignore_bind_def] >>
  irule replay_bind_no_halt >>
  simp[assert_def, return_def, fail_def, replay_context_write_no_halt,
       LET_THM, AllCaseEqs()]
QED

Theorem replay_push_logs_no_halt[local]:
  !s t. push_logs ls s <> (INR NONE,t)
Proof
  pure_rewrite_tac[push_logs_def] >> irule replay_bind_no_halt >>
  simp[replay_context_read_no_halt, replay_context_write_no_halt]
QED

Theorem replay_update_gas_refund_no_halt[local]:
  !s t. update_gas_refund refunds s <> (INR NONE,t)
Proof
  PairCases_on `refunds` >> pure_rewrite_tac[update_gas_refund_def] >>
  irule replay_bind_no_halt >>
  simp[replay_context_read_no_halt, replay_context_write_no_halt]
QED

Theorem replay_set_rollback_no_halt[local]:
  !s t. set_rollback rb s <> (INR NONE,t)
Proof
  simp[set_rollback_def, return_def]
QED

Theorem replay_pop_and_incorporate_no_halt[local]:
  !s t. pop_and_incorporate_context success s <> (INR NONE,t)
Proof
  pure_rewrite_tac[pop_and_incorporate_context_def, LET_THM] >> BETA_TAC >>
  irule replay_bind_no_halt >> conj_tac
  >- simp[replay_get_gas_left_no_halt] >>
  gen_tac >> BETA_TAC >> irule replay_bind_no_halt >> conj_tac
  >- simp[replay_pop_context_no_halt] >>
  gen_tac >> BETA_TAC >> pure_rewrite_tac[ignore_bind_def] >>
  irule replay_bind_no_halt >> conj_tac
  >- simp[replay_unuse_gas_no_halt] >>
  gen_tac >> BETA_TAC >> Cases_on `success` >> pure_rewrite_tac[COND_CLAUSES]
  >- (irule replay_bind_no_halt >>
      simp[replay_push_logs_no_halt, replay_update_gas_refund_no_halt]) >>
  simp[replay_set_rollback_no_halt]
QED

Theorem replay_exception_caller_no_halt[local]:
  !s t. (do inc_pc;
        case outputTo of
        | Code address => if success then do set_return_data []; push_stack (w2w address) od
                          else do set_return_data output; push_stack (b2w F) od
        | Memory r => do set_return_data output; push_stack (b2w success);
                         write_memory r.offset (TAKE r.size output) od od) s <> (INR NONE,t)
Proof
  pure_rewrite_tac[ignore_bind_def] >> irule replay_bind_no_halt >> conj_tac
  >- simp[replay_inc_pc_no_halt] >>
  gen_tac >> BETA_TAC >> Cases_on `outputTo` >>
  pure_rewrite_tac[return_destination_case_def] >> BETA_TAC
  >- (irule replay_bind_no_halt >> conj_tac
      >- simp[replay_set_return_data_no_halt] >>
      gen_tac >> BETA_TAC >> irule replay_bind_no_halt >>
      simp[replay_push_stack_no_halt, replay_write_memory_no_halt]) >>
  Cases_on `success` >> pure_rewrite_tac[COND_CLAUSES] >>
  (irule replay_bind_no_halt >>
   simp[replay_set_return_data_no_halt, replay_push_stack_no_halt])
QED

Theorem replay_exception_finish_no_halt[local]:
  !s t. (do output <- get_return_data; outputTo <- get_output_to;
        pop_and_incorporate_context success; inc_pc;
        case outputTo of
        | Code address => if success then do set_return_data []; push_stack (w2w address) od
                          else do set_return_data output; push_stack (b2w F) od
        | Memory r => do set_return_data output; push_stack (b2w success);
                         write_memory r.offset (TAKE r.size output) od od) s <> (INR NONE,t)
Proof
  irule replay_bind_no_halt >> conj_tac
  >- simp[replay_get_return_data_no_halt] >>
  gen_tac >> BETA_TAC >> irule replay_bind_no_halt >> conj_tac
  >- simp[replay_get_output_to_no_halt] >>
  gen_tac >> BETA_TAC >> pure_rewrite_tac[ignore_bind_def] >>
  irule replay_bind_no_halt >> conj_tac
  >- simp[replay_pop_and_incorporate_no_halt] >>
  gen_tac >> BETA_TAC >> pure_rewrite_tac[GSYM ignore_bind_def] >>
  simp[replay_exception_caller_no_halt]
QED

Theorem replay_exception_prepare_length[local]:
  (if ~success /\ e <> SOME Reverted then
     do gasLeft <- get_gas_left; consume_gas gasLeft; set_return_data [] od
   else return ()) s = (r,s') ==>
  LENGTH s'.contexts = LENGTH s.contexts /\ r <> INR NONE
Proof
  Cases_on `~success /\ e <> SOME Reverted` >> asm_rewrite_tac[return_def]
  >- (pure_rewrite_tac[ignore_bind_def] >>
      Cases_on `get_gas_left s` >> Cases_on `q` >> simp[bind_def]
      >- (rename1 `get_gas_left s = (INL gas,smid)` >>
          Cases_on `consume_gas gas smid` >> Cases_on `q` >> simp[bind_def] >>
          metis_tac[get_gas_left_context_length, consume_gas_context_length,
            set_return_data_context_length, replay_consume_gas_no_halt,
            replay_set_return_data_no_halt]) >>
      strip_tac >> gvs[] >>
      drule get_gas_left_context_length >> strip_tac >> simp[] >>
      Cases_on `y` >> gvs[replay_get_gas_left_no_halt]) >>
  rw[]
QED

Theorem handle_exception_nested_no_halt:
  1 < LENGTH s.contexts ==> handle_exception e s <> (INR NONE,t)
Proof
  strip_tac >> pure_rewrite_tac[handle_exception_def, LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `ignore_bind prep _ s` >>
  `!r sp. prep s = (r,sp) ==>
      LENGTH sp.contexts = LENGTH s.contexts /\ r <> INR NONE` by
    (unabbrev_all_tac >> rpt strip_tac >>
     drule replay_exception_prepare_length >> simp[]) >>
  Cases_on `prep s` >>
  `LENGTH r.contexts = LENGTH s.contexts /\ q <> INR NONE` by metis_tac[] >>
  Cases_on `q` >>
  pure_rewrite_tac[ignore_bind_def] >> simp[Once bind_def]
  >- (rename1 `prep s = (INL x,sp)` >>
      `~(LENGTH sp.contexts <= 1)` by decide_tac >>
      simp[get_num_contexts_def, Once bind_def, return_def] >>
      pure_rewrite_tac[GSYM ignore_bind_def] >>
      qspec_then `sp` mp_tac
        (Q.INST [`success` |-> `(e:exception option) = NONE`] replay_exception_finish_no_halt) >>
      simp[]) >>
  gvs[]
QED

Theorem replay_bind_context_length[local]:
  (!s r s'. f s = (r,s') ==> LENGTH s'.contexts = LENGTH s.contexts) /\
  (!x s r s'. k x s = (r,s') ==> LENGTH s'.contexts = LENGTH s.contexts) ==>
  !s r s'. bind f k s = (r,s') ==> LENGTH s'.contexts = LENGTH s.contexts
Proof
  strip_tac >> rpt gen_tac >> Cases_on `f s` >> Cases_on `q` >>
  simp[bind_def] >> metis_tac[]
QED

Theorem replay_create_read_lengths[local]:
  (!s r s'. get_return_data s = (r,s') ==> LENGTH s'.contexts = LENGTH s.contexts) /\
  (!s r s'. get_output_to s = (r,s') ==> LENGTH s'.contexts = LENGTH s.contexts)
Proof
  conj_tac >- metis_tac[get_return_data_context_length] >>
  simp[get_output_to_def, get_current_context_def, bind_def, return_def,
       fail_def, AllCaseEqs()] >> rw[]
QED

Theorem replay_update_accounts_context_length[local]:
  update_accounts f s = (r,s') ==> LENGTH s'.contexts = LENGTH s.contexts
Proof
  simp[update_accounts_def, return_def] >> rw[] >> simp[]
QED

Theorem handle_create_context_length:
  !e s r s'. handle_create e s = (r,s') ==>
    LENGTH s'.contexts = LENGTH s.contexts
Proof
  gen_tac >> pure_rewrite_tac[handle_create_def] >>
  ho_match_mp_tac replay_bind_context_length >> conj_tac
  >- metis_tac[replay_create_read_lengths] >>
  gen_tac >> BETA_TAC >> ho_match_mp_tac replay_bind_context_length >> conj_tac
  >- metis_tac[replay_create_read_lengths] >>
  qx_gen_tac `outputTo` >> BETA_TAC >> Cases_on `e` >> Cases_on `outputTo` >>
  simp_tac bool_ss[optionTheory.option_case_def, return_destination_case_def, pairTheory.pair_case_thm] >>
  BETA_TAC >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  pure_rewrite_tac[ignore_bind_def] >>
  simp[reraise_def] >>
  ho_match_mp_tac replay_bind_context_length >> conj_tac
  >- (simp[assert_def, return_def, fail_def, AllCaseEqs()] >> rw[]) >>
  gen_tac >> BETA_TAC >> ho_match_mp_tac replay_bind_context_length >> conj_tac
  >- metis_tac[consume_gas_context_length] >>
  gen_tac >> BETA_TAC >> ho_match_mp_tac replay_bind_context_length >> conj_tac
  >- (simp[assert_def, return_def, fail_def, AllCaseEqs()] >> rw[]) >>
  gen_tac >> BETA_TAC >> ho_match_mp_tac replay_bind_context_length >> conj_tac
  >- metis_tac[replay_update_accounts_context_length] >>
  simp[reraise_def] >> rw[]
QED

Theorem root_replay_create_deposit[local]:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (do assert prefix_ok InvalidContractPrefix; consume_gas gas;
        assert size_ok OutOfGas; update_accounts f; reraise e od)
    (do assert prefix_ok InvalidContractPrefix; consume_gas gas;
        assert size_ok OutOfGas; update_accounts f; reraise e od)
Proof
  irule root_replay_ignore_bind_exact >> conj_tac
  >- irule root_replay_assert >>
  irule root_replay_ignore_bind_exact >> conj_tac
  >- irule root_replay_consume_gas >>
  irule root_replay_ignore_bind_exact >> conj_tac
  >- irule root_replay_assert >>
  irule root_replay_ignore_bind_exact >> conj_tac
  >- irule root_replay_update_accounts >>
  irule root_replay_reraise >> simp[]
QED

Theorem root_replay_nested_weaken[local]:
  root_replay_judgement d (root_replay_rel d) Q f f ==>
  root_replay_judgement d
    (\s t. root_replay_rel d s t /\ 1 < LENGTH s.contexts) Q f f
Proof
  strip_tac >> irule root_replay_consequence >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem root_replay_nested_handle_create:
  root_replay_judgement d
    (\s t. root_replay_rel d s t /\ 1 < LENGTH s.contexts)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (handle_create e) (handle_create e)
Proof
  pure_rewrite_tac[handle_create_def] >> irule root_replay_bind_through >>
  qexists_tac `\s t. root_replay_rel d s t /\ 1 < LENGTH s.contexts` >>
  reverse conj_tac
  >- (BETA_TAC >> pure_rewrite_tac[CONJ_ASSOC] >> irule root_replay_nested_get_return_data) >>
  gen_tac >> BETA_TAC >> irule root_replay_bind_through >>
  qexists_tac `\s t. root_replay_rel d s t /\ 1 < LENGTH s.contexts` >>
  reverse conj_tac >- (BETA_TAC >> irule root_replay_nested_get_output_to) >>
  qx_gen_tac `outputTo` >> BETA_TAC >> irule root_replay_nested_weaken >>
  Cases_on `e`
  >- (Cases_on `outputTo` >>
      simp_tac bool_ss[optionTheory.option_case_def, return_destination_case_def,
        pairTheory.pair_case_thm] >> BETA_TAC
      >- (irule root_replay_reraise >> simp[]) >>
      pure_rewrite_tac[LET_THM] >> BETA_TAC >> irule root_replay_create_deposit) >>
  Cases_on `outputTo` >>
  simp_tac bool_ss[optionTheory.option_case_def, return_destination_case_def,
    pairTheory.pair_case_thm] >> BETA_TAC >>
  (irule root_replay_reraise >> simp[])
QED

Theorem root_replay_nested_handle_step:
  root_replay_judgement d
    (\s t. root_replay_rel d s t /\ 1 < LENGTH s.contexts)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (handle_step e) (handle_step e)
Proof
  pure_rewrite_tac[handle_step_def] >> Cases_on `vfm_abort e` >> asm_rewrite_tac[]
  >- (irule root_replay_reraise >> simp[]) >>
  irule root_replay_handle_invariant >> reverse conj_tac
  >- irule root_replay_nested_handle_create >>
  qexists_tac `\s. 1 < LENGTH s.contexts` >> conj_tac
  >- (BETA_TAC >> rpt strip_tac >> drule handle_create_context_length >> simp[]) >>
  gen_tac >> BETA_TAC >> irule root_replay_nested_handle_exception
QED

Theorem root_replay_exception_prepare_exact[local]:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (if ~success /\ e <> SOME Reverted then
       do gasLeft <- get_gas_left; consume_gas gasLeft; set_return_data [] od
     else return ())
    (if ~success /\ e <> SOME Reverted then
       do gasLeft <- get_gas_left; consume_gas gasLeft; set_return_data [] od
     else return ())
Proof
  Cases_on `~success /\ e <> SOME Reverted` >> asm_rewrite_tac[]
  >- (irule root_replay_bind_exact >> reverse conj_tac
      >- irule root_replay_get_gas_left >>
      gen_tac >> BETA_TAC >> irule root_replay_ignore_bind_exact >> conj_tac
      >- irule root_replay_consume_gas >> irule root_replay_set_return_data) >>
  irule root_replay_return >> simp[]
QED

Theorem root_replay_singleton_exception_prepare[local]:
  root_replay_judgement d
    (\s t. root_replay_rel d s t /\ LENGTH s.contexts = 1)
    (\x s y t. (x = y /\ root_replay_rel d s t) /\ LENGTH s.contexts = 1)
    (if ~success /\ e <> SOME Reverted then
       do gasLeft <- get_gas_left; consume_gas gasLeft; set_return_data [] od
     else return ())
    (if ~success /\ e <> SOME Reverted then
       do gasLeft <- get_gas_left; consume_gas gasLeft; set_return_data [] od
     else return ())
Proof
  ho_match_mp_tac root_replay_success_frame >> rpt conj_tac
  >- (irule root_replay_consequence >>
      qexists_tac `root_replay_rel d` >>
      qexists_tac `\x s y t. x = y /\ root_replay_rel d s t` >>
      simp[root_replay_exception_prepare_exact])
  >- simp[] >> rpt strip_tac >> drule replay_exception_prepare_length >> simp[]
QED

Theorem root_replay_singleton_exception_read[local]:
  root_replay_judgement d
    (\s t. root_replay_rel d s t /\ LENGTH s.contexts = 1)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (bind get_num_contexts (\n. if n <= 1 then reraise e else k))
    (bind get_num_contexts (\n. if n <= 1 then reraise e else k))
Proof
  simp[root_replay_judgement_def, root_replay_rel_def, shadow_root_def,
       shadow_root_contexts_length, get_num_contexts_def, bind_def,
       return_def, reraise_def]
QED

Theorem root_replay_singleton_handle_exception:
  root_replay_judgement d
    (\s t. root_replay_rel d s t /\ LENGTH s.contexts = 1)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (handle_exception e) (handle_exception e)
Proof
  pure_rewrite_tac[handle_exception_def, LET_THM] >> BETA_TAC >>
  pure_rewrite_tac[ignore_bind_def] >> irule root_replay_bind_through >>
  qexists_tac `\s t. root_replay_rel d s t /\ LENGTH s.contexts = 1` >>
  reverse conj_tac
  >- (BETA_TAC >> pure_rewrite_tac[CONJ_ASSOC] >>
      pure_rewrite_tac[GSYM ignore_bind_def] >>
      irule root_replay_singleton_exception_prepare) >>
  gen_tac >> BETA_TAC >> irule root_replay_singleton_exception_read
QED

Theorem root_replay_handle_create_exception[local]:
  root_replay_judgement d (root_replay_rel d)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (handle_create (SOME exc)) (handle_create (SOME exc))
Proof
  simp[root_replay_judgement_def, root_replay_rel_def] >> rpt strip_tac >>
  ` (shadow_root s).contexts <> []` by
    simp[shadow_root_def, shadow_root_contexts_nil] >>
  simp[handle_create_exception_nonempty, root_replay_rel_def]
QED

Theorem root_replay_singleton_handle_step_exception:
  root_replay_judgement d
    (\s t. root_replay_rel d s t /\ LENGTH s.contexts = 1)
    (\x s y t. x = y /\ root_replay_rel d s t)
    (handle_step (SOME exc)) (handle_step (SOME exc))
Proof
  pure_rewrite_tac[handle_step_def] >>
  Cases_on `vfm_abort (SOME exc)` >> asm_rewrite_tac[]
  >- (irule root_replay_reraise >> simp[]) >>
  irule root_replay_handle_invariant >> reverse conj_tac
  >- (irule root_replay_consequence >>
      qexists_tac `root_replay_rel d` >>
      qexists_tac `\x s y t. x = y /\ root_replay_rel d s t` >>
      simp[root_replay_handle_create_exception]) >>
  qexists_tac `\s. LENGTH s.contexts = 1` >> conj_tac
  >- (BETA_TAC >> rpt strip_tac >> drule handle_create_context_length >> simp[]) >>
  gen_tac >> BETA_TAC >> irule root_replay_singleton_handle_exception
QED

Theorem replay_bind_no_return[local]:
  (!x s t. k x s <> (INL y,t)) ==> bind f k s <> (INL y,t)
Proof
  strip_tac >> Cases_on `f s` >> Cases_on `q` >> simp[bind_def]
QED

Theorem handle_create_no_return[local]:
  handle_create e s <> (INL x,t)
Proof
  pure_rewrite_tac[handle_create_def] >> irule replay_bind_no_return >>
  qx_gen_tac `code` >> rpt gen_tac >> BETA_TAC >>
  irule replay_bind_no_return >> qx_gen_tac `dest` >> rpt gen_tac >> BETA_TAC >>
  Cases_on `e` >> Cases_on `dest` >>
  simp_tac bool_ss[optionTheory.option_case_def, return_destination_case_def,
    pairTheory.pair_case_thm, LET_THM] >> BETA_TAC >>
  pure_rewrite_tac[ignore_bind_def] >>
  rpt (irule replay_bind_no_return >> rpt gen_tac >> BETA_TAC) >> simp[reraise_def]
QED

Theorem handle_step_nested_no_halt:
  1 < LENGTH s.contexts ==> handle_step e s <> (INR NONE,t)
Proof
  strip_tac >> pure_rewrite_tac[handle_step_def] >>
  Cases_on `vfm_abort e`
  >- (Cases_on `e` >> gvs[vfm_abort_def, reraise_def]) >>
  Cases_on `(handle_create e s : unit execution_result)` >>
  `LENGTH r.contexts = LENGTH s.contexts` by
    metis_tac[handle_create_context_length] >>
  Cases_on `q`
  >- metis_tac[handle_create_no_return] >>
  gvs[handle_def] >>
  irule handle_exception_nested_no_halt >> simp[]
QED

Theorem shadow_root_handle_step_exact[local]:
  es.contexts <> [] /\ (1 < LENGTH es.contexts \/ e <> NONE) ==>
  ?r es'. handle_step e es = (r,es') /\
    handle_step e (shadow_root es) = (r,shadow_root es') /\
    es'.contexts <> [] /\ root_output_to es' = root_output_to es
Proof
  strip_tac >>
  `root_replay_judgement (root_output_to es)
    (\s t. root_replay_rel (root_output_to es) s t /\
           (1 < LENGTH s.contexts \/ e <> NONE /\ LENGTH s.contexts = 1))
    (\x s y t. x = y /\ root_replay_rel (root_output_to es) s t)
    (handle_step e) (handle_step e)` by
    (simp_tac bool_ss[root_replay_judgement_def] >> rpt strip_tac
     >- (mp_tac (Q.INST [`d` |-> `root_output_to es`] root_replay_nested_handle_step) >>
         simp_tac bool_ss[root_replay_judgement_def] >> metis_tac[]) >>
     Cases_on `e` >- gvs[] >> rename1 `handle_step (SOME exc) s` >>
     mp_tac (Q.INST [`d` |-> `root_output_to es`] root_replay_singleton_handle_step_exception) >>
     simp_tac bool_ss[root_replay_judgement_def] >> metis_tac[]) >>
  qpat_x_assum `root_replay_judgement _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[root_replay_judgement_def] >>
  disch_then (qspecl_then [`es`, `shadow_root es`] mp_tac) >>
  pure_rewrite_tac[root_replay_rel_def] >>
  `LENGTH es.contexts = 1 \/ 1 < LENGTH es.contexts` by
    (Cases_on `es.contexts` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  simp[] >>
  Cases_on `handle_step e es` >> Cases_on `handle_step e (shadow_root es)` >>
  Cases_on `q` >> Cases_on `q'` >> gvs[] >> metis_tac[]
QED

Theorem handle_exception_some_no_halt[local]:
  handle_exception (SOME exc) s <> (INR NONE,t)
Proof
  pure_rewrite_tac[handle_exception_def, LET_THM] >> BETA_TAC >>
  pure_rewrite_tac[ignore_bind_def] >> irule replay_bind_no_halt >> conj_tac
  >- (pure_rewrite_tac[GSYM ignore_bind_def] >> rpt strip_tac >>
      drule replay_exception_prepare_length >> simp[]) >>
  gen_tac >> BETA_TAC >> irule replay_bind_no_halt >> conj_tac
  >- simp[get_num_contexts_def, return_def] >>
  gen_tac >> BETA_TAC >> IF_CASES_TAC >- simp[reraise_def] >>
  pure_rewrite_tac[GSYM ignore_bind_def] >>
  mp_tac (Q.INST [`success` |-> `(SOME exc:exception option) = NONE`]
    replay_exception_finish_no_halt) >> simp[]
QED

Theorem handle_step_some_no_halt[local]:
  s.contexts <> [] ==> handle_step (SOME exc) s <> (INR NONE,t)
Proof
  strip_tac >> simp[handle_step_def] >>
  Cases_on `vfm_abort (SOME exc)` >> simp[reraise_def] >>
  simp[handle_def, handle_create_exception_nonempty, handle_exception_some_no_halt]
QED

Theorem shadow_root_handle_step_nonhalt:
  es.contexts <> [] /\ r <> INR NONE /\
  handle_step e (shadow_root es) = (r,ghost) ==>
  ?es'. handle_step e es = (r,es') /\ es'.contexts <> [] /\
    shadow_root es' = ghost /\ root_output_to es' = root_output_to es
Proof
  strip_tac >> Cases_on `1 < LENGTH es.contexts \/ e <> NONE`
  >- (drule_all shadow_root_handle_step_exact >> strip_tac >> gvs[] >> metis_tac[]) >>
  gvs[] >> Cases_on `es.contexts` >> gvs[] >>
  Cases_on `t` >> gvs[] >> PairCases_on `h` >>
  drule shadow_root_handle_halt_singleton >> gvs[]
QED

Theorem shadow_root_handle_step_halt:
  es.contexts <> [] /\ handle_step e (shadow_root es) = (INR NONE,ghost) ==>
  e = NONE /\ ?ctxt rb. es.contexts = [(ctxt,rb)] /\
    shadow_root es = ghost /\ ctxt.msgParams.outputTo = root_output_to es
Proof
  strip_tac >>
  `~(1 < LENGTH es.contexts)` by
    (strip_tac >>
     `1 < LENGTH (shadow_root es).contexts` by
       simp[shadow_root_def, shadow_root_contexts_length] >>
     metis_tac[handle_step_nested_no_halt]) >>
  `e = NONE` by
    (Cases_on `e` >> simp[] >>
     `(shadow_root es).contexts <> []` by
       simp[shadow_root_def, shadow_root_contexts_nil] >>
     metis_tac[handle_step_some_no_halt]) >>
  gvs[] >> Cases_on `es.contexts` >> gvs[] >>
  Cases_on `t` >> gvs[] >> PairCases_on `h` >>
  drule shadow_root_handle_halt_singleton >>
  simp[root_output_to_def] >> metis_tac[]
QED

Theorem shadow_root_step_continue:
  !es ghost.
    es.contexts <> [] /\ step (shadow_root es) = (INL (), ghost) ==>
    ?es'. step es = (INL (), es') /\ es'.contexts <> [] /\
          shadow_root es' = ghost /\ root_output_to es' = root_output_to es
Proof
  rpt strip_tac >> drule shadow_root_step_body_raw >> strip_tac >>
  gvs[step_eq_handle_step_inner, handle_def] >> Cases_on `r` >> gvs[] >>
  drule_at (Pos last) shadow_root_handle_step_nonhalt >> simp[]
QED

Theorem shadow_root_step_exception:
  !es exc ghost.
    es.contexts <> [] /\
    step (shadow_root es) = (INR (SOME exc), ghost) ==>
    ?es'. step es = (INR (SOME exc), es') /\ es'.contexts <> [] /\
          shadow_root es' = ghost /\ root_output_to es' = root_output_to es
Proof
  rpt strip_tac >> drule shadow_root_step_body_raw >> strip_tac >>
  gvs[step_eq_handle_step_inner, handle_def] >> Cases_on `r` >> gvs[] >>
  drule_at (Pos last) shadow_root_handle_step_nonhalt >> simp[]
QED

Theorem shadow_root_step_halt:
  !es ghost.
    es.contexts <> [] /\ step (shadow_root es) = (INR NONE, ghost) ==>
    ?mid ctxt rb.
      mid.contexts = [(ctxt, rb)] /\ shadow_root mid = ghost /\
      ctxt.msgParams.outputTo = root_output_to es /\
      step es = handle_step NONE mid
Proof
  rpt strip_tac >> drule shadow_root_step_body_raw >> strip_tac >>
  gvs[step_eq_handle_step_inner, handle_def] >> Cases_on `r` >> gvs[] >>
  drule_all shadow_root_handle_step_halt >> strip_tac >> gvs[] >>
  qexists_tac `es'` >> simp[] >> metis_tac[]
QED

Theorem root_replay_run_induct[local]:
  (!s e s'. step s = (INR e,s') ==> P s (INR e,s')) /\
  (!s s' r. step s = (INL (),s') /\ P s' r ==> P s r) ==>
  !s r. run s = SOME r ==> P s r
Proof
  strip_tac >>
  `!rs final. OWHILE (ISL o FST) (step o SND) rs = SOME final ==>
    (case FST rs of INL _ => P (SND rs) final | INR _ => rs = final)` suffices_by
    (disch_tac >> rpt gen_tac >>
     first_x_assum (qspecl_then [`(INL (),s)`, `r`] mp_tac) >> simp[run_def]) >>
  ho_match_mp_tac WhileTheory.OWHILE_IND >> conj_tac
  >- (Cases >> Cases_on `q` >> simp[]) >>
  Cases >> Cases_on `q` >> simp[] >> rpt gen_tac >>
  Cases_on `step r` >> Cases_on `q` >> simp[] >> metis_tac[]
QED

Theorem handle_exception_singleton_no_return[local]:
  LENGTH s.contexts = 1 ==> handle_exception e s <> (INL x,t)
Proof
  strip_tac >> pure_rewrite_tac[handle_exception_def, LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `ignore_bind prep _ s` >>
  `!r sp. prep s = (r,sp) ==> LENGTH sp.contexts = LENGTH s.contexts` by
    (unabbrev_all_tac >> rpt strip_tac >>
     drule replay_exception_prepare_length >> simp[]) >>
  Cases_on `(prep s : unit execution_result)` >>
  `LENGTH r.contexts = 1` by metis_tac[] >>
  Cases_on `q` >>
  simp[ignore_bind_def, bind_def, get_num_contexts_def, return_def, reraise_def]
QED

Theorem handle_step_singleton_no_return[local]:
  LENGTH s.contexts = 1 ==> handle_step e s <> (INL x,t)
Proof
  strip_tac >> pure_rewrite_tac[handle_step_def] >>
  Cases_on `vfm_abort e` >- simp[reraise_def] >>
  Cases_on `(handle_create e s : unit execution_result)` >>
  `LENGTH r.contexts = 1` by metis_tac[handle_create_context_length] >>
  Cases_on `q` >- metis_tac[handle_create_no_return] >>
  gvs[handle_def] >> irule handle_exception_singleton_no_return >> simp[]
QED

Theorem root_replay_run_empty[local]:
  es.contexts = [] ==> run es = SOME (INR (SOME Impossible),es)
Proof
  strip_tac >> irule run_step_inr >>
  simp[step_def, handle_def, get_current_context_def, bind_def,
       fail_def, handle_step_def, vfm_abort_def, reraise_def]
QED

Theorem shadow_root_run_exception:
  !es exc ghost.
    run (shadow_root es) = SOME (INR (SOME exc), ghost) ==>
    ?es'. run es = SOME (INR (SOME exc), es') /\ shadow_root es' = ghost
Proof
  `!s result. run s = SOME result ==>
    !es exc ghost. es.contexts <> [] /\ s = shadow_root es /\
      result = (INR (SOME exc),ghost) ==>
      ?es'. run es = SOME (INR (SOME exc),es') /\ shadow_root es' = ghost` by
    (ho_match_mp_tac root_replay_run_induct >> conj_tac
     >- (rpt strip_tac >> gvs[] >> drule_all shadow_root_step_exception >>
         strip_tac >> drule run_step_inr >> metis_tac[]) >>
     rpt strip_tac >> gvs[] >> drule_all shadow_root_step_continue >>
     strip_tac >> drule run_step_inl >> metis_tac[]) >>
  rpt strip_tac >> Cases_on `es.contexts = []`
  >- (`shadow_root es = es` by
        simp[shadow_root_def, shadow_root_contexts_def,
             execution_state_component_equality] >>
      drule root_replay_run_empty >> gvs[] >> qexists_tac `es` >> simp[]) >>
  metis_tac[]
QED

Theorem root_replay_run_handler_terminal[local]:
  LENGTH mid.contexts = 1 /\ step es = handle_step NONE mid ==>
  run es = SOME (handle_step NONE mid)
Proof
  strip_tac >> Cases_on `(handle_step NONE mid : unit execution_result)` >>
  Cases_on `q` >- metis_tac[handle_step_singleton_no_return] >>
  gvs[] >> irule run_step_inr >> simp[]
QED

Theorem shadow_root_run_halt:
  !es ghost.
    es.contexts <> [] /\ run (shadow_root es) = SOME (INR NONE, ghost) ==>
    ?mid ctxt rb.
      mid.contexts = [(ctxt, rb)] /\ shadow_root mid = ghost /\
      ctxt.msgParams.outputTo = root_output_to es /\
      run es = SOME (handle_step NONE mid)
Proof
  `!s result. run s = SOME result ==>
    !es ghost. es.contexts <> [] /\ s = shadow_root es /\ result = (INR NONE,ghost) ==>
      ?mid ctxt rb. mid.contexts = [(ctxt,rb)] /\ shadow_root mid = ghost /\
        ctxt.msgParams.outputTo = root_output_to es /\
        run es = SOME (handle_step NONE mid)` by
    (ho_match_mp_tac root_replay_run_induct >> conj_tac
     >- (rpt strip_tac >> gvs[] >> drule_all shadow_root_step_halt >> strip_tac >>
         `LENGTH mid.contexts = 1` by simp[] >>
         drule_all root_replay_run_handler_terminal >> metis_tac[]) >>
     rpt strip_tac >> gvs[] >> drule_all shadow_root_step_continue >> strip_tac >>
     drule run_step_inl >> metis_tac[]) >>
  metis_tac[]
QED

Theorem shadow_root_contexts_map[local]:
  (!c rb. f (c with msgParams updated_by
    (\mp. mp with outputTo := Memory <| offset := 0; size := 0 |>),rb) = f (c,rb)) ==>
  !cs. MAP f (shadow_root_contexts cs) = MAP f cs
Proof
  strip_tac >> Induct >> simp[shadow_root_contexts_def] >>
  Cases_on `h` >> Cases_on `cs = []` >> gvs[shadow_root_contexts_def]
QED

Theorem shadow_root_contexts_every[local]:
  (!c rb. P (c,rb) ==> P (c with msgParams updated_by
    (\mp. mp with outputTo := Memory <| offset := 0; size := 0 |>),rb)) ==>
  !cs. EVERY P cs ==> EVERY P (shadow_root_contexts cs)
Proof
  strip_tac >> Induct >> simp[shadow_root_contexts_def] >>
  Cases_on `h` >> Cases_on `cs = []` >> gvs[shadow_root_contexts_def]
QED

Theorem shadow_root_all_accounts[local]:
  all_accounts (shadow_root es) = all_accounts es
Proof
  simp[all_accounts_def, shadow_root_def] >> AP_TERM_TAC >>
  irule shadow_root_contexts_map >> simp[]
QED

Theorem shadow_root_stack_room[local]:
  stack_room_ok (shadow_root es) = stack_room_ok es
Proof
  simp[stack_room_ok_def, shadow_root_def, EVERY_MAP] >>
  Cases_on `es.contexts` >> simp[shadow_root_contexts_def] >>
  PairCases_on `h` >> Cases_on `t = []` >>
  simp[shadow_root_contexts_def] >>
  `MAP (\cr. LENGTH (FST cr).stack < stack_limit) (shadow_root_contexts t) =
   MAP (\cr. LENGTH (FST cr).stack < stack_limit) t` by
    (irule shadow_root_contexts_map >> simp[]) >>
  pop_assum (mp_tac o AP_TERM ``EVERY I``) >>
  simp[EVERY_MAP, combinTheory.o_DEF]
QED

Theorem shadow_root_gas_stack[local]:
  gas_stack_ok (shadow_root es) = gas_stack_ok es
Proof
  `MAP (\cr. (FST cr).gasUsed) (shadow_root_contexts es.contexts) =
   MAP (\cr. (FST cr).gasUsed) es.contexts` by
    (irule shadow_root_contexts_map >> simp[]) >>
  `MAP (\cr. (FST cr).msgParams.gasLimit - (FST cr).gasUsed)
     (shadow_root_contexts es.contexts) =
   MAP (\cr. (FST cr).msgParams.gasLimit - (FST cr).gasUsed) es.contexts` by
    (irule shadow_root_contexts_map >> simp[]) >>
  simp[gas_stack_ok_def, shadow_root_def, shadow_root_contexts_length,
       unused_gas_def, MAP_MAP_o, combinTheory.o_DEF, MAP_TAKE] >>
  eq_tac >> rpt strip_tac >> first_x_assum drule >>
  `EL (SUC i) (MAP (\cr. (FST cr).gasUsed) (shadow_root_contexts es.contexts)) =
   EL (SUC i) (MAP (\cr. (FST cr).gasUsed) es.contexts)` by simp[] >>
  gvs[EL_MAP, shadow_root_contexts_length, MAP_TAKE]
QED

Theorem shadow_root_wf_state:
  !es. wf_state es ==> wf_state (shadow_root es)
Proof
  simp_tac bool_ss[wf_state_def, shadow_root_all_accounts,
    shadow_root_stack_room, shadow_root_gas_stack] >>
  gen_tac >> strip_tac >>
  gvs[outputTo_consistent_stack_def, shadow_root_def,
      shadow_root_contexts_nil, shadow_root_contexts_length, EVERY_MAP] >>
  conj_tac
  >- (irule shadow_root_contexts_every >> simp[wf_context_def]) >>
  irule shadow_root_contexts_every >> simp[outputTo_consistent_ctx_def]
QED

Theorem shadow_root_current_projection[local]:
  (!c. f (c with msgParams updated_by
    (\mp. mp with outputTo := Memory <| offset := 0; size := 0 |>)) = f c) ==>
  !cs. f (FST (HD (shadow_root_contexts cs))) = f (FST (HD cs))
Proof
  strip_tac >> Cases >> simp[shadow_root_contexts_def] >>
  PairCases_on `h` >> Cases_on `t = []` >> simp[shadow_root_contexts_def]
QED

Theorem shadow_root_head_observers[local]:
  next_opcode (FST (HD (shadow_root es).contexts)) = next_opcode (FST (HD es.contexts)) /\
  observable_call (FST (HD (shadow_root es).contexts)) = observable_call (FST (HD es.contexts)) /\
  (FST (HD (shadow_root es).contexts)).stack = (FST (HD es.contexts)).stack /\
  (FST (HD (shadow_root es).contexts)).logs = (FST (HD es.contexts)).logs
Proof
  simp[shadow_root_def] >> rpt conj_tac >>
  irule shadow_root_current_projection >> simp[next_opcode_def, observable_call_def]
QED

Theorem shadow_root_request_of[local]:
  request_of (shadow_root es) = request_of es
Proof
  Cases_on `es.contexts` >> simp[shadow_root_def, shadow_root_contexts_def, request_of_def] >>
  PairCases_on `h` >> Cases_on `t = []` >>
  simp[shadow_root_def, shadow_root_contexts_def, request_of_def, next_opcode_def]
QED

Theorem shadow_root_outcome_of[local]:
  outcome_of (shadow_root es) n m = outcome_of es n m
Proof
  Cases_on `es.contexts` >> simp[shadow_root_def, shadow_root_contexts_def, outcome_of_def] >>
  PairCases_on `h` >> Cases_on `t = []` >>
  simp[shadow_root_def, shadow_root_contexts_def, outcome_of_def]
QED

Theorem shadow_root_context_count[local]:
  LENGTH (shadow_root es).contexts = LENGTH es.contexts
Proof
  simp[shadow_root_def, shadow_root_contexts_length]
QED

Theorem shadow_root_observe[local]:
  observe d (shadow_root es) ((INL ():unit + exception option),shadow_root es') obs =
  observe d es ((INL ():unit + exception option),es') obs
Proof
  simp[observe_def, shadow_root_head_observers, shadow_root_request_of,
       shadow_root_outcome_of] >>
  simp[shadow_root_def, shadow_root_contexts_length]
QED

Theorem shadow_root_frame_obs_tr[local]:
  !d obs s r s'. !es. es.contexts <> [] /\ s = shadow_root es /\ (r,s') = step s ==>
    frame_obs_tr d obs s (r,s') = frame_obs_tr d obs es (step es)
Proof
  recInduct frame_obs_tr_ind >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `r`
  >- (Cases_on `x` >> gvs[] >>
      qpat_x_assum `(INL (),_) = step _` (assume_tac o SYM) >>
      drule_all shadow_root_step_continue >> strip_tac >>
      gvs[] >> once_rewrite_tac[frame_obs_tr_def] >>
      simp[shadow_root_observe, shadow_root_context_count] >>
      Cases_on `LENGTH es'.contexts < d` >> simp[] >>
      qpat_x_assum `_ ==> _` mp_tac >> simp[shadow_root_context_count] >>
      disch_then (qspec_then `es'` mp_tac) >> simp[shadow_root_observe]) >>
  Cases_on `y`
  >- (gvs[] >> qpat_x_assum `(INR NONE,_) = step _` (assume_tac o SYM) >>
      drule_all shadow_root_step_halt >> strip_tac >>
      Cases_on `(handle_step NONE mid : unit execution_result)` >>
      Cases_on `q`
      >- (`LENGTH mid.contexts = 1` by simp[] >>
          metis_tac[handle_step_singleton_no_return]) >>
      gvs[] >> once_rewrite_tac[frame_obs_tr_def] >> simp[observe_def]) >>
  gvs[] >> qpat_x_assum `(INR (SOME _),_) = step _` (assume_tac o SYM) >>
  drule_all shadow_root_step_exception >> strip_tac >>
  gvs[] >> once_rewrite_tac[frame_obs_tr_def] >> simp[observe_def]
QED

Theorem shadow_root_frame_obs:
  !es. es.contexts <> [] ==> frame_obs (shadow_root es) = frame_obs es
Proof
  rpt strip_tac >> simp[frame_obs_def, shadow_root_context_count] >>
  Cases_on `step (shadow_root es)` >>
  irule shadow_root_frame_obs_tr >> simp[]
QED
