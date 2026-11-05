Theory dftEvmConstructedState
Ancestors
  dftEvmExtractionBoundary venomExecSemantics vfmExecutionProp vfmContext
  list arithmetic

Theorem dft_evm_call_state_wf:
  wf_accounts s.vs_accounts ==>
  wf_state (make_venom_call_state s target gas value calldata code is_static)
Proof
  strip_tac >>
  simp[make_venom_call_state_def, make_rollback_def, wf_state_def,
       wf_context_def, all_accounts_def, stack_room_ok_def, gas_stack_ok_def,
       outputTo_consistent_stack_def, outputTo_consistent_ctx_def,
       initial_context_def, initial_msg_params_def,
       empty_return_destination_def]
QED

Theorem dft_evm_delegatecall_state_wf:
  wf_accounts s.vs_accounts ==>
  wf_state (make_venom_delegatecall_state s target gas calldata code is_static)
Proof
  strip_tac >>
  simp[make_venom_delegatecall_state_def, make_rollback_def, wf_state_def,
       wf_context_def, all_accounts_def, stack_room_ok_def, gas_stack_ok_def,
       outputTo_consistent_stack_def, outputTo_consistent_ctx_def,
       initial_context_def, initial_msg_params_def,
       empty_return_destination_def]
QED

Theorem dft_evm_create_state_wf:
  wf_accounts s.vs_accounts ==>
  wf_state (make_venom_create_state s new_address gas value init_code)
Proof
  strip_tac >>
  simp[make_venom_create_state_def, make_rollback_def, wf_state_def,
       wf_context_def, all_accounts_def, stack_room_ok_def, gas_stack_ok_def,
       outputTo_consistent_stack_def, outputTo_consistent_ctx_def,
       initial_context_def, initial_msg_params_def]
QED

Theorem dft_evm_call_extraction_success:
  wf_accounts s.vs_accounts /\
  (!e es'. run (make_venom_call_state s target gas value calldata code is_static) =
           SOME (INR e, es') ==> ~vfm_abort e) ==>
  ?v t. extract_venom_result s out off sz
          (run (make_venom_call_state s target gas value calldata code is_static)) =
        SOME (v,t)
Proof
  strip_tac >> irule dft_evm_extraction_success >>
  simp[dft_evm_call_state_wf]
QED

Theorem dft_evm_delegatecall_extraction_success:
  wf_accounts s.vs_accounts /\
  (!e es'. run (make_venom_delegatecall_state s target gas calldata code is_static) =
           SOME (INR e, es') ==> ~vfm_abort e) ==>
  ?v t. extract_venom_result s out off sz
          (run (make_venom_delegatecall_state s target gas calldata code is_static)) =
        SOME (v,t)
Proof
  strip_tac >> irule dft_evm_extraction_success >>
  simp[dft_evm_delegatecall_state_wf]
QED

Theorem dft_evm_create_extraction_success:
  wf_accounts s.vs_accounts /\
  (!e es'. run (make_venom_create_state s new_address gas value init_code) =
           SOME (INR e, es') ==> ~vfm_abort e) ==>
  ?v t. extract_venom_result s out off sz
          (run (make_venom_create_state s new_address gas value init_code)) =
        SOME (v,t)
Proof
  strip_tac >> irule dft_evm_extraction_success >>
  simp[dft_evm_create_state_wf]
QED
