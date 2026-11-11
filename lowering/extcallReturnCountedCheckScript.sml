(* The counted observer may change only returndata and the predecessor label.
   Neither field belongs to the successful decoder's resource/frame payload. *)
Theory extcallReturnCountedCheck
Ancestors
  abiValidAllocatedContract exprSimAbiGasBridge exprLoweringProps compileEnv loweringStateRelDefs
  venomState venomMemDefs abiMalformedRecursiveInterface abiMalformedSiteFrame

Theorem extcall_return_observer_state_rel:
  stmt_state_rel ctx func cenv cx es
    (t with <| vs_returndata := rd; vs_prev_bb := prev |>) <=>
  stmt_state_rel ctx func cenv cx es t
Proof
  `!op. eval_operand op (t with <|vs_returndata := rd; vs_prev_bb := prev|>) =
        eval_operand op t` by (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  simp[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def,
    local_backed_def, local_region_def, lookup_var_def,
    storage_rel_def, transient_rel_def, accounts_rel_def,
    contract_storage_def, contract_transient_def,
    immutables_rel_def, logs_rel_def, alloca_inv_def,
    allocas_non_overlapping_def, alloca_next_valid_def,
    alloca_room_def, fmp_room_def, pending_alloca_size_def,
    immutable_alloca_sep_def, immutable_base_zero_def, eval_operand_def]
QED

Theorem extcall_return_observer_resources:
  abi_malformed_resource_post ctx func cenv cx es next sites dstid s
    (t with <| vs_returndata := rd; vs_prev_bb := prev |>) <=>
  abi_malformed_resource_post ctx func cenv cx es next sites dstid s t
Proof
  `!op. eval_operand op (t with <|vs_returndata := rd; vs_prev_bb := prev|>) =
        eval_operand op t` by (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  simp[abi_malformed_resource_post_def, extcall_return_observer_state_rel,
    eval_operand_def, lookup_var_def]
QED

Theorem extcall_return_observer_frame:
  abi_valid_allocated_frame sites d n s
    (t with <| vs_returndata := rd; vs_prev_bb := prev |>) <=>
  abi_valid_allocated_frame sites d n s t
Proof
  simp[abi_valid_allocated_frame_def, abi_malformed_site_range_def]
QED
