Theory ctorDeployLoweringFramePayload
Ancestors
  e2eDeployDefs vyperTypeStoragePreservation e2eDefs list
  vyperStorageLayoutSafety vyperLookupStorage venomMemProps

Theorem deploy_oracle_storage_payload:
  oracle_storage_ok (deploy_evaluation_context tops am tx)
    (es0 with outcomes := SOME os) <=>
  EVERY (\co. contract_storage_well_formed
    (deploy_evaluation_context tops am tx)
    (empty_state with <|accounts := co.co_accounts;
                       tStorage := co.co_tStorage|>)) os
Proof
  simp[oracle_storage_ok_payload]
QED

(* Exact residual reads in the installed context. Neither validity in the
   old context nor validity of the initial backends asserts these reads. *)
Theorem deploy_oracle_storage_read_obligations:
  oracle_storage_ok (deploy_evaluation_context tops am tx)
    (es0 with outcomes := SOME os) <=>
  !co. MEM co os ==>
    (!mid n b off tv storage st'.
      storage_var_info (deploy_evaluation_context tops am tx) mid n =
        SOME (b,off,tv) /\
      get_storage_backend (deploy_evaluation_context tops am tx) b
        (empty_state with <|accounts := co.co_accounts;
                           tStorage := co.co_tStorage|>) = (INL storage,st') ==>
      slots_in_range storage off tv) /\
    (!mid n subs b slot tv storage st'.
      declared_storage_region (deploy_evaluation_context tops am tx)
        mid n subs = SOME (b,slot,tv) /\
      get_storage_backend (deploy_evaluation_context tops am tx) b
        (empty_state with <|accounts := co.co_accounts;
                           tStorage := co.co_tStorage|>) = (INL storage,st') ==>
      slots_in_range storage (w2n slot) tv)
Proof
  simp[deploy_oracle_storage_payload, EVERY_MEM,
       contract_storage_well_formed_def, well_formed_storage_def,
       storage_var_in_range_def]
QED
