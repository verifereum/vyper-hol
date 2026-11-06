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

(* A sufficient backend-frame hypothesis, not a consequence of
   call_outcomes_ok: the latter checks a different source context. *)
Theorem deploy_oracle_storage_backend_frame:
  deploy_storage_ok tops am tx /\
  (!co. MEM co os ==> !b.
    get_storage (deploy_evaluation_context tops am tx)
      (empty_state with <|accounts := co.co_accounts;
                         tStorage := co.co_tStorage|>) b =
    get_storage (deploy_evaluation_context tops am tx)
      (initial_state am []) b) ==>
  oracle_storage_ok (deploy_evaluation_context tops am tx)
    (es0 with outcomes := SOME os)
Proof
  strip_tac >> simp[deploy_oracle_storage_payload, EVERY_MEM] >>
  rpt strip_tac >> irule contract_storage_well_formed_storage_frame >>
  qexists `initial_state am []` >>
  gvs[deploy_storage_ok_def]
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

(* This separates a candidate supplier only, not the compiled actual trace. *)
Theorem deploy_oracle_storage_context_separation:
  ?tops am tx co es0.
    deploy_storage_ok tops am tx /\
    call_outcomes_ok am tx [co] /\
    ~oracle_storage_ok (deploy_evaluation_context tops am tx)
       (es0 with outcomes := SOME [co])
Proof
  qexistsl [
    `[VariableDecl Private Storage "s" (BaseT (StringT 1)) (SOME 0)]`,
    `initial_machine_state with layouts := [(0w, ([( (NONE,"s"),0)],[]))]`,
    `empty_call_txn with target := 0w`,
    `<|co_created := 0w; co_success := T; co_returnData := [];
       co_accounts := update_account 0w
         (empty_account_state with storage := update_storage 0w 2w empty_storage)
         empty_accounts;
       co_tStorage := empty_transient_storage; co_logs := []; co_toDelete := []|>`,
    `empty_state`] >>
  simp[deploy_storage_ok_def, call_outcomes_ok_def,
       deploy_oracle_storage_read_obligations,
       deploy_evaluation_context_def, vyperInterpreterTheory.initial_evaluation_context_def,
       vyperInterpreterTheory.initial_machine_state_def,
       vyperContextTheory.empty_call_txn_def,
       vyperInterpreterTheory.lookup_nonreentrant_slot_def] >>
  conj_tac >- (
    simp[contract_storage_well_formed_def, well_formed_storage_def,
         storage_var_in_range_def, storage_layout_safe_def, well_formed_layout_def,
         nonreentrant_slot_separated_def, storage_var_info_def,
         declared_storage_region_def, vyperContextTheory.get_module_code_def,
         vyperContextTheory.get_tenv_def, vyperStateTheory.find_var_decl_by_name_def,
         vyperStateTheory.lookup_var_slot_from_layout_def,
         vyperContextTheory.type_env_all_modules_def,
         vyperContextTheory.type_env_for_module_def,
         vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
    simp[vyperStateTheory.get_storage_backend_def,
         vyperStateTheory.get_accounts_def, vyperStateTheory.bind_def,
         vyperStateTheory.return_def, vyperInterpreterTheory.initial_state_def,
         slots_in_range_def, vyperStorageTheory.read_slot_def] >> EVAL_TAC >>
    simp[]) >>
  conj_tac >- (
    simp[contract_storage_well_formed_def, well_formed_storage_def,
         storage_var_in_range_def, storage_var_info_def,
         declared_storage_region_def, vyperContextTheory.get_module_code_def,
         vyperRuntimeAccountsTheory.accounts_runtime_well_typed_def,
         vyperRuntimeAccountsTheory.account_runtime_well_typed_def] >>
    gen_tac >> EVAL_TAC >> simp[] >>
    IF_CASES_TAC >> simp[]) >>
  disj1_tac >> qexistsl [`NONE`, `"s"`, `F`, `0`, `BaseTV (StringT 1)`] >>
  simp[storage_var_info_def, vyperContextTheory.get_module_code_def,
       vyperContextTheory.get_tenv_def, vyperStateTheory.find_var_decl_by_name_def,
       vyperStateTheory.lookup_var_slot_from_layout_def,
       vyperContextTheory.type_env_all_modules_def,
       vyperContextTheory.type_env_for_module_def,
       vyperValueTheory.evaluate_type_def,
       vyperStateTheory.get_storage_backend_def, vyperStateTheory.get_accounts_def,
       vyperStateTheory.bind_def, vyperStateTheory.return_def,
       slots_in_range_def, vyperStorageTheory.read_slot_def] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256]
QED
