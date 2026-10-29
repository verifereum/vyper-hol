(*
 * Typed storage invariants and preservation for primitive operations.
 *
 * The transparent contract-storage invariant covers ordinary declarations and
 * resolved hashmap regions on both persistent and transient backends.  Layout
 * safety supplies nonoverflow and separation for those regions and reserves the
 * nonreentrant transient lock slot.  Result-form preservation is intentional:
 * sequential tuple assignment, append, and pop may retain an earlier successful
 * write when a later operation returns an error.
 *
 * Whole-value writes reuse update_toplevel_name preservation. Resolved storage
 * places use typed region writes, including nested paths,
 * dynamic-array length updates, append, and pop.  The combined
 * runtime_storage_consistent predicate adds storage decodability and layout
 * safety without changing runtime_consistent or state_well_typed.
 *
 * Constructor introduction requires explicit zero-read premises because
 * load_contract does not allocate fresh storage.  External-call preservation is
 * separately parameterized by protected_storage_calls_preserve, which constrains
 * every returned persistent/transient state for the protected caller.
 *)

Theory vyperTypeStoragePreservation
Ancestors
  vyperTypeStatePreservation vyperHashMapPreservation vyperStorageFrame
  vyperStorageLayoutSafety vyperStorageReadSoundness vyperState
  vyperStorageBackend vyperCreate vyperInterpreter
Libs
  wordsLib markerLib

(* Additive combined invariant: the established runtime invariant is unchanged,
   and storage decodability/layout safety are carried as explicit conjuncts. *)
Definition runtime_storage_consistent_def:
  runtime_storage_consistent env cx st <=>
    runtime_consistent env cx st /\
    contract_storage_well_formed cx st /\
    storage_layout_safe cx
End

Theorem runtime_storage_consistent_runtime:
  runtime_storage_consistent env cx st ==> runtime_consistent env cx st
Proof
  simp[runtime_storage_consistent_def]
QED

Theorem runtime_storage_consistent_storage:
  runtime_storage_consistent env cx st ==>
  contract_storage_well_formed cx st
Proof
  simp[runtime_storage_consistent_def]
QED

Theorem runtime_storage_consistent_layout:
  runtime_storage_consistent env cx st ==> storage_layout_safe cx
Proof
  simp[runtime_storage_consistent_def]
QED

Theorem runtime_storage_consistent_intro:
  runtime_consistent env cx st /\
  contract_storage_well_formed cx st /\
  storage_layout_safe cx ==>
  runtime_storage_consistent env cx st
Proof
  simp[runtime_storage_consistent_def]
QED

(* ===== Oracle storage boundary (PLAN T6.2 / D26) ===== *)
Definition oracle_storage_ok_def:
  oracle_storage_ok cx st <=>
    !os. st.outcomes = SOME os ==>
      EVERY (\co. co.co_success ==>
        contract_storage_well_formed cx
          (st with <|accounts := co.co_accounts; tStorage := co.co_tStorage|>)) os
End

(* Payload storage depends on cx and the supplied two backends, not on the
   remaining fields of the evaluation state. No runtime account guard is used. *)
Theorem contract_storage_payload_frame:
  contract_storage_well_formed cx
    (st with <|accounts := accounts; tStorage := transient|>) <=>
  contract_storage_well_formed cx
    (other with <|accounts := accounts; tStorage := transient|>)
Proof
  EQ_TAC >> strip_tac >> irule contract_storage_well_formed_storage_frame >>
  goal_assum (drule_at Any) >> Cases >> simp[get_storage_def]
QED

Theorem oracle_storage_ok_outcomes:
  st'.outcomes = st.outcomes ==>
  (oracle_storage_ok cx st' <=> oracle_storage_ok cx st)
Proof
  simp[oracle_storage_ok_def] >> strip_tac >>
  simp[contract_storage_payload_frame |> Q.INST [`other` |-> `empty_state`]]
QED

(* A single generic residual-frame normal form; scopes/logs/requests and all
   other state fields are irrelevant after the two payload backends are set. *)
Theorem oracle_storage_ok_payload:
  oracle_storage_ok cx st <=>
    !os. st.outcomes = SOME os ==>
      EVERY (\co. co.co_success ==>
        contract_storage_well_formed cx
          (empty_state with <|accounts := co.co_accounts;
                              tStorage := co.co_tStorage|>)) os
Proof
  simp[oracle_storage_ok_def,
    contract_storage_payload_frame |> Q.INST [`other` |-> `empty_state`]]
QED

(* Generic storage projection transport, independent of residual fields. *)
Theorem contract_storage_well_formed_backends_frame:
  contract_storage_well_formed cx st /\
  st'.accounts = st.accounts /\ st'.tStorage = st.tStorage ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >> irule contract_storage_well_formed_storage_frame >>
  goal_assum (drule_at Any) >> Cases >> simp[get_storage_def]
QED

(* A typed zero-width encoding cannot change either storage backend. *)
Theorem zero_slot_write_storage_frame:
  value_has_type tv v /\
  type_slot_size tv = 0 /\
  write_storage_slot cx b slot tv v st = (res,st') ==>
  !b'. get_storage cx st' b' = get_storage cx st b'
Proof
  rpt strip_tac >>
  drule (CONJUNCT1 vyperTypingTheory.value_has_type_equiv) >> strip_tac >>
  Cases_on `encode_value tv v` >> gvs[] >>
  `x = []` by
    (Cases_on `x` >> simp[] >>
     qpat_x_assum `encode_value _ _ = SOME _` mp_tac >>
     simp[] >> strip_tac >>
     drule (CONJUNCT1 vyperEncodeDecodeTheory.encode_writes_bounded) >>
     simp[] >> metis_tac[]) >>
  gvs[vyperStorageBackendTheory.write_storage_slot_eq,
      vyperStorageTheory.apply_writes_def] >>
  Cases_on `b = b'` >> gvs[]
  >- simp[vyperStorageBackendTheory.get_storage_after_set] >>
  simp[vyperStorageBackendTheory.get_storage_after_set_other]
QED



Theorem zero_read_slots_in_range_mutual[local]:
  (!storage off tv.
     (!n. read_slot storage n = 0w) ==>
     slots_in_range storage off tv) /\
  (!storage off tvs.
     (!n. read_slot storage n = 0w) ==>
     tuple_slots_in_range storage off tvs) /\
  (!storage off tv n.
     (!m. read_slot storage m = 0w) ==>
     static_slots_in_range storage off tv n) /\
  (!storage off tv n.
     (!m. read_slot storage m = 0w) ==>
     dyn_slots_in_range storage off tv n) /\
  (!storage off fields.
     (!n. read_slot storage n = 0w) ==>
     struct_slots_in_range storage off fields)
Proof
  ho_match_mp_tac vyperLookupStorageTheory.slots_in_range_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  PURE_ONCE_REWRITE_TAC[vyperLookupStorageTheory.slots_in_range_def] >>
  gvs[] >>
  metis_tac[]
QED

Theorem zero_read_storage_contract_storage_well_formed:
  (!b n. read_slot (get_storage cx st b) n = 0w) ==>
  contract_storage_well_formed cx st
Proof
  simp[contract_storage_well_formed_def,
       vyperLookupStorageTheory.well_formed_storage_def,
       vyperLookupStorageTheory.storage_var_in_range_def,
       vyperStorageBackendTheory.get_storage_backend_eq] >>
  metis_tac[zero_read_slots_in_range_mutual]
QED

Theorem constructor_entry_contract_storage_well_formed:
  (!n. read_slot (am.tStorage cx.txn.target) n = 0w) /\
  (!n. read_slot ((am.accounts cx.txn.target).storage) n = 0w) ==>
  contract_storage_well_formed cx
    (initial_state am [scope] with <|outcomes := orc; requests := rqs|>)
Proof
  strip_tac >> irule zero_read_storage_contract_storage_well_formed >>
  Cases >>
  gvs[vyperStorageBackendTheory.get_storage_def,
      vyperInterpreterTheory.initial_state_def]
QED

Theorem constructor_entry_runtime_storage_consistent:
  (!n. read_slot (am.tStorage cx.txn.target) n = 0w) /\
  (!n. read_slot ((am.accounts cx.txn.target).storage) n = 0w) /\
  storage_layout_safe cx /\
  runtime_consistent env cx
    (initial_state am [scope] with <|outcomes := orc; requests := rqs|>) ==>
  runtime_storage_consistent env cx
    (initial_state am [scope] with <|outcomes := orc; requests := rqs|>)
Proof
  simp[runtime_storage_consistent_def] >>
  metis_tac[constructor_entry_contract_storage_well_formed]
QED

Definition protected_storage_calls_preserve_def:
  protected_storage_calls_preserve cx <=>
    (!callee calldata value_opt gas st txp success returndata accounts' tStorage' emitted_logs.
       run_ext_call cx.txn.target callee calldata value_opt gas
         st.accounts st.tStorage txp =
         SOME (success,returndata,accounts',tStorage',emitted_logs) /\
       contract_storage_well_formed cx st ==>
       contract_storage_well_formed cx
         (st with <| accounts := accounts'; tStorage := tStorage' |>)) /\
    (!callee calldata st success returndata accounts' tStorage' emitted_logs.
       run_delegate_call cx callee calldata st.accounts st.tStorage =
         SOME (success,returndata,accounts',tStorage',emitted_logs) /\
       contract_storage_well_formed cx st ==>
       contract_storage_well_formed cx
         (st with <| accounts := accounts'; tStorage := tStorage' |>))
End

Theorem protected_storage_calls_preserve_run_ext_call:
  protected_storage_calls_preserve cx /\
  run_ext_call cx.txn.target callee calldata value_opt gas
    st.accounts st.tStorage txp =
    SOME (success,returndata,accounts',tStorage',emitted_logs) /\
  contract_storage_well_formed cx st ==>
  contract_storage_well_formed cx
    (st with <| accounts := accounts'; tStorage := tStorage' |>)
Proof
  simp[protected_storage_calls_preserve_def] >> metis_tac[]
QED

Theorem protected_storage_calls_preserve_run_delegate_call:
  protected_storage_calls_preserve cx /\
  run_delegate_call cx callee calldata st.accounts st.tStorage =
    SOME (success,returndata,accounts',tStorage',emitted_logs) /\
  contract_storage_well_formed cx st ==>
  contract_storage_well_formed cx
    (st with <| accounts := accounts'; tStorage := tStorage' |>)
Proof
  simp[protected_storage_calls_preserve_def] >> metis_tac[]
QED

Theorem protected_storage_calls_preserve_run_raw_call:
  protected_storage_calls_preserve cx /\
  run_raw_call cx flags callee calldata amount st.accounts st.tStorage =
    SOME (success,returndata,accounts',tStorage',emitted_logs) /\
  contract_storage_well_formed cx st ==>
  contract_storage_well_formed cx
    (st with <| accounts := accounts'; tStorage := tStorage' |>)
Proof
  rw[run_raw_call_def] >>
  metis_tac[protected_storage_calls_preserve_run_delegate_call,
            protected_storage_calls_preserve_run_ext_call]
QED

(* ===== CREATE postulate =====
   Storage is NOT preserved through creation in general: the created
   constructor runs arbitrary EVM code that may write any account's storage,
   including the protected transaction target's own.  As with external calls
   above, the frame condition on the adapter boundary is therefore a
   postulate, parameterized by the context, discharged analogously.

   The adapter includes the creation prelude internally (endowment transfer
   and nonce bumps) and rolls back to the sender nonce bump on failure.  The
   protected frame covers the complete adapter step. *)
Definition protected_storage_creates_preserve_def:
  protected_storage_creates_preserve cx <=>
    (!sender address initcode value st txp code_opt
       accounts' tStorage' emitted_logs revertData pending'.
      run_create_evm sender address initcode value st.accounts st.tStorage
        st.pending_deletions txp =
        SOME (code_opt,accounts',tStorage',emitted_logs,revertData,pending') /\
      contract_storage_well_formed cx st ==>
      contract_storage_well_formed cx
        (st with <| accounts := accounts'; tStorage := tStorage' |>)) /\
    (* A failed adapter run retains only the sender nonce bump. *)
    (!sender address initcode value st txp.
      run_create_evm sender address initcode value st.accounts st.tStorage
        st.pending_deletions txp = NONE /\
      contract_storage_well_formed cx st ==>
      contract_storage_well_formed cx
        (st with accounts := create_rollback_accounts sender st.accounts))
End

Theorem protected_storage_creates_preserve_run_create_evm:
  protected_storage_creates_preserve cx /\
  run_create_evm sender address initcode value st.accounts st.tStorage
    st.pending_deletions txp =
    SOME (code_opt,accounts',tStorage',emitted_logs,revertData,pending') /\
  contract_storage_well_formed cx st ==>
  contract_storage_well_formed cx
    (st with <| accounts := accounts'; tStorage := tStorage' |>)
Proof
  simp[protected_storage_creates_preserve_def] >> metis_tac[]
QED

Theorem protected_storage_creates_preserve_run_create_evm_NONE:
  protected_storage_creates_preserve cx /\
  run_create_evm sender address initcode value st.accounts st.tStorage
    st.pending_deletions txp = NONE /\
  contract_storage_well_formed cx st ==>
  contract_storage_well_formed cx
    (st with accounts := create_rollback_accounts sender st.accounts)
Proof
  simp[protected_storage_creates_preserve_def] >> metis_tac[]
QED
