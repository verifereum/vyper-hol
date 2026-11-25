(* Creation boundary and gas exemptions for linked units. *)
Theory e2eDeployModsDefs
Ancestors
  e2eModsDefs e2eDefs e2eDeployDefs e2eGasSufficient[qualified]
  ctorDeployDefs[qualified] compileUnit sourceExemptMods
  vyperInterpreter vyperTypeContract vyperTypeInvariants vyperContext vyperABI
  vyperStorageFootprint callTrace frameOutcome vfmExecution vfmState
  alist finite_map list

(* The main module owns the creation entry. Its argument types may refer
   to declarations in other modules. *)
Definition constructor_args_encode_mods_def:
  constructor_args_encode_mods mods tx bs <=>
    let tenv = type_env_all_modules mods in
    ?mut args body abi_vals.
      vyperInterpreter$lookup_function NONE "__init__" Deploy (main_module mods) =
        SOME (mut, F, args, [], NoneT, body) /\
      LENGTH tx.args = LENGTH args /\
      IS_SOME (bind_arguments tenv args tx.args) /\
      vyper_to_abi_list tenv (MAP SND args) tx.args = SOME abi_vals /\
      bs = enc (Tuple (vyper_to_abi_types tenv (MAP SND args)))
               (ListV abi_vals)
End

Theorem constructor_args_encode_mods_singleton:
  constructor_args_encode_mods [(NONE, tops)] tx bs <=>
  constructor_args_encode tops tx bs
Proof
  simp[constructor_args_encode_mods_def, constructor_args_encode_def,
       main_module_def, type_env_all_modules_def, type_env_def, FUNION_FEMPTY_2]
QED

Definition deploy_evaluation_context_mods_def:
  deploy_evaluation_context_mods mods am tx =
    initial_evaluation_context ((tx.target, mods) :: am.sources)
      am.layouts (tx with created_in_tx := T) NONE with in_deploy := T
End

Theorem deploy_evaluation_context_mods_singleton:
  deploy_evaluation_context_mods [(NONE, tops)] am tx =
  deploy_evaluation_context tops am tx
Proof
  simp[deploy_evaluation_context_mods_def, deploy_evaluation_context_def]
QED

(* The deploy checker covers the full unit.
   Deployment runs before the target has installed source or constant cells. *)
Definition deploy_typing_ok_mods_def:
  deploy_typing_ok_mods mods exps am tx <=>
    ?deploy_art.
      check_contract T am.layouts tx.target mods = SOME deploy_art /\
      exports_ok am.layouts tx.target mods exps /\
      machine_well_typed am /\ call_tx_well_typed tx
End

Theorem deploy_typing_ok_mods_singleton:
  deploy_typing_ok_mods [(NONE, tops)] [] am tx <=>
  deploy_typing_ok tops am tx
Proof
  simp[deploy_typing_ok_mods_def, deploy_typing_ok_def] >>
  metis_tac[check_contract_single_module_exports_ok]
QED

Definition deploy_storage_trace_mods_def:
  deploy_storage_trace_mods orc gobs am tx mods exps =
    SND (load_contract_trace orc gobs am tx mods exps)
End

Theorem deploy_storage_trace_mods_singleton:
  deploy_storage_trace_mods orc gobs am tx [(NONE, tops)] [] =
  deploy_storage_trace orc gobs am tx tops
Proof
  simp[deploy_storage_trace_mods_def, deploy_storage_trace_def]
QED

Definition deploy_storage_ok_mods_def:
  deploy_storage_ok_mods mods exps am tx os gs <=>
    let cx = deploy_evaluation_context_mods mods am tx in
    let obs = deploy_storage_trace_mods (SOME os) gs am tx mods exps in
    let (regions, locks) = storage_trace_horizon obs in
      storage_roots_fit obs /\ regions_consistent regions /\
      storage_locks_separated regions locks /\
      storage_well_formed_on cx (initial_state am []) regions /\
      storage_trace_backends_well_formed cx regions obs
End

Theorem deploy_storage_ok_mods_singleton:
  deploy_storage_ok_mods [(NONE, tops)] [] am tx os gs <=>
  deploy_storage_ok tops am tx os gs
Proof
  simp[deploy_storage_ok_mods_def, deploy_storage_ok_def,
       deploy_evaluation_context_mods_singleton, deploy_storage_trace_mods_singleton]
QED

Definition deploy_state_rel_mods_def:
  deploy_state_rel_mods mods exps deploy_bc am tx es <=>
    ?ctxt rb args_bytes.
      es.contexts = [(ctxt, rb)] /\
      wf_state es /\ balance_bounded (2 ** 256 - 1) es /\
      (?d. es.msdomain = Collect d) /\
      account_empty (lookup_account tx.target es.originalAccounts) /\
      ctxt.jumpDest = NONE /\ ~ctxt.msgParams.static /\
      ctxt.msgParams.outputTo = Code tx.target /\
      ctxt.msgParams.code = deploy_bc ++ args_bytes /\
      tx.code = ctxt.msgParams.code /\
      ctxt.msgParams.parsed = parse_code 0 FEMPTY (deploy_bc ++ args_bytes) /\
      buffer_to_list ctxt.msgParams.data = [] /\
      tx.calldata = [] /\
      constructor_args_encode_mods mods tx args_bytes /\
      ctxt.pc = 0 /\ ctxt.stack = [] /\ ctxt.logs = [] /\
      ctxt.returnData = [] /\ buffer_to_list ctxt.memory = [] /\
      value_transfer_ok tx am.accounts /\
      es.rollback.accounts = accounts_after_transfer tx am.accounts /\
      es.rollback.tStorage = am.tStorage /\ am.logs = [] /\
      es.rollback.toDelete = am.pending_deletions /\
      ctxt.msgParams.caller = tx.sender /\ ctxt.msgParams.callee = tx.target /\
      ctxt.msgParams.value = tx.value /\
      tx_block_fields_rel tx es.txParams /\
      tx.function_name = "__init__" /\ ~tx.is_static /\ tx.created_in_tx /\
      ALOOKUP am.sources tx.target = NONE /\ ALOOKUP mods NONE <> NONE /\
      layouts_agree_mods mods exps am tx
End

Theorem deploy_state_rel_mods_singleton:
  deploy_state_rel_mods [(NONE, tops)] [] deploy_bc am tx es <=>
  deploy_state_rel tops deploy_bc am tx es
Proof
  simp[deploy_state_rel_mods_def, deploy_state_rel_def,
       constructor_args_encode_mods_singleton, layouts_agree_mods_singleton]
QED

Definition deploy_result_rel_mods_def:
  deploy_result_rel_mods H mods runtime_bc tx es r es' src <=>
    case src of
      INL (am', rqs) =>
        if ALOOKUP am'.sources tx.target = NONE then
          (* the constructor self-destructed: no source installed, no code
             deposited *)
          frame_outcome es r es' NONE [] am'.logs /\
          (lookup_account tx.target es'.rollback.accounts).code = [] /\
          MEM tx.target es'.rollback.toDelete /\
          accounts_agree H tx.target am'.accounts
            (process_deletions es'.rollback.toDelete es'.rollback.accounts) /\
          transient_agree H tx.target am'.tStorage es'.rollback.tStorage /\
          LIST_REL (request_agree H tx.target) rqs (call_requests es)
        else
          ?section.
            immutables_section_rel_mods mods (account_immutables am' tx.target)
              section /\
            frame_outcome es r es' NONE (runtime_bc ++ section) am'.logs /\
            (lookup_account tx.target es'.rollback.accounts).code =
              runtime_bc ++ section /\
            accounts_agree H tx.target am'.accounts
              (process_deletions es'.rollback.toDelete
                 (update_account tx.target
                    (lookup_account tx.target es'.rollback.accounts with
                       code := (lookup_account tx.target am'.accounts).code)
                    es'.rollback.accounts)) /\
            transient_agree H tx.target am'.tStorage es'.rollback.tStorage /\
            LIST_REL (request_agree H tx.target) rqs (call_requests es)
    | INR (AssertException s) =>
        ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs /\
                      (exc = Reverted \/ s = "UNREACHABLE")
    | INR (Error e) =>
        unspecified_behaviour_exempt_mods mods e \/
        ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs /\
                      (!d. e = RevertData d ==> exc = Reverted)
    | INR _ => F
End

Theorem deploy_result_rel_mods_singleton:
  deploy_result_rel_mods H [(NONE, tops)] runtime_bc tx es r es' src <=>
  deploy_result_rel H tops runtime_bc tx es r es' src
Proof
  simp[deploy_result_rel_mods_def, deploy_result_rel_def,
       immutables_section_rel_mods_singleton, unspecified_behaviour_exempt_mods_singleton] >>
  BasicProvers.EVERY_CASE_TAC >> simp[]
QED

Definition deploy_call_result_rel_mods_def:
  deploy_call_result_rel_mods mods exps runtime_bc am tx es r es' <=>
    let os = MAP SND (call_trace es) in
    gas_readings_rel (gas_readings es)
      (\gs. deploy_storage_ok_mods mods exps am tx os gs ==>
            deploy_result_rel_mods
              (storage_trace_horizon (deploy_storage_trace_mods (SOME os) gs am tx mods exps))
              mods runtime_bc tx es r es'
              (load_contract (SOME os) gs am tx mods exps))
End

Theorem deploy_call_result_rel_mods_singleton:
  deploy_call_result_rel_mods [(NONE, tops)] [] runtime_bc am tx es r es' <=>
  deploy_call_result_rel tops runtime_bc am tx es r es'
Proof
  simp[deploy_call_result_rel_mods_def, deploy_call_result_rel_def,
       deploy_storage_ok_mods_singleton, deploy_result_rel_mods_singleton,
       deploy_storage_trace_mods_singleton]
QED

Definition deploy_source_exempt_mods_def:
  deploy_source_exempt_mods mods
    (src : (abstract_machine # call_request list) + exception) <=>
    case src of
      INR (Error e) => unspecified_behaviour_exempt_mods mods e
    | _ => F
End

Theorem deploy_source_exempt_mods_singleton:
  deploy_source_exempt_mods [(NONE, tops)] src <=>
  ctorDeployDefs$deploy_source_exempt tops src
Proof
  simp[deploy_source_exempt_mods_def, ctorDeployDefsTheory.deploy_source_exempt_def,
       unspecified_behaviour_exempt_mods_singleton] >>
  BasicProvers.EVERY_CASE_TAC >> simp[]
QED

Definition deploy_gas_source_exempt_mods_def:
  deploy_gas_source_exempt_mods mods
    (src : (abstract_machine # call_request list) + exception) <=>
    deploy_source_exempt_mods mods src \/
    src = INR (Error (RuntimeError "create initcode too large"))
End

Theorem deploy_gas_source_exempt_mods_singleton:
  deploy_gas_source_exempt_mods [(NONE, tops)] src <=>
  e2eGasSufficient$deploy_gas_source_exempt tops src
Proof
  simp[deploy_gas_source_exempt_mods_def, e2eGasSufficientTheory.deploy_gas_source_exempt_def,
       deploy_source_exempt_mods_singleton]
QED
