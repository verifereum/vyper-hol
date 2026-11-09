(* PLAN 5.11 / D28: single-frame creation boundary, NOT a deployment proof.
 * TOP-LEVEL: constructor_args_encode, constructor_call_free, deploy_typing_ok,
 * deploy_storage_ok, deploy_state_rel, deploy_result_rel.
 * Helpers: constructor_call_root, deploy_evaluation_context.
 * DAG: e2eDefs + syntax traversal + source entry readiness -> e2eDeployDefs;
 * e2eDeployDefs -> clean e2eDeployChecks and e2eCorrectness's planned admission.
 * No dependency on e2eCorrectness or an admitted deployment theory.
 *)
Theory e2eDeployDefs
Ancestors
  e2eDefs supportedStmtTraverse vyperTypeEntryReadiness
  vyperTypeContractSoundness vyperTypeInitialState vyperStorageLayoutSafety
  vyperInterpreter vyperABI vfmExecution vfmExecutionProp frameOutcome
  list immutableSectionRel compileEnv callTrace

(* ===== Canonical constructor ABI and syntactic Call exclusion ===== *)

Definition constructor_args_encode_def:
  constructor_args_encode tops tx bs <=>
    ?mut args body abi_vals.
      vyperInterpreter$lookup_function NONE "__init__" Deploy tops =
        SOME (mut, F, args, [], NoneT, body) /\
      LENGTH tx.args = LENGTH args /\
      IS_SOME (bind_arguments (type_env tops) args tx.args) /\
      vyper_to_abi_list (type_env tops) (MAP SND args) tx.args = SOME abi_vals /\
      bs = enc (Tuple (vyper_to_abi_types (type_env tops) (MAP SND args)))
               (ListV abi_vals)
End

(* All Call constructors, not just external calls or effectful roots, and the
 * precompile builtins (sha256, ecrecover, ecadd, ecmul): the constructor
 * source runs without the call oracle, while the EVM can fail their
 * STATICCALL for lack of gas. The existing total traversal inspects nested
 * statements, assignment indices, assert/raise reasons and expression
 * children, even in unsupported syntax. Pop and the other builtins remain
 * admitted by this test.
 *)
Definition constructor_call_root_def:
  constructor_call_root e <=>
    case e of
      Call ty target args default => T
    | Builtin ty bt args => precompile_builtin bt
    | _ => F
End

Definition constructor_call_free_def:
  constructor_call_free tops <=>
    !mut nr args dflts ret body.
      vyperInterpreter$lookup_function NONE "__init__" Deploy tops =
        SOME (mut, nr, args, dflts, ret, body) ==>
      ~supported_stmts_expr_exists constructor_call_root body
End

(* ===== The actual load_contract deployment context ===== *)

Definition deploy_evaluation_context_def:
  deploy_evaluation_context tops am tx =
    initial_evaluation_context ((tx.target, [(NONE, tops)]) :: am.sources)
      am.layouts (tx with created_in_tx := T) NONE with in_deploy := T
End

(* The constructor runs with created_in_tx set; the value transfer reads none
   of it. *)
Theorem value_transfer_created_in_tx:
  (value_transfer_ok (tx with created_in_tx := c) accs <=>
   value_transfer_ok tx accs) /\
  accounts_after_transfer (tx with created_in_tx := c) accs =
  accounts_after_transfer tx accs
Proof
  simp[value_transfer_ok_def, accounts_after_transfer_def]
QED

(* Runtime readiness must NOT be required of the uninstalled source target.
 * Use the source's pre-constant deployment readiness on precisely the machine
 * load_contract builds. The two artifacts are the checked deployment/runtime
 * pair used by load_contract_establishes_machine_well_typed. This is an input
 * typing/setup boundary, not a hypothesis that deployment already succeeded.
 *)
Definition deploy_typing_ok_def:
  deploy_typing_ok tops am tx <=>
    ?deploy_art runtime_art imms.
      check_contract T am.layouts tx.target [(NONE, tops)] = SOME deploy_art /\
      check_contract F am.layouts tx.target [(NONE, tops)] = SOME runtime_art /\
      machine_well_typed am /\ call_tx_well_typed tx /\
      initial_immutables (type_env_all_modules [(NONE, tops)]) [(NONE, tops)] =
        SOME imms /\
      checked_deployment_constants_ready (deploy_evaluation_context tops am tx)
        (am with <| immutables updated_by CONS (tx.target, imms);
                    exports updated_by CONS (tx.target, []) |>)
        tx.target [(NONE, tops)]
End

Definition deploy_storage_ok_def:
  deploy_storage_ok tops am tx <=>
    contract_storage_well_formed (deploy_evaluation_context tops am tx)
      (initial_state am []) /\
    storage_layout_safe (deploy_evaluation_context tops am tx)
End

(* ===== Fresh single creation frame, live entry-transfer accounts ===== *)

Definition deploy_state_rel_def:
  deploy_state_rel tops deploy_bc am tx es <=>
    ?ctxt rb args_bytes.
      es.contexts = [(ctxt, rb)] /\
      wf_state es /\ (?d. es.msdomain = Collect d) /\
      ctxt.jumpDest = NONE /\ ~ctxt.msgParams.static /\
      ctxt.msgParams.outputTo = Code tx.target /\
      ctxt.msgParams.code = deploy_bc ++ args_bytes /\
      ctxt.msgParams.parsed = parse_code 0 FEMPTY (deploy_bc ++ args_bytes) /\
      buffer_to_list ctxt.msgParams.data = [] /\
      tx.calldata = [] /\
      constructor_args_encode tops tx args_bytes /\
      ctxt.pc = 0 /\ ctxt.stack = [] /\ ctxt.logs = [] /\
      ctxt.returnData = [] /\ buffer_to_list ctxt.memory = [] /\
      value_transfer_ok tx am.accounts /\
      es.rollback.accounts = accounts_after_transfer tx am.accounts /\
      es.rollback.tStorage = am.tStorage /\ am.logs = [] /\
      es.rollback.toDelete = am.pending_deletions /\
      am.pending_deletions = [] /\
      ctxt.msgParams.caller = tx.sender /\ ctxt.msgParams.callee = tx.target /\
      ctxt.msgParams.value = tx.value /\
      tx_block_fields_rel tx es.txParams /\
      tx.function_name = "__init__" /\ ~tx.is_static /\
      call_outcomes_ok am tx (MAP SND (call_trace es)) /\
      (* Under constructor_call_free the real call trace is empty, so this
       * clause is vacuous. It could be discharged by proving that a
       * call-free constructor compiles (through O1 and codegen) to code with
       * no CALL-family instruction, leaving call_trace es empty; it is kept
       * as a premise only to avoid that detour. *)
      EVERY (\co. contract_storage_well_formed (deploy_evaluation_context tops am tx)
                    (initial_state (am with <|accounts := co.co_accounts;
                                              tStorage := co.co_tStorage|>) []))
        (MAP SND (call_trace es)) /\
      ALOOKUP am.sources tx.target = NONE /\ layouts_agree tops am tx
End

(* ===== Creation result cases (no nested creation frame_outcome) ===== *)

(* This named case expression is for clean focused boundary clients. The stage
 * theorem keeps the literal PLAN 5.11 expression in its conclusion. Source
 * installation is not EVM bytecode installation: compare the target modulo
 * code, with its storage modulo storage_dead, all other accounts exactly,
 * transient storage modulo storage_dead, and ordered logs (as the runtime's
 * accounts_agree/transient_agree).
 *)
Definition deploy_result_rel_def:
  deploy_result_rel tops runtime_bc tx es r es' src <=>
    case src of
      INL (am', rqs) =>
        let cx = initial_evaluation_context am'.sources am'.layouts tx NONE in
        ?section lgs.
          immutables_section_rel tops (account_immutables am' tx.target) section /\
          frame_outcome es r es' NONE (runtime_bc ++ section) lgs /\
          (lookup_account tx.target es'.rollback.accounts).code = runtime_bc ++ section /\
          (!a. a <> tx.target ==>
               lookup_account a es'.rollback.accounts =
               lookup_account a am'.accounts) /\
          (lookup_account tx.target es'.rollback.accounts) with code := [] =
          (lookup_account tx.target am'.accounts) with
            <| code := [];
               storage := (lookup_account tx.target es'.rollback.accounts).storage |> /\
          storage_agree
            (storage_dead cx F (lookup_account tx.target am'.accounts).storage)
            (lookup_account tx.target am'.accounts).storage
            (lookup_account tx.target es'.rollback.accounts).storage /\
          transient_agree cx am'.tStorage es'.rollback.tStorage /\
          logs_correspond (compiled_event_info tops) (type_env tops)
            tx.target am'.logs lgs
    | INR (AssertException s) =>
        ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs /\
                      (exc = Reverted \/ s = "UNREACHABLE")
    | INR (Error e) =>
        unspecified_behaviour_exempt tops e \/
        ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs
    | INR BreakException => F
    | INR ContinueException => F
    | INR (ReturnException _) => F
End

(* Current-owner kernel gate: definitions are total saved objects, not stage
 * assumptions. This checks their tags, not those of unrelated ancestors.
 *)
val _ = List.app (fn (name, th) =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn tag => tag = "DISK_THM") oracles then ()
    else raise Fail ("non-clean deployment definition: " ^ name)
  end) (DB.thms "e2eDeployDefs");
