(* TASK055 focused creation/boundary clients. All exports are admission-free;
 * no import of e2eCorrectness or use of its deployment admission. These are
 * definition/interface checks, NOT a simulation or a deployment proof.
 *)
Theory e2eDeployChecks
Ancestors
  e2eDeployDefs e2eDefs supportedStmtTraverse supportedExprTraverse
  vyperInterpreter vyperABI vyperCreate vyperState vyperTypeEntryReadiness
  vyperTypeContractSoundness vyperTypeInitialState vyperTypeInvariants
  vyperStorageLayoutSafety
  vfmExecution frameOutcome list

val _ = Parse.hide "body";

(* ===== Canonical ABI tail, including synthetic empty constructor ===== *)

Theorem constructor_args_encode_unique:
  constructor_args_encode tops tx bs /\ constructor_args_encode tops tx bs' ==>
  bs = bs'
Proof
  rw[constructor_args_encode_def] >> gvs[]
QED

Theorem constructor_empty_canonical:
  constructor_call_free [] /\
  (constructor_args_encode [] (tx with args := []) bs <=> bs = [])
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

(* The canonical tail is exactly the source creation helper's tuple encoding,
   not calldata with a selector and not an arbitrary ABI-decodable byte string. *)
Theorem constructor_args_source_create_encoding:
  constructor_args_encode tops tx bs ==>
  ?mut args body.
    vyperInterpreter$lookup_function NONE "__init__" Deploy tops =
      SOME (mut,F,args,[],NoneT,body) /\ LENGTH tx.args = LENGTH args /\
    encode_create_ctor_args (type_env tops) (MAP SND args) tx.args = SOME bs
Proof
  rw[constructor_args_encode_def] >>
  qexistsl_tac [`mut`,`args`,`body`] >> simp[encode_create_ctor_args_def]
QED

(* The guard is Call-specific, not a ban on Pop or computed precompiles.
   Inspect nested expressions/reasons/branches as well as direct statement
   roots. The function lookup does not need already-deployed source code. *)
Theorem constructor_call_exclusion:
  ~constructor_call_free
    [FunctionDecl Deploy Payable F F "__init__" [] [] NoneT
      [If (Literal (BaseT BoolT) (BoolL T))
         [Assert (Literal (BaseT BoolT) (BoolL T))
           (AssertReason (Call NoneT (Send F) [] NONE))] []]] /\
  ~constructor_call_free
    [FunctionDecl Deploy Payable F F "__init__" [] [] NoneT
      [Return (SOME (Call NoneT (IntCall (NONE,"helper")) [] NONE))]] /\
  constructor_call_free
    [FunctionDecl Deploy Payable F F "__init__" [] [] NoneT [Pass]]
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem constructor_malformed_not_canonical:
  ~constructor_args_encode
    [FunctionDecl Deploy Payable T F "__init__" [] [] NoneT []] tx bs /\
  ~constructor_args_encode
    [FunctionDecl Deploy Payable F F "__init__" [] [] (BaseT BoolT) []] tx bs
Proof
  simp[constructor_args_encode_def, vyperInterpreterTheory.lookup_function_def,
       dest_Deploy_Fn_def]
QED

Theorem constructor_computed_builtin_not_call:
  constructor_call_free
    [FunctionDecl Deploy Payable F F "__init__" [] [] NoneT
      [Expr (Builtin (BaseT (BytesT (Fixed 32))) Sha256
         [Literal (BaseT (BytesT (Dynamic 0))) (BytesL [])])]]
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem constructor_call_free_body:
  constructor_call_free tops /\
  vyperInterpreter$lookup_function NONE "__init__" Deploy tops =
    SOME (mut,nr,args,dflts,ret,body) ==>
  ~supported_stmts_expr_exists constructor_call_root body
Proof
  simp[constructor_call_free_def]
QED

(* ===== Actual source setup; no runtime-ready undeployed target ===== *)

Theorem deploy_context_source_install:
  (deploy_evaluation_context tops am tx).sources =
    (tx.target, [(NONE,tops)]) :: am.sources /\
  (deploy_evaluation_context tops am tx).in_deploy /\
  (deploy_evaluation_context tops am tx).txn = tx
Proof
  simp[deploy_evaluation_context_def, initial_evaluation_context_def]
QED

Theorem deploy_typing_setup:
  deploy_typing_ok tops am tx ==>
  ?deploy_art runtime_art imms.
    check_contract T am.layouts tx.target [(NONE,tops)] = SOME deploy_art /\
    check_contract F am.layouts tx.target [(NONE,tops)] = SOME runtime_art /\
    machine_well_typed am /\ call_tx_well_typed tx /\
    initial_immutables (type_env_all_modules [(NONE,tops)]) [(NONE,tops)] =
      SOME imms /\
    checked_deployment_constants_ready (deploy_evaluation_context tops am tx)
      (am with <|immutables updated_by CONS (tx.target,imms);
                 exports updated_by CONS (tx.target,[])|>) tx.target [(NONE,tops)]
Proof
  simp[deploy_typing_ok_def]
QED

Theorem deploy_typing_context_well_typed:
  deploy_typing_ok tops am tx ==>
  context_well_typed (deploy_evaluation_context tops am tx)
Proof
  rw[deploy_typing_ok_def] >>
  gvs[call_tx_well_typed_def, context_well_typed_def,
      deploy_evaluation_context_def, initial_evaluation_context_def]
QED

Theorem deploy_storage_setup:
  deploy_storage_ok tops am tx <=>
  contract_storage_well_formed
    (initial_evaluation_context ((tx.target,[(NONE,tops)])::am.sources)
       am.layouts tx NONE with in_deploy := T) (initial_state am []) /\
  storage_layout_safe
    (initial_evaluation_context ((tx.target,[(NONE,tops)])::am.sources)
       am.layouts tx NONE with in_deploy := T)
Proof
  simp[deploy_storage_ok_def, deploy_evaluation_context_def]
QED

(* ===== Single fresh creation, NOT nested CALL or deployed runtime ===== *)

Theorem deploy_state_creation_entry:
  deploy_state_rel tops deploy_bc am tx es ==>
  ?ctxt rb bs.
    es.contexts = [(ctxt,rb)] /\ ctxt.msgParams.outputTo = Code tx.target /\
    ctxt.msgParams.code = deploy_bc ++ bs /\
    ctxt.msgParams.parsed = parse_code 0 FEMPTY (deploy_bc ++ bs) /\
    buffer_to_list ctxt.msgParams.data = [] /\ constructor_args_encode tops tx bs /\
    ctxt.jumpDest = NONE /\ ~ctxt.msgParams.static /\
    ctxt.pc = 0 /\ ctxt.stack = [] /\ buffer_to_list ctxt.memory = [] /\
    ctxt.returnData = [] /\ ctxt.logs = []
Proof
  rw[deploy_state_rel_def] >> qexistsl_tac [`ctxt`,`rb`,`args_bytes`] >> simp[]
QED

Theorem deploy_state_environment:
  deploy_state_rel tops deploy_bc am tx es ==>
  value_transfer_ok tx am.accounts /\
  es.rollback.accounts = accounts_after_transfer tx am.accounts /\
  es.rollback.tStorage = am.tStorage /\ am.logs = [] /\
  tx_block_fields_rel tx es.txParams /\ layouts_agree tops am tx /\
  tx.function_name = "__init__" /\ ALOOKUP am.sources tx.target = NONE
Proof
  rw[deploy_state_rel_def] >> simp[]
QED

Theorem deploy_state_rejects_nested_or_deployed:
  (~(LENGTH es.contexts = 1) \/ IS_SOME (ALOOKUP am.sources tx.target)) ==>
  ~deploy_state_rel tops deploy_bc am tx es
Proof
  rpt strip_tac >> gvs[deploy_state_rel_def]
QED

(* ===== Literal PLAN success observables, no whole-account code equality ===== *)

Theorem deploy_success_observables:
  deploy_result_rel tops runtime_bc tx es r es' (INL (am',rqs)) <=>
  ?lgs.
    frame_outcome es r es' NONE runtime_bc lgs /\
    (lookup_account tx.target es'.rollback.accounts).code = runtime_bc /\
    (!a. a <> tx.target ==>
      lookup_account a es'.rollback.accounts = lookup_account a am'.accounts) /\
    (lookup_account tx.target es'.rollback.accounts) with code := [] =
    (lookup_account tx.target am'.accounts) with code := [] /\
    es'.rollback.tStorage = am'.tStorage /\
    logs_correspond (compiled_event_info tops) (type_env tops)
      tx.target am'.logs lgs
Proof
  simp[deploy_result_rel_def]
QED

Theorem deploy_return_without_installation_rejected:
  (lookup_account tx.target es'.rollback.accounts).code <> bc ==>
  ~deploy_result_rel tops bc tx es r es' (INL (am',rqs))
Proof
  simp[deploy_result_rel_def]
QED

Theorem deploy_assert_case:
  deploy_result_rel tops bc tx es r es' (INR (AssertException s)) <=>
  ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs /\
                (exc = Reverted \/ s = "UNREACHABLE")
Proof
  simp[deploy_result_rel_def]
QED

Theorem deploy_error_case:
  deploy_result_rel tops bc tx es r es' (INR (Error e)) <=>
  decode_strictness_exempt tops e \/
  ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs
Proof
  simp[deploy_result_rel_def]
QED

Theorem deploy_failure_not_success:
  es.contexts = [(ctxt,rb)] ==>
  ~deploy_result_rel tops bc tx es (INR NONE) es' (INR (AssertException s)) /\
  (deploy_result_rel tops bc tx es (INR NONE) es' (INR (Error e)) <=>
   decode_strictness_exempt tops e)
Proof
  simp[deploy_result_rel_def, frame_outcome_def]
QED

Theorem deploy_no_control_escape:
  ~deploy_result_rel tops bc tx es r es' (INR BreakException) /\
  ~deploy_result_rel tops bc tx es r es' (INR ContinueException) /\
  ~deploy_result_rel tops bc tx es r es' (INR (ReturnException v))
Proof
  simp[deploy_result_rel_def]
QED

Theorem deploy_exemption_exact:
  decode_strictness_exempt tops e <=>
  e = RuntimeError "abi_decode invalid" /\
  ?ty. occurs_abi_decode_target ty tops /\
       is_dynamic (vyper_to_abi_type (type_env tops) ty)
Proof
  simp[decode_strictness_exempt_def]
QED

Theorem deploy_prefix_guard:
  ~(?t. ([] : word8 list) = 0xEFw :: t) /\
  ~ (~(?t. (0xEFw :: bs) = 0xEFw :: t))
Proof
  simp[]
QED

(* Every current focused export is saved, hypothesis/axiom/admission-free.
 * No deployment stage theorem is imported to this clean proof closure.
 * DISK_THM is HOL's normal saved-object/checkpoint marker, not an admission.
 *)
val _ = List.app (fn (name, th) =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn tag => tag = "DISK_THM") oracles then ()
    else raise Fail ("non-clean deployment boundary check: " ^ name ^
      " hypotheses=" ^ Int.toString (length (Thm.hyp th)) ^
      " oracles=" ^ String.concatWith "," oracles ^
      " axioms=" ^ String.concatWith "," axioms)
  end) (DB.thms "e2eDeployChecks");
