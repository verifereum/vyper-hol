(*
 * The body simulation of S1: the Log case (#637)
 *
 * A supported log statement names an event of the main module whose fields
 * are word types or bytestrings, with arguments of the fields' types
 * (supported_log).  body_log_case gives it stmtSimLog's
 * compile_log_stmt_frag, with the argument judgments of the induction
 * hypothesis; the event's buffers fit below 2 ** 64, as the lowering's
 * alloc_limits_stmt checks.
 *
 * TOP-LEVEL:
 *   body_log_metadata    — the compile env and the source give a supported
 *                          event the same metadata
 *   body_log_args_ready  — the arguments' judgments, from the induction
 *                          hypothesis
 *   body_log_case        — the case of the induction
 *)

Theory bodySimLog
Ancestors
  exprSimSource bodyExprPreFacts exprSimHypsDefs list bodySim bodySimStmtCases stmtSimLog exprSimHyps
  compileEnv compileVyper supportedStmts supportedDecls supportedTypes
  supportedExprs supportedExprTraverse supportedStmtTraverse vyperEvent vyperInterpreter
  vyperState vyperTypeSystem supportedProgram supportedNames vyperContext
  vyperABI vyperTypeInvariants vyperTypeExprSoundness vyperTypeCallGraph
  vyperTypeCallStackSoundness

(* ===== The event's metadata ===== *)

Theorem supported_event_fields_some[local]:
  !tops id fields.
    supported_event_fields tops id = SOME fields ==>
    ?name. id = (NONE, name) /\ MEM (EventDecl name fields) tops /\
           !tenv. lookup_event_metadata_in tenv name tops =
                  SOME (event_hash tenv name (MAP (SND o FST) fields),
                        MAP (SND o FST) fields, MAP SND fields)
Proof
  cheat
QED

Theorem event_decl_names_mem[local]:
  !tops n a. MEM (EventDecl n a) tops ==> MEM n (supported_event_names tops)
Proof
  cheat
QED

Theorem event_names_unique[local]:
  !tops n. ALL_DISTINCT (supported_event_names tops) ==> event_decl_unique n tops
Proof
  cheat
QED

(* A scalar type's ABI type does not look at the type environment. *)
Theorem scalar_abi_types_env[local]:
  !ts env env'.
    EVERY supported_scalar_type ts ==>
    vyper_to_abi_types env ts = vyper_to_abi_types env' ts
Proof
  cheat
QED

(* body_inv's ce_event_info is build_event_info's for the program, whose
   event names supported_program makes distinct, and the source finds the
   same declaration in the module get_module_code gives. *)
Theorem body_log_metadata:
  !tops ctx cenv cx id fields.
    body_inv tops ctx cenv cx /\ supported_event_fields tops id = SOME fields ==>
    ?h. cenv.ce_event_info (nsid_to_string id) =
          SOME (h, MAP (SND o FST) fields, MAP SND fields) /\
        lookup_event_metadata (get_tenv cx) cx.sources cx.txn.target id =
          SOME (h, MAP (SND o FST) fields, MAP SND fields) /\
        LENGTH (FILTER I (MAP SND fields)) <= 3 /\
        EVERY supported_scalar_type (MAP (SND o FST) fields)
Proof
  cheat
QED

(* ===== The arguments ===== *)

(* A supported pure argument meets expr_body_pre wherever expr_sim_inv
   holds: it makes no internal call and runs no EVM code. *)
Theorem log_arg_body_pre[local]:
  !tops ctx cenv cx env e calls es.
    body_inv tops ctx cenv cx /\ supported_pure_expr tops e /\
    well_typed_expr env e /\
    ~supported_expr_exists
       (\e. ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) e /\
    call_evaluation_safe cx (int_calls_expr e ++ calls) /\
    expr_sim_inv cenv cx env es ==>
    expr_body_pre cenv cx env e es
Proof
  cheat
QED

(* The arguments of a supported log are pure, so each meets expr_body_pre
   wherever expr_sim_inv holds, and its evaluation keeps expr_sim_inv and
   types its value (expr_body_pre_eval). *)
Theorem body_log_args_ready:
  !tops ctx func cenv cx env args.
    body_inv tops ctx cenv cx /\ body_exprs_ok cx args /\
    supported_pure_exprs tops args /\ well_typed_exprs env args /\
    ~supported_exprs_exists
       (\e. ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) args /\
    call_evaluation_safe cx (int_calls_exprs args) ==>
    log_args_ready ctx func cenv cx (\es. expr_sim_inv cenv cx env es) args
Proof
  cheat
QED

Theorem body_log_case:
  !cx id es. body_exprs_ok cx es ==> body_stmt_ok cx (Log id es)
Proof
  cheat
QED
