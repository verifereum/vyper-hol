(*
 * The body simulation of S1: statement cases (#637)
 *
 * One lemma for each statement case of evaluate_ind that bodySimMain's
 * body_sim_mutual does not close in a line or two.  Those marked GAP are
 * cheated; their comments name the existing lemmas they dispatch to and
 * what is left.  A case whose covered forms are proved dispatches the rest
 * to a cheated lemma marked RESIDUAL, whose comment names the premises
 * missing for the remaining forms.  The declarations, AnnAssign and For,
 * are in bodySimDeclCases, and Log in bodySimLog.
 *
 * TOP-LEVEL:
 *   body_*_case       — one case of the induction each
 *   body_*_other      — the residual forms of a case
 *   body_assign_local_memory — x = e for a local x held in memory
 *   stmt_expr_body_pre — a statement's expression meets expr_body_pre
 *   supported_expr_body_calls, supported_string_reason_body_calls — a
 *                       supported expression or reason runs no EVM code
 *                       and calls only the main module's functions
 *   reason_covered    — a reason compiles to a form the reason lemmas take
 *   supported_reason_code — a supported reason they don't take is an
 *                       immutable's, a pointer into code
 *   no_internal_call_int_calls, supported_pure_int_calls — no internal
 *                       call means int_calls_* = []
 *   expr_body_pre_eval_result, expr_body_pre_eval — evaluation keeps
 *                       expr_sim_inv and types the value
 *   type_widens_to_word — widening to a word type is equality
 *   expr_sim_inv_stmt  — expr_sim_inv after a statement, at the type
 *                        environment and compile environment it gives
 *   ce_locals_declared_declare_local, ce_locals_declared_stmt — the same
 *                        for ce_locals_declared
 *   locals_alloc_ok_extend, locals_alloc_ok_stmt — the same for
 *                        locals_alloc_ok
 *   compile_expr_open  — a supported expression that evaluates compiles
 *                        without terminating its block
 *   eval_stmts_popped_keys_indexed — statement evaluation keeps
 *                        popped_keys_indexed
 *
 * Helper:
 *   stmts_env_cs_mono, stmt_env_declare, declare_stmt_local_other,
 *   type_stmt_other    — stmt_env and type_stmt of a statement
 *   same_frame_trans, body_inv_same_frame, frame_ret_ok_same_frame,
 *   stmt_exprs_ok_same_frame, stmts_exprs_ok_EVERY — the frame facts
 *                        at a later compile env of the same body
 *   expr_sim_inv_push_scope — expr_sim_inv in a new scope
 *   body_inv_mcopy     — the frame's target has MCOPY
 *)

Theory bodySimStmtCases
Ancestors
  valueEncodingProps
  exprSimSource bodyExprPreFacts exprSimTopLevelProps stmtSimBreak stmtSimContinue stmtSimExpr stmtSimSeqEnv stmtSimPass stmtSimProps exprSimHypsDefs stmtSimZero stmtSimDefs loweringPosts bodyAppendStorageFacts bodyAppendStorageAdapter
  vyperStorageLayoutSafety vyperLookupStorage
  list finite_map bodySim allocLimits allocLimitsProps  exprSimHyps exprLoweringProps
  stmtSimIf stmtLoweringMono stmtLowering compileEnv fragExec
  supportedExprTraverse supportedStmtTraverse supportedStmts
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  vyperTypeCallStackSoundness stmtSimReason stmtSimReasonExpr
  stmtSimReasonStorage stmtSimReasonCode supportedExprs stmtSimAssign stmtSimDeclStore
  stmtSimAugAssign vyperTypeEvalSoundness vyperTypeInvariants
  vyperTypeExprSoundness vyperEvalOutcomeSuffix exprSimMain
  exprReasonOperand
  vyperTypeValues vyperTyping vyperTypeDefaults stmtSimAssignTuple
  vyperTypeEnvPreservation bodySimExprCases bodyStoragePreservation
  vyperCallOutcomeStorage vyperTypeStoragePreservation
  stmtSimAssignStorage supportedDecls vyperTypeContractStaticMaps
  vyperTypeContract compileVyper supportedTypes stmtSimAssignAttr
  stmtSimAssignStorageCopy
  stmtSimAugAssignAttr stmtSimAssignAttrStorage stmtSimAugAssignStorage
  stmtSimAugAssignAttrStorage stmtSimAssignMem stmtSimAssignTupleMem
  stmtSimAssignTupleTargets
  memoryLocalRhsProps stmtPoppedKeys exprOpenMain bodyStorageMetadata
Libs
  monadsyntax

(* ===== Helpers ===== *)


(* ===== The compile environment after a statement ===== *)

(* compile_expr leaves its block open for a supported expression of the
   frame that evaluates.  Not every expression does: the lowering's
   fallbacks end their block in INVALID.  Which fallback a module variable
   takes depends on cenv.ce_module_vars, so the storage and transient bindings
   that state_rel gives are premises.  The induction is exprOpenMain's
   compile_expr_open_general. *)
Theorem compile_expr_open:
  !tops ctx cenv cx env e es tv es1 sa vv sb.
    body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_body_pre cenv cx env e es /\
    storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
    eval_expr cx e es = (INL tv, es1) /\
    compile_expr cenv (expr_type e) e sa = (vv, sb) /\
    ~block_is_terminated sa ==>
    ~block_is_terminated sb
Proof
  cheat
QED

(* An assertion with no reason: stmtSimIf's compile_assert_frag. *)
Theorem body_assert_case:
  !cx e ak.
    (ak = AssertBare \/ ak = AssertUnreachable) /\ body_expr_ok cx e ==>
    body_stmt_ok cx (Assert e ak)
Proof
  cheat
QED

(* ===== Cases ===== *)

(* ===== Statements ===== *)

Theorem body_pass_case:
  !cx. body_stmt_ok cx Pass
Proof
  cheat
QED

Theorem body_continue_case:
  !cx. body_stmt_ok cx Continue
Proof
  cheat
QED

Theorem body_break_case:
  !cx. body_stmt_ok cx Break
Proof
  cheat
QED

(* The frame's RetQ (frame_ret_ok). *)
Theorem body_return_none_case:
  !cx. body_stmt_ok cx (Return NONE)
Proof
  cheat
QED

Theorem body_return_case:
  !cx e. body_expr_ok cx e ==> body_stmt_ok cx (Return (SOME e))
Proof
  cheat
QED

(* ===== Reasons ===== *)

(* The reason's compiled value is one the revert's encoder takes: a
   word or a memory buffer (stmtSimReasonExpr), or a storage or transient
   pointer (stmtSimReasonStorage). *)
Definition reason_covered_def:
  reason_covered cenv r <=>
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_vv_ok vv) \/
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_storage_vv vv)
End

Theorem well_typed_literal_string[local]:
  !ty s. well_typed_literal ty (StringL s) ==> ?n. ty = BaseT (StringT n)
Proof
  cheat
QED

(* Only an internal call is lowered at a type its source type does not
   fix: the callee's declared return type. *)
Theorem lowered_value_type_not_call_word[local]:
  !cenv e. (!a t es d. e <> Call a t es d) /\ ~is_word_type (expr_type e) ==>
           ~is_word_type (lowered_value_type cenv e)
Proof
  cheat
QED

(* A supported reason is a string expression (supported_string_reason),
   so it compiles to a memory or stack value, a storage or transient
   pointer, or a pointer into code (compile_expr_string_reason):
   expr_sim_inv holds each local through a variable pointer.  The first
   two are reason_covered. *)
Theorem supported_reason_code:
  !cenv cx env es tops e.
    expr_sim_inv cenv cx env es /\
    supported_string_reason tops e /\ well_typed_expr env e /\
    ~reason_covered cenv e ==>
    !sa vv sb. compile_expr cenv (expr_type e) e sa = (vv, sb) ==>
               reason_code_vv vv
Proof
  cheat
QED

(* A reason read from an immutable, whose compiled value is a pointer into
   code (supported_reason_code): the revert's encoder copies it out of code
   (stmtSimReasonCode), the body being runtime code (body_inv).  A string
   literal goes to stmtSimReason. *)
Theorem body_raise_reason_other:
  !ctx func cx lctx RetQ cenv tops bindings env ret_ty e es res es'.
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Raise (RaiseReason e)) /\
    expr_sim_inv cenv cx env es /\
    IS_SOME (type_stmt env ret_ty (Raise (RaiseReason e))) /\
    stmt_exprs_ok cenv (Raise (RaiseReason e)) /\
    call_evaluation_safe cx (int_calls_stmt (Raise (RaiseReason e))) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    (!sa vv sb. compile_expr cenv (expr_type e) e sa = (vv, sb) ==>
                reason_code_vv vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Raise (RaiseReason e)))
      (eval_stmt cx (Raise (RaiseReason e))) es
Proof
  cheat
QED

(* A string literal reason (stmtSimReason), one whose compiled value
   reason_covered covers (stmtSimReasonExpr, stmtSimReasonStorage), or a
   pointer into code (body_raise_reason_other). *)
Theorem body_raise_reason_case:
  !cx e. body_expr_ok cx e ==> body_stmt_ok cx (Raise (RaiseReason e))
Proof
  cheat
QED

(* As body_raise_reason_other, after the condition fails. *)
Theorem body_assert_reason_other:
  !ctx func cx lctx RetQ cenv tops bindings env ret_ty e se es res es'.
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assert e (AssertReason se)) /\
    expr_sim_inv cenv cx env es /\
    IS_SOME (type_stmt env ret_ty (Assert e (AssertReason se))) /\
    stmt_exprs_ok cenv (Assert e (AssertReason se)) /\
    call_evaluation_safe cx (int_calls_stmt (Assert e (AssertReason se))) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!es1. (do raw <- eval_expr cx e; read_result cx raw od) es =
             (INL (BoolV F), es1) ==>
           expr_vv_sim ctx func cenv cx (expr_type se) se es1) /\
    (!sa vv sb. compile_expr cenv (expr_type se) se sa = (vv, sb) ==>
                reason_code_vv vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assert e (AssertReason se)))
      (eval_stmt cx (Assert e (AssertReason se))) es
Proof
  cheat
QED

(* The reason simulates where the condition is false: both are pure, so
   the condition's evaluation keeps expr_sim_inv (expr_sim_pre_eval). *)
Theorem assert_reason_vv_sim[local]:
  !cx e se tops ctx func cenv env es es1.
    (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_expr_ok cx se) /\
    body_inv tops ctx cenv cx /\ expr_sim_pre cenv cx env e es /\
    well_typed_expr env se /\ int_calls_expr se = [] /\
    ~expr_has_evm_run se /\
    ~supported_expr_exists
       (\e. ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) se /\
    (do raw <- eval_expr cx e; read_result cx raw od) es =
      (INL (BoolV F), es1) ==>
    expr_vv_sim ctx func cenv cx (expr_type se) se es1
Proof
  cheat
QED

(* As body_raise_reason_case, after compile_assert_frag's condition. *)
Theorem body_assert_reason_case:
  !cx e se.
    (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_expr_ok cx se) /\
    body_expr_ok cx e ==>
    body_stmt_ok cx (Assert e (AssertReason se))
Proof
  cheat
QED

(* An append to a storage or transient DynArray, the only target
   supported_append_target admits.  The helper adapter relates both writes. *)
Theorem body_append_storage_other:
  !cx nid e.
    (!s'' p t'. eval_target_place cx (TopLevelNameTarget nid) s'' = (INL p,t') ==>
                body_expr_ok cx e) ==>
    body_stmt_ok cx (Append (TopLevelNameTarget nid) e)
Proof
  cheat
QED

(* supported_append_target admits no local, subscript or attribute target
   (#549, #559), so the storage root is the only form. *)
Theorem body_append_case:
  !cx t e.
    (!s'' p t'. eval_target_place cx t s'' = (INL p,t') ==> body_expr_ok cx e) /\
    body_base_target_ok cx t ==>
    body_stmt_ok cx (Append t e)
Proof
  cheat
QED

(* ===== Assignments ===== *)

(* expr_sim_pre_eval_result and expr_sim_pre_eval under expr_body_pre
   (exprSimHyps' expr_body_pre_eval_result). *)
Theorem expr_body_pre_eval_result:
  !cenv cx env e es res es'.
    expr_body_pre cenv cx env e es /\ eval_expr cx e es = (res, es') ==>
    expr_sim_inv cenv cx env es'
Proof
  cheat
QED

Theorem expr_body_pre_eval:
  !cenv cx env e es res es'.
    expr_body_pre cenv cx env e es /\
    (do result <- eval_expr cx e; read_result cx result od) es = (res, es') ==>
    expr_sim_inv cenv cx env es' /\
    !v. res = INL v ==> value_runtime_typed env (expr_type e) v
Proof
  cheat
QED

(* An assignment to a word local: stmtSimAssign's
   compile_assign_local_stmt_frag. *)
Theorem body_assign_local_word[local]:
  !cx id e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res es'
   ty.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    FLOOKUP env.var_types id = SOME ty /\ is_word_type ty ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  cheat
QED

(* A storage declaration found by name is a variable declaration of tops
   under that name. *)

Theorem find_var_decl_storage_some[local]:
  !ts vis mut id ty init.
    MEM (VariableDecl vis mut id ty init) ts /\
    (mut = Storage \/ mut = Transient) ==>
    find_var_decl_by_name id ts <> NONE
Proof
  cheat
QED


(* expr_sim_inv's storage-variable clause from the program's frame: in a
   single-module program, a storage or transient variable has its declared
   type in ce_module_var_type and is not a mapping. *)
Theorem body_inv_storage_var_types:
  !tops ctx cenv cx.
    body_inv tops ctx cenv cx /\
    (!src ts. get_module_code cx src = SOME ts ==> src = NONE) ==>
    !src id ts tr typ id_str.
      get_module_code cx src = SOME ts /\
      find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) ==>
      cenv.ce_hashmap_info (src,id) = NONE /\
      cenv.ce_module_var_type (src,id) = SOME typ
Proof
  cheat
QED

Theorem env_assignable_find_NONE[local]:
  !env cx st src id ty.
    env_consistent env cx st /\
    FLOOKUP env.bare_global_assignable (src, id) = SOME ty ==>
    ?ts. get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE
Proof
  cheat
QED

(* A supported scalar target is a word variable of tops in storage or
   transient storage. *)
Theorem supported_scalar_target_decl[local]:
  !tops src id.
    supported_scalar_target tops (src, id) ==>
    src = NONE /\ find_var_decl_by_name id tops <> NONE /\
    ?vis mut ty slot. MEM (VariableDecl vis mut id ty slot) tops /\
                      is_word_type ty
Proof
  cheat
QED

(* An assignment to a word storage or transient variable:
   stmtSimAssignStorage's compile_assign_storage_typed_stmt_frag.  The
   typing finds the variable's declaration and layout slot, and body_inv's
   module clauses give cenv's view of it. *)
Theorem body_assign_toplevel_word[local]:
  !cx src id e tops ctx func cenv env env' ret_ty lctx RetQ es res es'.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\
    supported_scalar_target tops (src, id) /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget (src, id))) e) =
      SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget (src, id))) e) /\
    call_evaluation_safe cx
      (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget (src, id))) e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (Assign (BaseTarget (TopLevelNameTarget (src, id))) e))
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src, id))) e)) es
Proof
  cheat
QED

(* An assignment to a local in memory of the local's own type, a bytestring
   (a narrower one widens: Bytes[10] into Bytes[64]), or an empty value of a
   type with a length word: stmtSimAssignMem's
   compile_assign_local_memory_stmt_frag and the same for the widening and
   for the empty value, as stmtSimDeclMem's and stmtSimDeclEmpty's
   declarations.  The local's size is below 2 ** 64 (locals_alloc_ok), so
   its buffer and a bytestring copy's length word fit below 2 ** 256. *)
Theorem body_assign_local_rhs_pre[local]:
  !cx id e tops bindings ctx cenv env env' ret_ty es ty.
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    FLOOKUP env.var_types id = SOME ty ==>
    supported_expr tops e /\ well_typed_expr env e /\
    type_widens_to env.type_defs (expr_type e) ty /\
    expr_body_pre cenv cx env e es
Proof
  cheat
QED

Theorem body_assign_local_memory_read[local]:
  !cenv cx env e es tops id ty tyv v es1 entry.
    expr_body_pre cenv cx env e es /\ supported_expr tops e /\
    supported_program tops /\
    cenv.ce_func_return_type = build_func_return_type tops /\
    get_module_code cx NONE = SOME tops /\
    FLOOKUP env.var_types id = SOME ty /\
    type_widens_to env.type_defs (expr_type e) ty /\
    (expr_type e = ty \/ is_bytestring_type ty) /\
    evaluate_type (get_tenv cx) ty = SOME tyv /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es1) /\
    lookup_scopes id es1.scopes = SOME entry /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    entry.type = tyv /\ value_has_type tyv v /\
    val_footprint tyv v <= type_memory_bytes cenv (lowered_value_type cenv e)
Proof
  cheat
QED

Theorem body_assign_local_memory:
  !cx id e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res es'
   ty.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
    expr_sim_inv cenv cx env es /\ locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    FLOOKUP env.var_types id = SOME ty /\ ~is_word_type ty /\
    0 < type_memory_bytes cenv ty /\
    (lowered_value_type cenv e = ty \/ is_bytestring_type ty \/
     has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  cheat
QED

(* An assignment to a word field of a local struct: stmtSimAssignAttr's
   compile_assign_attr_local_case. *)
Theorem body_assign_attr_local[local]:
  !cx id fld e tops ctx func cenv env env' ret_ty lctx RetQ es res es' sid
   fty.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty
      (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) =
      SOME env' /\
    stmt_exprs_ok cenv
      (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt
         (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)) /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    attribute_type env.type_defs (StructT sid) fld = SOME fty /\
    is_word_type fty ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)) es
Proof
  cheat
QED

(* A struct field write the supported subset admits is to a storage or
   transient struct of the main module, tops. *)
Theorem supported_storage_field_write_decl[local]:
  !tops src id fld.
    supported_storage_field_write tops (src, id) fld ==>
    src = NONE /\ find_var_decl_by_name id tops <> NONE /\
    ?mut sid slot. MEM (VariableDecl Private mut id (StructT sid) slot) tops
Proof
  cheat
QED

(* An assignment to a word field of a storage or transient struct:
   stmtSimAssignAttrStorage's compile_assign_attr_storage_case.  The
   supported subset puts the struct in tops with a slot, the typing finds
   its declaration and layout slot, and body_inv's module clauses give
   cenv's view of it. *)
Theorem body_assign_attr_storage[local]:
  !cx src id fld e tops ctx func cenv env env' ret_ty lctx RetQ es res es'
   fty.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    supported_storage_field_write tops (src, id) fld /\
    type_place_target env
      (AttributeTarget (TopLevelNameTarget (src, id)) fld) =
      SOME (Type fty) /\
    is_word_type fty /\
    type_stmt env ret_ty
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id)) fld))
         e) = SOME env' /\
    stmt_exprs_ok cenv
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id)) fld))
         e) /\
    call_evaluation_safe cx
      (int_calls_stmt
         (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id))
            fld)) e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id))
            fld)) e))
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id)) fld)) e)) es
Proof
  cheat
QED

Theorem body_assign_copy_rhs_pre[local]:
  !tops ctx cenv cx e env es ret_ty nsid env'.
    body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e) =
      SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) ==>
    expr_body_pre cenv cx env e es
Proof
  cheat
QED

Theorem body_assign_copy_region[local]:
  !cx mid id tr off tvt.
    storage_layout_safe cx /\
    storage_var_info cx mid id = SOME (tr,off,tvt) /\
    0 < type_slot_size tvt ==>
    off + type_slot_size tvt <= dimword (:256) /\
    (!mid' n' subs' k' tv'.
      declared_storage_region cx mid' n' subs' = SOME (tr,k',tv') /\
      (k',tv') <> (n2w off,tvt) ==>
      ranges_disjoint off (type_slot_size tvt) (w2n k') (type_slot_size tv'))
Proof
  cheat
QED

Theorem body_assign_copy_target[local]:
  !tops ctx cenv cx src id mut ty ast_slot env es ret_ty e env'.
    body_inv tops ctx cenv cx /\
    supported_variable_decl tops (src,id) = SOME (Private,mut,ty,SOME ast_slot) /\
    (mut = Storage \/ mut = Transient) /\ expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget (src,id))) e) =
      SOME env' ==>
    src = NONE /\ get_module_code cx NONE = SOME tops /\
    cenv.ce_hashmap_info (NONE,id) = NONE /\
    cenv.ce_module_var_type (NONE,id) = SOME ty /\
    ?tr id_str off tvt.
      find_var_decl_by_name id tops = SOME (StorageVarDecl tr ty,id_str) /\
      lookup_var_slot_from_layout cx tr NONE id_str = SOME off /\
      evaluate_type (get_tenv cx) ty = SOME tvt
Proof
  cheat
QED

Theorem storage_scalar_fit_equal[local]:
  !tops fuel t u.
    supported_scalar_type t /\
    supported_nested_type supported_full_word_type fuel tops u /\
    arg_type_fits t u ==> t = u
Proof
  cheat
QED

Theorem storage_scalars_fit_equal[local]:
  !ts us tops fuel.
    EVERY supported_scalar_type ts /\
    EVERY (supported_nested_type supported_full_word_type fuel tops) us /\
    arg_types_fit ts us ==> ts = us
Proof
  cheat
QED

Theorem storage_value_fit_equal[local]:
  !tops t u.
    supported_value_type tops t /\ supported_storage_type tops u /\
    (!et n. u <> ArrayT et (Dynamic n)) /\ arg_type_fits t u ==> t = u
Proof
  cheat
QED

Theorem storage_not_bytestring[local]:
  !tops t. supported_storage_type tops t ==> ~is_bytestring_type t
Proof
  cheat
QED

Theorem storage_rhs_lowered_type[local]:
  !cenv e tops ctx cx env es.
    body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
    expr_body_pre cenv cx env e es /\ supported_expr tops e /\
    supported_storage_type tops (expr_type e) /\
    (!elem n. expr_type e <> ArrayT elem (Dynamic n)) ==>
    lowered_value_type cenv e = expr_type e
Proof
  cheat
QED

(* An assignment to a private storage or transient variable of a type that
   is not a word, not a DynArray and not empty, from a value of exactly that
   type: stmtSimAssignStorageCopy's compile_assign_storage_copy_stmt_frag.
   The region separation it asks for comes from storage_layout_safe in
   expr_sim_inv. *)
Theorem body_assign_toplevel_copy[local]:
  !cx nsid e tops ctx func cenv env env' ret_ty lctx RetQ es res es' mut ty
   slot.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\
    supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME slot) /\
    (mut = Storage \/ mut = Transient) /\
    ~is_word_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
    0 < type_memory_bytes cenv ty /\ expr_type e = ty /\
    supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e) =
      SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) es
Proof
  cheat
QED

(* A local assigned to takes memory: its type is a widening of the assigned
   value's type, which is assignable. *)
Theorem assign_local_memory_bytes_pos[local]:
  !cenv cx env es ret_ty id e env' ty.
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    FLOOKUP env.var_types id = SOME ty ==>
    0 < type_memory_bytes cenv ty
Proof
  cheat
QED

(* RESIDUAL (#637 assignments): the other base targets.
   - A local in memory that body_assign_local_memory leaves: a value
     that widens to a type other than a bytestring (type_widens_to: a
     DynArray of a smaller bound, elementwise) has no statement lemma.
   - A storage or transient variable that is not a word, other than
     body_assign_toplevel_copy's: a DynArray (compile_dynarray_to_storage),
     a value of a narrower type (a widened bytestring), or a type of size
     0: no statement lemma.
   - An immutable (supported_target's supported_immutable_type): no
     statement lemma.
   - An attribute target other than a word field of a local struct or of
     a storage or transient struct:
     - a field of a local, storage or transient struct that is not a
       word: no statement lemma (the copy of an aggregate into the field);
     - a field of a field or of a subscript: no statement lemma (the
       simulation of compile_get_target_ptr on eval_target_place).
   - Subscript targets: no statement lemma (#851). *)
Theorem body_assign_other:
  !cx t e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res es'.
    (!s'' pv t'. eval_expr cx e s'' = (INL pv,t') ==> body_base_target_ok cx t) /\
    body_expr_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget t) e) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              is_word_type ty) /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              ~is_word_type ty /\
              (expr_type e = ty \/ is_bytestring_type ty \/
               has_length_word (expr_type e) /\ is_empty_value_expr e)) /\
    ~(?nsid. t = TopLevelNameTarget nsid /\ supported_scalar_target tops nsid) /\
    ~(?nsid mut ty slot.
        t = TopLevelNameTarget nsid /\
        supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME slot) /\
        (mut = Storage \/ mut = Transient) /\
        ~is_word_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
        0 < type_memory_bytes cenv ty /\ expr_type e = ty) /\
    ~(?id fld sid fty.
        t = AttributeTarget (NameTarget id) fld /\
        FLOOKUP env.var_types id = SOME (StructT sid) /\
        attribute_type env.type_defs (StructT sid) fld = SOME fty /\
        is_word_type fty) /\
    ~(?nsid fld fty.
        t = AttributeTarget (TopLevelNameTarget nsid) fld /\
        supported_storage_field_write tops nsid fld /\
        type_place_target env t = SOME (Type fty) /\ is_word_type fty) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e))
      (eval_stmt cx (Assign (BaseTarget t) e)) es
Proof
  cheat
QED

(* RESIDUAL (#767): a memory-backed local assigned an internal call whose
   return type widens to the call's type other than as a bytestring
   (type_widens_to: a DynArray of a smaller bound, a tuple elementwise). *)
Theorem body_assign_widened_aggregate_call:
  !cx id e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res es'
   ty.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
    expr_sim_inv cenv cx env es /\ locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    FLOOKUP env.var_types id = SOME ty /\ ~is_word_type ty /\
    0 < type_memory_bytes cenv ty /\
    ~(lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  cheat
QED

Theorem body_assign_case:
  !cx t e.
    (!s'' pv t'. eval_expr cx e s'' = (INL pv,t') ==> body_base_target_ok cx t) /\
    body_expr_ok cx e ==>
    body_stmt_ok cx (Assign (BaseTarget t) e)
Proof
  cheat
QED

(* Both lowering entry points check that the target supports MCOPY. *)
Theorem body_inv_mcopy[local]:
  !tops ctx cenv cx. body_inv tops ctx cenv cx ==> cenv.ce_target CapMcopy
Proof
  cheat
QED

(* A local of a tuple target, of a type with a size that is not 0: held
   through a pointer at its own type, and if in memory, with a size below
   2 ** 64 (locals_alloc_ok), so a bytestring copy's 64 bytes of rounding
   fit below 2 ** 256. *)
Theorem tuple_target_local_ptr[local]:
  !cenv cx env es id ty tv.
    expr_sim_inv cenv cx env es /\ locals_alloc_ok cenv env /\
    FLOOKUP env.var_types id = SOME ty /\ 0 < type_memory_bytes cenv ty /\
    evaluate_type (get_tenv cx) ty = SOME tv ==>
    ?p sz vt.
      FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
      cenv.ce_var_type id = SOME vt /\
      if is_word_type ty then is_word_type vt
      else
        (vt = ty \/ is_bytestring_type vt /\ is_bytestring_type ty) /\
        type_memory_bytes cenv ty = type_memory_size tv /\
        ?vtv. evaluate_type (get_tenv cx) vt = SOME vtv /\
              type_memory_bytes cenv vt = type_memory_size vtv /\
              0 < type_memory_size vtv /\
              type_memory_size vtv + 64 < dimword (:256)
Proof
  cheat
QED

(* After the source is read, a local of a tuple target holds a value of its
   own type: a word as stored, otherwise at the type its pointer has. *)
Theorem tuple_target_local_lays_out[local]:
  !cenv cx env es1 id ty tv v entry.
    expr_sim_inv cenv cx env es1 /\ FLOOKUP env.var_types id = SOME ty /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
    lookup_scopes id es1.scopes = SOME entry ==>
    if is_word_type ty then store_lays_out tv entry.type v
    else
      ?vt. cenv.ce_var_type id = SOME vt /\
           evaluate_type (get_tenv cx) vt = SOME entry.type /\
           value_has_type entry.type v
Proof
  cheat
QED

(* The buffer a tuple assignment stages a memory view's value in fits
   below 2 ** 256: alloc_limits_stmt bounds it by 2 ** 64. *)
Theorem tuple_staging_bound[local]:
  !cenv cx env es g e tys tvs.
    expr_sim_inv cenv cx env es /\
    stmt_exprs_ok cenv (Assign (TupleTarget g) e) /\
    expr_type e = TupleT tys /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    is_memory_view e ==>
    type_memory_size (TupleTV tvs) < dimword (:256)
Proof
  cheat
QED

(* A tuple of locals of types with sizes that are not 0 (a word's is 32):
   stmtSimAssignTupleMem's compile_assign_tuple_locals_memory_stmt_frag.
   The target has MCOPY (body_inv_mcopy). *)
Theorem body_assign_tuple_locals[local]:
  !cx ids e tops ctx func cenv env env' ret_ty lctx RetQ es res es'.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\ locals_alloc_ok cenv env /\
    type_stmt env ret_ty
      (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) =
      SOME env' /\
    stmt_exprs_ok cenv
      (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt
         (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)) /\
    ids <> [] /\
    EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty /\
                     0 < type_memory_bytes cenv ty) ids /\
    lowered_value_type cenv e = expr_type e ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e))
      (eval_stmt cx (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)) es
Proof
  cheat
QED

(* The locals a tuple is assigned to take memory: their types are the
   tuple's element types, which are assignable, so they take a storage slot
   (assignable_type_slot_size_pos). *)
Theorem assign_tuple_locals_bytes_pos[local]:
  !cenv cx env es ret_ty ids e env'.
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty
      (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) =
      SOME env' ==>
    EVERY (\id. !ty. FLOOKUP env.var_types id = SOME ty ==>
                     0 < type_memory_bytes cenv ty) ids
Proof
  cheat
QED

Theorem body_assign_tuple_rhs_pre[local]:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) ==>
  expr_body_pre cenv cx env e es
Proof
  cheat
QED

Theorem body_tuple_target_local_aligned[local]:
  expr_sim_inv cenv cx env es /\ FLOOKUP env.var_types id = SOME ty /\
  0 < type_memory_bytes cenv ty /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  tuple_target_aligned cenv cx (BaseTarget (NameTarget id)) ty tv
Proof
  cheat
QED

Theorem body_tuple_target_local_layout[local]:
  expr_sim_inv cenv cx env es /\
  well_typed_atarget env (BaseTarget (NameTarget id)) ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v ==>
  tuple_target_layout es.scopes (BaseTarget (NameTarget id)) ty tv v
Proof
  cheat
QED

Theorem body_tuple_target_local_room[local]:
  expr_sim_inv cenv cx env es /\ locals_alloc_ok cenv env /\
  FLOOKUP env.var_types id = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  type_memory_size tv + 64 < dimword (:256)
Proof
  cheat
QED

Theorem body_tuple_target_toplevel_aligned[local]:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  supported_scalar_target tops nsid /\
  type_place_target env (TopLevelNameTarget nsid) = SOME (Type ty) /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  tuple_target_aligned cenv cx (BaseTarget (TopLevelNameTarget nsid)) ty tv
Proof
  cheat
QED

Theorem body_tuple_target_field_aligned[local]:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  supported_storage_field_write tops nsid fld /\
  type_place_target env (AttributeTarget (TopLevelNameTarget nsid) fld) =
    SOME (Type ty) /\ is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  tuple_target_aligned cenv cx
    (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) ty tv
Proof
  cheat
QED

Theorem body_tuple_target_ready[local]:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  locals_alloc_ok cenv env /\ well_typed_atarget env g ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  ((?id lty. g = BaseTarget (NameTarget id) /\
            FLOOKUP env.var_types id = SOME lty /\
            0 < type_memory_bytes cenv lty) \/
   (?nsid. g = BaseTarget (TopLevelNameTarget nsid) /\
           supported_scalar_target tops nsid) \/
   (?nsid fld fty.
      g = BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld) /\
      supported_storage_field_write tops nsid fld /\
      type_place_target env (AttributeTarget (TopLevelNameTarget nsid) fld) =
        SOME (Type fty) /\ is_word_type fty)) ==>
  tuple_target_aligned cenv cx g ty tv /\
  (~is_word_type ty ==> type_memory_size tv + 64 < dimword (:256)) /\
  (!es1 v. expr_sim_inv cenv cx env es1 /\ value_has_type tv v ==>
     tuple_target_layout es1.scopes g ty tv v)
Proof
  cheat
QED

(* Every element of the tuple is a local of a size that is not 0, a word
   storage or transient variable, or a word field of a storage or transient
   struct, mixed in any order (an empty tuple is not assignable_type, so it
   does not type-check).  The lowering loads
   every element before it stores any (compile_tuple_unpack); each store
   evaluates its target (compile_get_target_ptr) right before it, as the
   source evaluates each element's place right before its write
   (assign_tuple_target_list). *)
Theorem body_assign_tuple_targets[local]:
  !cx gs e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res es'.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    lowered_value_type cenv e = expr_type e /\
    EVERY (\g. (?id ty. g = BaseTarget (NameTarget id) /\
                        FLOOKUP env.var_types id = SOME ty /\
                        0 < type_memory_bytes cenv ty) \/
               (?nsid. g = BaseTarget (TopLevelNameTarget nsid) /\
                       supported_scalar_target tops nsid) \/
               (?nsid fld fty.
                  g = BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld) /\
                  supported_storage_field_write tops nsid fld /\
                  type_place_target env
                    (AttributeTarget (TopLevelNameTarget nsid) fld) =
                    SOME (Type fty) /\ is_word_type fty)) gs ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  cheat
QED

(* RESIDUAL (#637 tuple assignments): the other tuple targets, each with
   an element body_assign_tuple_targets leaves.
   - A local of size 0 next to a storage element: there is none (a
     tuple element's type is assignable, assign_tuple_locals_bytes_pos), but
     the case split doesn't show it yet.
   - A subscript element (a storage array or mapping): its target's place
     needs the subscript step of the target/place judgment
     (targetPlaceSimCases' target_subscript_case), not proved yet.
   - A field of a storage or transient struct that is not a word: the
     copy of an aggregate into storage, as for Assign (body_assign_other).
   - An immutable: the lowering keeps it in code (LocCode), which nothing
     relates to the source's immutables yet (targetPlaceSim's
     immutable_root).
   A nested TupleTarget is not supported (supported_assignment). *)
Theorem body_assign_tuple_other:
  !cx gs e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res es'.
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_ok cx (TupleTarget gs) v) /\ body_expr_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    ~(?ids. gs = MAP (BaseTarget o NameTarget) ids /\ ids <> [] /\
            EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty) ids) /\
    ~EVERY (\g. (?id ty. g = BaseTarget (NameTarget id) /\
                         FLOOKUP env.var_types id = SOME ty /\
                         0 < type_memory_bytes cenv ty) \/
                (?nsid. g = BaseTarget (TopLevelNameTarget nsid) /\
                        supported_scalar_target tops nsid) \/
                (?nsid fld fty.
                   g = BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld) /\
                   supported_storage_field_write tops nsid fld /\
                   type_place_target env
                     (AttributeTarget (TopLevelNameTarget nsid) fld) =
                     SOME (Type fty) /\ is_word_type fty)) gs ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  cheat
QED

(* RESIDUAL (#767): a tuple target assigned an internal call whose return
   type widens to the call's type (type_widens_to: a tuple elementwise), so
   the tuple is unpacked at the callee's return type. *)
Theorem body_assign_tuple_widened_call[local]:
  !cx gs e tops ctx func cenv env env' ret_ty lctx RetQ es res es'.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\ locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
    lowered_value_type cenv e <> expr_type e ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  cheat
QED

Theorem body_assign_tuple_case:
  !cx gs e.
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_ok cx (TupleTarget gs) v) /\ body_expr_ok cx e ==>
    body_stmt_ok cx (Assign (TupleTarget gs) e)
Proof
  cheat
QED

(* ===== Augmented assignments ===== *)

(* x op= e on a local: stmtSimAugAssign's compile_augassign_local_case,
   the operand's internal calls allowed. *)
Theorem body_augassign_local[local]:
  !cx ty id bop e tops ctx func cenv env env' ret_ty lctx RetQ es res es'.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (NameTarget id) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ok cx e) /\
    body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (AugAssign ty (NameTarget id) bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty (NameTarget id) bop e) /\
    call_evaluation_safe cx
      (int_calls_stmt (AugAssign ty (NameTarget id) bop e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty (NameTarget id) bop e))
      (eval_stmt cx (AugAssign ty (NameTarget id) bop e)) es
Proof
  cheat
QED

(* x.f op= e on a field of a local struct: stmtSimAugAssignAttr's
   compile_augassign_attr_local_case.  The typing makes f's type a word
   (well_typed_binop_augassign_word), and x.f is read wherever
   expr_sim_inv holds (augassign_attr_local_place), which gives e's
   judgment. *)
Theorem body_augassign_attr_local[local]:
  !cx ty id fld bop e tops ctx func cenv env env' ret_ty lctx RetQ es res
   es'.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (AttributeTarget (NameTarget id) fld) s'' =
         (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ok cx e) /\
    body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty
      (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) =
      SOME env' /\
    stmt_exprs_ok cenv
      (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) /\
    call_evaluation_safe cx
      (int_calls_stmt
         (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
      (eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)) es
Proof
  cheat
QED

(* self.x op= e on a word storage or transient variable:
   stmtSimAugAssignStorage's compile_augassign_toplevel_case.  The typing
   finds x's declaration, and body_inv's module clauses give cenv's view of
   it, as for body_assign_toplevel_word; x's place is read wherever
   expr_sim_inv holds, which gives e's judgment. *)
Theorem body_augassign_toplevel_word[local]:
  !cx ty src id bop e tops ctx func cenv env env' ret_ty lctx RetQ es res
   es'.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (TopLevelNameTarget (src, id)) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ok cx e) /\
    body_inv tops ctx cenv cx /\ supported_scalar_target tops (src, id) /\
    supported_expr tops e /\ expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (AugAssign ty (TopLevelNameTarget (src, id)) bop e) =
      SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty (TopLevelNameTarget (src, id)) bop e) /\
    call_evaluation_safe cx
      (int_calls_stmt (AugAssign ty (TopLevelNameTarget (src, id)) bop e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (AugAssign ty (TopLevelNameTarget (src, id)) bop e))
      (eval_stmt cx (AugAssign ty (TopLevelNameTarget (src, id)) bop e)) es
Proof
  cheat
QED

(* self.x.f op= e on a word field of a storage or transient struct:
   stmtSimAugAssignAttrStorage's compile_augassign_attr_storage_case.  The
   supported subset puts the struct in tops with a slot and the typing finds
   its declaration, as for body_assign_attr_storage; x.f's slot is read
   wherever expr_sim_inv holds, which gives e's judgment. *)
Theorem body_augassign_attr_storage[local]:
  !cx ty src id fld bop e tops ctx func cenv env env' ret_ty lctx RetQ es
   res es'.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx
         (AttributeTarget (TopLevelNameTarget (src, id)) fld) s'' =
         (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ok cx e) /\
    body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    supported_storage_field_write tops (src, id) fld /\
    type_stmt env ret_ty
      (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld) bop e)
      = SOME env' /\
    stmt_exprs_ok cenv
      (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld) bop
         e) /\
    call_evaluation_safe cx
      (int_calls_stmt
         (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld)
            bop e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld)
            bop e))
      (eval_stmt cx (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld) bop e)) es
Proof
  cheat
QED

(* RESIDUAL (#637 augmented assignment): the targets other than a local, a
   field of a local struct, a word storage or transient variable
   (supported_scalar_target), or a word field of a storage or transient
   struct (supported_storage_field_write).
   - A field of a storage or transient struct the supported subset does
     not admit: no statement lemma.
   - An immutable (supported_target's supported_immutable_type): no
     statement lemma.
   - A field of a field or of a subscript: no statement lemma (the
     simulation of compile_get_target_ptr on eval_target_place).
   - Subscript targets: no statement lemma (#851). *)
Theorem body_augassign_other:
  !cx ty t bop e tops bindings ctx func cenv env env' ret_ty lctx RetQ es
   res es'.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ok cx e) /\ body_base_target_ok cx t /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AugAssign ty t bop e) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty t bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign ty t bop e)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    ~(?id. t = NameTarget id) /\
    ~(?nsid. t = TopLevelNameTarget nsid /\
             supported_scalar_target tops nsid) /\
    ~(?id fld. t = AttributeTarget (NameTarget id) fld) /\
    ~(?nsid fld. t = AttributeTarget (TopLevelNameTarget nsid) fld /\
                 supported_storage_field_write tops nsid fld) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty t bop e))
      (eval_stmt cx (AugAssign ty t bop e)) es
Proof
  cheat
QED

Theorem body_augassign_case:
  !cx ty t bop e.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ok cx e) /\ body_base_target_ok cx t ==>
    body_stmt_ok cx (AugAssign ty t bop e)
Proof
  cheat
QED

(* stmtSimIf's compile_if_stmt_frag, with the branches' judgments at the
   pushed scope. *)
Theorem body_if_case:
  !cx e ss1 ss2.
    (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_ok cx ss1) /\
    (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_ok cx ss2) /\ body_expr_ok cx e ==>
    body_stmt_ok cx (If e ss1 ss2)
Proof
  cheat
QED

(* stmtSim's compile_expr_stmt_frag_ok, given the expression's
   expr_vv_sim (the IH) and compile_expr_open. *)
Theorem body_expr_stmt_case:
  !cx e. body_expr_ok cx e ==> body_stmt_ok cx (Expr e)
Proof
  cheat
QED

(* ===== Statement lists ===== *)

Theorem body_stmts_nil_case:
  !cx. body_stmts_ok cx []
Proof
  cheat
QED

(* stmtSim's stmt_frag_cons_env: the head by the IH, the tail by the IH at
   the environments the head's typing and declaration give. *)
Theorem body_stmts_cons_case:
  !cx s ss.
    (!s'' x t. eval_stmt cx s s'' = (INL x,t) ==> body_stmts_ok cx ss) /\
    body_stmt_ok cx s ==>
    body_stmts_ok cx (s::ss)
Proof
  cheat
QED
