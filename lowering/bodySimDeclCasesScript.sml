(*
 * The body simulation of S1: declaration cases (#637)
 *
 * The cases of body_sim_mutual that declare a local: AnnAssign, and For,
 * whose loop variable is one.  Every declaration lemma (stmtSimDecl,
 * stmtSimDeclMem, stmtSimDeclEmpty, stmtSimFor, stmtSimForRange) asks
 * that the declared name is unbound in the compile env or held through a
 * pointer.  The typing declares only a name not in env.var_types, and
 * ce_locals_declared (bodySim) binds no other local, so the name is
 * unbound (declared_name_unbound).  The loop's scope pop also rests on
 * bodySimStmtCases' eval_stmts_popped_keys_indexed.
 *
 * TOP-LEVEL:
 *   declared_name_unbound        — a declared name is unbound
 *   declare_local_same_frame, expr_sim_inv_declare_local — the compile
 *                                  env of a declaration is a frame where
 *                                  the statement's expressions simulate
 *   expr_sim_inv_for_scope, expr_sim_inv_for_pop — expr_sim_inv into
 *                                  and out of a loop iteration's scope
 *   body_annassign_case, body_for_case — the cases
 *   body_annassign_memory        — the declarations in memory
 *   body_annassign_other         — RESIDUAL, the declarations not of a
 *                                  word type that it leaves
 *   body_for_other               — dispatcher for computed ranges and arrays
 *   body_for_array               — iteration over a fixed array
 *   body_for_range               — checked integer-range body simulation
 *)

Theory bodySimDeclCases
Ancestors
  exprSimSource
  bodyExprPreFacts
  stmtSimProps
  exprSimHypsDefs
  vyperTypeStoragePreservation
  list finite_map bodySim bodySimStmtCases allocLimits exprSimHyps exprLoweringProps stmtSimDecl stmtSimReturn stmtSimAssign bodyExprPreFacts bodyAppendStorageFacts
  stmtSimDeclMem stmtSimDeclEmpty memoryLocalRhsProps
  stmtSimFor stmtSimForParts stmtSimForRange stmtLowering stmtLoweringMono
  stmtSimForArray stmtSimForArrayFrag stmtSimForArrayFrame vyperTyping
  fragExec compileEnv supportedStmts supportedStmtTraverse vyperAST
  vyperInterpreter vyperState vyperValue vyperTypeSystem
  vyperTypeInvariants vyperTypeExprSoundness vyperTypeValues
  vyperTypeEvalSoundness vyperTypeEnvPreservation vyperTypeEnvExtension
  vyperTypeScopePop vyperEvalOutcomeSuffix vyperTypeCallGraph
  vyperEvalPreservesScopes
  vyperTypeCallStackSoundness compileVyper moduleLowering intCallCallee
Libs
  monadsyntax

(* ===== Declared names ===== *)

(* The typing declares only a name it does not know, which the compile env
   then does not bind. *)
Theorem declared_name_unbound:
  !cenv env ret_ty s env' id.
    ce_locals_declared cenv env /\ type_stmt env ret_ty s = SOME env' /\
    ((?typ e. s = AnnAssign id typ e) \/
     (?typ it n body. s = For id typ it n body)) ==>
    FLOOKUP cenv.ce_vars id = NONE
Proof
  cheat
QED

(* ===== The compile env of a declaration ===== *)

Theorem declare_local_same_frame:
  !cenv id ty st c st1.
    declare_local cenv id ty st = (c, st1) /\ cenv.ce_alloca_locals /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) ==>
    same_frame cenv c
Proof
  cheat
QED

(* Declaring a name the typing does not know keeps expr_sim_inv: its
   clauses speak of the names in env.var_types only. *)
Theorem expr_sim_inv_declare_local:
  !cenv cx env es id ty st c st1.
    expr_sim_inv cenv cx env es /\ id NOTIN FDOM env.var_types /\
    declare_local cenv id ty st = (c, st1) /\ cenv.ce_alloca_locals ==>
    expr_sim_inv c cx env es
Proof
  cheat
QED

(* ===== AnnAssign ===== *)

(* A declaration of a word type: stmtSimDecl's
   compile_annassign_typed_stmt_frag.  A word type takes no wider type, so
   the value has the declared type itself. *)
Theorem body_annassign_word[local]:
  !cx id typ e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res
   es'.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_ok cx e) /\
    body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    is_word_type typ ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  cheat
QED

Theorem body_annassign_rhs_pre[local]:
  !cenv cx env e es tops id typ ctx.
    body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) ==>
    expr_body_pre cenv cx env e es
Proof
  cheat
QED

Theorem body_annassign_declared_rhs[local]:
  !cenv cx env e es tops id typ st c st1 ctx func.
    body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
    id NOTIN FDOM env.var_types /\ FLOOKUP cenv.ce_vars id = NONE /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    body_expr_ok cx e /\ declare_local cenv id typ st = (c,st1) ==>
    expr_sim ctx func c cx (expr_type e) e es /\
    expr_vv_sim ctx func c cx (expr_type e) e es
Proof
  cheat
QED

(* A declaration of a type that is not a word, from a value of the type
   itself, a bytestring (a narrower one widens), or an empty value of a
   type with a length word: stmtSimDeclMem's
   compile_annassign_memory_widen_stmt_frag and stmtSimDeclEmpty's
   compile_annassign_empty_stmt_frag.  The declared type is below 2 ** 64
   (alloc_limits_stmt), so its buffer and a bytestring copy's length word
   fit below 2 ** 256. *)
Theorem body_annassign_memory:
  !cx id typ e tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_ok cx e) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AnnAssign id typ e) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    ~is_word_type typ /\ 0 < type_memory_bytes cenv typ /\
    (lowered_value_type cenv e = typ \/ is_bytestring_type typ \/
     has_length_word typ /\ is_empty_value_expr e) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  cheat
QED




(* A declared type takes memory: it is assignable, so it takes a storage slot
   (assignable_type_slot_size_pos). *)
Theorem annassign_memory_bytes_pos[local]:
  !cenv cx env es ret_ty id typ e env'.
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' ==>
    0 < type_memory_bytes cenv typ
Proof
  cheat
QED

(* RESIDUAL (#637 declarations): a declaration of a type that is not a
   word, which body_annassign_memory leaves: a value that widens to a type
   other than a bytestring (type_widens_to: a DynArray of a smaller bound,
   elementwise) has no statement lemma. *)
Theorem body_annassign_other:
  !cx id typ e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res
   es'.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_ok cx e) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AnnAssign id typ e) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    ~is_word_type typ /\
    ~(expr_type e = typ \/ is_bytestring_type typ \/
      has_length_word typ /\ is_empty_value_expr e) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  cheat
QED

(* RESIDUAL (#767): a memory-backed declaration of an internal call whose
   return type widens to the call's type other than as a bytestring
   (type_widens_to: a DynArray of a smaller bound, a tuple elementwise). *)
Theorem body_annassign_widened_aggregate_call:
  !cx id typ e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res
   es'.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_ok cx e) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AnnAssign id typ e) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    ~is_word_type typ /\ 0 < type_memory_bytes cenv typ /\
    ~(lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  cheat
QED

Theorem body_annassign_case:
  !cx id typ e.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_ok cx e) ==>
    body_stmt_ok cx (AnnAssign id typ e)
Proof
  cheat
QED

(* ===== For ===== *)

(* The scope of a loop's iteration: the loop variable, declared in the
   compile env and added to the type environment. *)
Theorem for_pushed_state_well_typed[local]:
  !st tyv v id.
    state_well_typed st /\ value_has_type tyv v /\
    well_formed_type_value tyv ==>
    state_well_typed
      (st with scopes updated_by
         CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                                popped := []|>)))
Proof
  cheat
QED

Theorem for_pushed_popped_keys[local]:
  !scs id tyv v.
    popped_keys_indexed scs ==>
    popped_keys_indexed
      (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                        popped := []|>) :: scs)
Proof
  cheat
QED

Theorem scopes_CONS_updated[local]:
  !es x. es with scopes := x :: es.scopes = es with scopes updated_by CONS x
Proof
  cheat
QED

Theorem expr_sim_inv_for_scope:
  !cenv cx env es id fty tyv v st c st1.
    expr_sim_inv cenv cx env es /\ id NOTIN FDOM env.var_types /\
    evaluate_type (get_tenv cx) fty = SOME tyv /\ value_has_type tyv v /\
    declare_local cenv id fty st = (c, st1) /\ cenv.ce_alloca_locals ==>
    expr_sim_inv c cx (extend_local env id fty F)
      (es with scopes :=
         (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                           popped := []|>)) :: es.scopes)
Proof
  cheat
QED

(* After an iteration that goes on (a normal end or a continue), with the
   loop variable's scope popped, expr_sim_inv holds again at the loop's
   compile and type environments: the type soundness of the body, and
   vyperTypeEvalSoundness's for_body_env_consistent_after_pop. *)
Theorem expr_sim_inv_for_pop:
  !cenv cx env es id fty tyv v ret_ty body env_b r2 es2 sc rest tops
   bindings.
    expr_sim_inv cenv cx env es /\ id NOTIN FDOM env.var_types /\
    evaluate_type (get_tenv cx) fty = SOME tyv /\ value_has_type tyv v /\
    type_stmts (extend_local env id fty F) ret_ty body = SOME env_b /\
    call_evaluation_safe cx (int_calls_stmts body) /\
    eval_stmts cx body
      (es with scopes :=
         (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                           popped := []|>)) :: es.scopes) = (r2, es2) /\
    (r2 = INL () \/ r2 = INR ContinueException) /\
    es2.scopes = sc :: rest /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    supported_stmts tops bindings body ==>
    expr_sim_inv cenv cx env (es2 with scopes := rest)
Proof
  cheat
QED

Theorem compile_stmts_grows[local]:
  !c lc ty stmts sa sb.
    compile_stmts c lc ty stmts sa = ((), sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  cheat
QED

Theorem is_int_type_word[local]:
  !t. is_int_type t ==> is_word_type t
Proof
  cheat
QED

(* A range of literals: stmtSimFor's compile_for_range_lit_frag, whose
   invariant is expr_sim_inv at the loop's environments.  The literals'
   type bounds the rounds below 2 ** 256. *)
Theorem body_for_range_lit[local]:
  !cx id typ a1 n1 a2 n2 n stmts tops bindings ctx func cenv env env'
   ret_ty lctx RetQ es res es'.
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\
       eval_iterator cx (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
         s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_ok cx tyv id stmts vs) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings
      (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) n
         stmts) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty
      (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) n
         stmts) = SOME env' /\
    stmt_exprs_ok cenv
      (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) n
         stmts) /\
    call_evaluation_safe cx
      (int_calls_stmt
         (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) n
            stmts)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) n
            stmts))
      (eval_stmt cx (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) n stmts)) es
Proof
  cheat
QED

(* The source checker validates computed bounds in the loop's integer type. *)
Theorem body_range_typing[local]:
  !(env, ret_ty, id, typ, e1, e2, bound, stmts) env'.
    type_stmt env ret_ty (For id typ (Range e1 e2) bound stmts) = SOME env' /\
    ~(?a1 n1 a2 n2. e1 = Literal a1 (IntL n1) /\
                       e2 = Literal a2 (IntL n2)) ==>
    id NOTIN FDOM env.var_types /\ is_int_type typ /\
    well_typed_expr env e1 /\ well_typed_expr env e2 /\
    expr_type e1 = typ /\ expr_type e2 = typ /\
    well_formed_type env.type_defs typ /\
    0 < bound /\ well_typed_literal typ (IntL (&bound)) /\
    ?env_b. type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b
Proof
  cheat
QED

(* A successful typed integer endpoint preserves the loop invariant. *)
Theorem body_range_endpoint_read[local]:
  !(cenv, cx, env, e, typ, tyv) es tv es'.
    expr_body_pre cenv cx env e es /\ is_int_type typ /\
    expr_type e = typ /\ evaluate_type (get_tenv cx) typ = SOME tyv /\
    (do raw <- eval_expr cx e; read_result cx raw od) es = (INL tv, es') ==>
    expr_sim_inv cenv cx env es' /\
    ?n. tv = IntV n /\ value_has_type tyv (IntV n)
Proof
  cheat
QED

(* A successful nonempty checked iterator activates the source body IH. *)
Theorem body_for_range_active[local]:
  !(cx, id, typ, e1, e2, bound, body, tyv) lo hi es0 es1 es2.
    (!tenv s'' tv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tv,t) /\
       eval_iterator cx (Range e1 e2) s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic bound) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==> body_for_ok cx tv id body vs) /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\
    (do raw <- eval_expr cx e1; read_result cx raw od) es0 = (INL (IntV lo), es1) /\
    (do raw <- eval_expr cx e2; read_result cx raw od) es1 = (INL (IntV hi), es2) /\
    lo <= hi /\ Num (hi - lo) <= bound /\ 0 < Num (hi - lo) ==>
    body_stmts_ok cx body
Proof
  cheat
QED

(* The enclosing For carries both traversal and allocation safety for its body. *)
Theorem body_for_exprs_ok[local]:
  !cenv id typ it n body.
    stmt_exprs_ok cenv (For id typ it n body) ==>
    EVERY (stmt_exprs_ok cenv) body
Proof
  cheat
QED

(* Normalize only a paired outer binder at theorem application boundaries. *)
fun range_tuple_forall th =
  SIMP_RULE std_ss [pairTheory.FORALL_PROD]
    (CONV_RULE (RAND_CONV (REWR_CONV (GSYM ETA_AX))) th);

(* Integer ranges use checked endpoints unless the frontend supplies two
   source integer literals. Array iteration remains a separate residual.
   body_for_ok supplies a body judgment only for a successfully checked,
   nonempty iterator; rejecting and empty ranges need no body judgment. *)
Theorem body_for_range:
  !cx id typ it n body tops bindings ctx func cenv env env' ret_ty lctx RetQ
   es res es'.
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_ok cx it) /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings (For id typ it n body) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (For id typ it n body) = SOME env' /\
    stmt_exprs_ok cenv (For id typ it n body) /\
    call_evaluation_safe cx (int_calls_stmt (For id typ it n body)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    (?e1 e2. it = Range e1 e2) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ it n body))
      (eval_stmt cx (For id typ it n body)) es
Proof
  cheat
QED





(* A loop over an array (#637 for, #559): the iterable is a variable
   holding a fixed array of the loop variable's type (supported_iterator),
   which the body does not write (type_stmt's iterator_unmodified).  The
   lowering reads each element from the array's place at each iteration,
   the source iterates over the array's value read once before the loop;
   the two agree as the body leaves the array's value unchanged.
   Why it holds: a source Name is a memory place, and expr_sim_inv binds it
   to a PtrVar whose bytes hold the value (val_in_memory); the body has no
   internal calls and iterator_unmodified (via stmt_writes_ok) rejects
   every statement that could write it, so the variable's value, and with
   the state relation the bytes the lowering reads, are those of the
   snapshot at every iteration.  The element at index j of a fixed array
   lies at j * type_memory_bytes of the element (val_in_memory_sarray,
   elems_in_memory_EL); the element and loop types are equal, so the copy
   is MLOAD/MSTORE for a word and compile_store_memory at one type
   otherwise (compile_store_memory_run).  m < 2 ** 256, since evaluate_type
   bounds the array's size. *)
Theorem array_for_source_ready[local]:
  (!tenv s tyv t s3 vs t3 s4 x t4.
    tenv = get_tenv cx /\
    lift_option_type (evaluate_type tenv typ) "For evaluate_type" s = (INL tyv,t) /\
    eval_iterator cx (Array e) s3 = (INL vs,t3) /\
    check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s4 = (INL x,t4)
    ==> body_for_ok cx tyv id stmts vs) /\
  supported_stmt tops bindings (For id typ (Array e) n stmts) /\
  expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
  type_stmt env ret_ty (For id typ (Array e) n stmts) = SOME env' /\
  eval_stmt cx (For id typ (Array e) n stmts) es = (res,es') ==>
  ?name env_b entry tv ptr sz al vs.
    e = Name (ArrayT typ (Fixed n)) name /\ env' = env /\
    well_typed_expr env (Name (ArrayT typ (Fixed n)) name) /\
    id NOTIN FDOM env.var_types /\
    iterator_unmodified (Array (Name (ArrayT typ (Fixed n)) name)) stmts /\
    type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
    supported_stmts tops bindings stmts /\
    ~supported_stmts_expr_exists expr_internal_call_root stmts /\
    lookup_scopes name es.scopes = SOME entry /\
    evaluate_type (get_tenv cx) typ = SOME tv /\
    entry.type = ArrayTV tv (Fixed n) /\
    value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var ptr) sz) /\
    cenv.ce_var_type name = SOME (ArrayT typ (Fixed n)) /\
    0 < n /\ n < dimword (:256) /\ entry.value = ArrayV (SArrayV al) /\
    vs = array_elements (ArrayTV tv (Fixed n)) (SArrayV al) /\ LENGTH vs = n /\
    eval_for cx tv id stmts vs es = (res,es') /\ body_stmts_ok cx stmts /\
    FLOOKUP cenv.ce_vars id = NONE /\ lookup_scopes id es.scopes = NONE
Proof
  cheat
QED

Theorem array_for_layout_ready[local]:
  expr_sim_inv cenv cx env es /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  stmt_exprs_ok cenv (For id typ (Array e) n stmts) ==>
  type_memory_bytes cenv typ = type_memory_size tv /\
  type_memory_bytes cenv typ + 64 < dimword (:256)
Proof
  cheat
QED

Theorem array_body_fragment_callback[local]:
  !cx stmts tops ctx cenv bindings env ei id typ tv v env_b ret_ty
   func RetQ st0 bc sd ex inc r ef.
    body_stmts_ok cx stmts /\ body_inv tops ctx cenv cx /\
    supported_stmts tops bindings stmts /\ expr_sim_inv cenv cx env ei /\
    ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
    id NOTIN FDOM env.var_types /\
    evaluate_type (get_tenv cx) typ = SOME tv /\ value_has_type tv v /\
    type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
    EVERY (stmt_exprs_ok cenv) stmts /\
    type_memory_bytes cenv typ < 2 ** 64 /\
    call_evaluation_safe cx (int_calls_stmts stmts) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    declare_local cenv id typ st0 = (bc,sd) /\
    eval_stmts cx stmts
      (ei with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := v;
                          popped := []|>)) :: ei.scopes) = (r,ef) ==>
    stmt_frag ctx func cx (InLoop ex inc) RetQ bc
      (stmts_env bc (InLoop ex inc) ret_ty stmts)
      (eval_stmts cx stmts)
      (ei with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := v;
                          popped := []|>)) :: ei.scopes)
Proof
  cheat
QED

Theorem array_body_scope_shape[local]:
  !cx stmts ei id tv v r ef.
    lookup_scopes id ei.scopes = NONE /\
    eval_stmts cx stmts
      (ei with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := v;
                          popped := []|>)) :: ei.scopes) = (r,ef) ==>
    ?sc rest. ef.scopes = sc::rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE)
Proof
  cheat
QED

Theorem array_body_result_ok[local]:
  !cx stmts cenv env ei id typ tv v ret_ty env_b r ef.
    expr_sim_inv cenv cx env ei /\ id NOTIN FDOM env.var_types /\
    evaluate_type (get_tenv cx) typ = SOME tv /\ value_has_type tv v /\
    type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
    call_evaluation_safe cx (int_calls_stmts stmts) /\
    eval_stmts cx stmts
      (ei with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := v;
                          popped := []|>)) :: ei.scopes) = (r,ef) ==>
    !ex inc. stmt_res_ok (InLoop ex inc) r
Proof
  cheat
QED

Theorem array_body_direct_snapshot[local]:
  !tops bindings stmts env id typ name elem bound ret_ty env_b aty
   cx ei tv v r ef sc rest entry.
    supported_stmts tops bindings stmts /\
    FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\ name <> id /\
    type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
    iterator_unmodified (Array (Name aty name)) stmts /\
    ~supported_stmts_expr_exists expr_internal_call_root stmts /\
    lookup_scopes name ei.scopes = SOME entry /\
    eval_stmts cx stmts
      (ei with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := v;
                          popped := []|>)) :: ei.scopes) = (r,ef) /\
    ef.scopes = sc::rest ==>
    lookup_scopes name rest = SOME entry
Proof
  cheat
QED

Theorem array_body_scope_callback[local]:
  !cenv cx env ei id typ tv v ret_ty stmts env_b r ef tops bindings
   name elem bound aty entry.
    expr_sim_inv cenv cx env ei /\ id NOTIN FDOM env.var_types /\
    evaluate_type (get_tenv cx) typ = SOME tv /\ value_has_type tv v /\
    type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
    call_evaluation_safe cx (int_calls_stmts stmts) /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    supported_stmts tops bindings stmts /\
    FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\ name <> id /\
    iterator_unmodified (Array (Name aty name)) stmts /\
    ~supported_stmts_expr_exists expr_internal_call_root stmts /\
    lookup_scopes name ei.scopes = SOME entry /\
    lookup_scopes id ei.scopes = NONE /\
    eval_stmts cx stmts
      (ei with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := v;
                          popped := []|>)) :: ei.scopes) = (r,ef) ==>
    (!ex inc. stmt_res_ok (InLoop ex inc) r) /\
    ?sc rest. ef.scopes = sc::rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        expr_sim_inv cenv cx env (ef with scopes := rest) /\
        lookup_scopes name rest = SOME entry /\ lookup_scopes id rest = NONE)
Proof
  cheat
QED

Theorem body_for_array:
  !cx id typ it n body tops bindings ctx func cenv env env' ret_ty lctx RetQ
   es res es'.
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_ok cx it) /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings (For id typ it n body) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (For id typ it n body) = SOME env' /\
    stmt_exprs_ok cenv (For id typ it n body) /\
    call_evaluation_safe cx (int_calls_stmt (For id typ it n body)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    (?e. it = Array e) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ it n body))
      (eval_stmt cx (For id typ it n body)) es
Proof
  cheat
QED

Theorem body_for_other:
  !cx id typ it n body tops bindings ctx func cenv env env' ret_ty lctx RetQ
   es res es'.
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_ok cx it) /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings (For id typ it n body) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (For id typ it n body) = SOME env' /\
    stmt_exprs_ok cenv (For id typ it n body) /\
    call_evaluation_safe cx (int_calls_stmt (For id typ it n body)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    ~(?a1 n1 a2 n2. it = Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ it n body))
      (eval_stmt cx (For id typ it n body)) es
Proof
  cheat
QED

Theorem body_for_case:
  !cx id typ it n body.
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_ok cx it) ==>
    body_stmt_ok cx (For id typ it n body)
Proof
  cheat
QED
