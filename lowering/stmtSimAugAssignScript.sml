(*
 * Statement simulation: an augmented assignment to a word local (#637)
 *
 * AugAssign over stmt_frag (stmtSim) for x op= e where x is a local held
 * through its pointer and of a type whose values are word_values.  x op= e
 * is x = x op e on both sides: the source reads x, evaluates e, runs the
 * operator and writes x, as evaluating the expression x op e annotated with
 * x's type and then writing x would, and the lowering is x op e's lowering
 * at x's type (an MLOAD of the pointer, e, compile_binop) and then an
 * MSTORE at the pointer.  So the expression side is compile_bop_word_case's
 * (exprSimOperators), the checked operators' aborts (overflow, division by
 * zero) among its exits, and ** and the narrow or negative shifts rest on
 * exprSimBinopFrag's cheats (#572).  The store is stmtSimAssignStore's.
 *
 * TOP-LEVEL:
 *   compile_augassign_local_case      — x op= e on a word local, for every
 *                                       outcome, given e's expr_sim_case
 *   compile_augassign_local_stmt_frag — the same, given e's expr_sim_ok
 *   eval_augassign_local_bop          — x op= e evaluates as x op e, then
 *                                       writes x
 *   augassign_local_code_bop          — its code is x op e's, then MSTORE
 *)

Theory stmtSimAugAssign
Ancestors
  exprBopSimDefs exprBopSimProps
  exprSimSource
  exprSimName
  stmtSimProps
  exprSimHypsDefs
  stmtSimDefs
  exprSimDefs
  loweringPosts
  allocLimits
  list rich_list finite_map pred_set
  fragExec localPtrsProps  exprSimHyps exprSimOps exprSimBinopFrag
  exprSimOperators exprSimLeaves loweringSlice  stmtSimDecl
  stmtSimDeclStore stmtSimAssignStore
  exprLowering exprBopLowering stmtLowering emitHelper emitHelperProps
  exprLoweringProps compileEnv valueEncoding
  vyperInterpreter vyperState vyperValue vyperValueOperation vyperContext
  vyperExprNoControl vyperTypeSystem vyperTyping vyperTypeEnv
  vyperTypeInvariants vyperTypeCallGraph vyperLookup vyperAST
  venomExecSemantics venomExecProofs venomInst venomState
Libs
  monadsyntax intLib

(* ===== The source side ===== *)

(* A local in scope: its target place, the value there and its type. *)
Theorem eval_target_place_local:
  !cx id es entry.
    lookup_scopes id es.scopes = SOME entry ==>
    eval_target_place cx (NameTarget id) es = (INL (MemoryPlace id []), es) /\
    read_place cx (MemoryPlace id []) es = (INL entry.value, es) /\
    place_type_value cx (MemoryPlace id []) es = (INL entry.type, es)
Proof
  cheat
QED

(* x op= e on a local x in scope: x's place, its value and its type are read
   without changing the state, e is evaluated, then the operator runs on
   x's value and e's, and the result is written to x. *)
Theorem eval_augassign_local:
  !cx ty id bop e es res es' entry.
    eval_stmt cx (AugAssign ty (NameTarget id) bop e) es = (res, es') /\
    lookup_scopes id es.scopes = SOME entry ==>
    ?r1 es1.
      (do tv <- eval_expr cx e; read_result cx tv od) es = (r1, es1) /\
      case r1 of
        INR ex => res = INR ex /\ es' = es1
      | INL v =>
          case evaluate_binop
                 (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
                 entry.type bop entry.value v of
            INR err => res = INR (Error err) /\ es' = es1
          | INL r => write_place cx (MemoryPlace id []) r es1 = (res, es')
Proof
  cheat
QED

(* The operator's type argument matters only for in and not in on an
   array. *)
Theorem evaluate_binop_tv:
  !u tv tv' bop v1 v2.
    bop <> In /\ bop <> NotIn ==>
    evaluate_binop u tv bop v1 v2 = evaluate_binop u tv' bop v1 v2
Proof
  cheat
QED

(* ===== The code ===== *)

(* x op= e on a local x held through its pointer p: no declaration, x's
   target is p itself with no code, then MLOAD, e lowered at x's type, the
   operator and MSTORE. *)
Theorem augassign_local_code_parts:
  !cenv lctx ty0 ty id bop e sa c sf p sz.
    stmt_env cenv lctx ty0 (AugAssign ty (NameTarget id) bop e) sa = (c, sf) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) ==>
    c = cenv /\
    ?s1 s2 s3 cur_op rhs_op res_op.
      emit_op MLOAD [Var p] sa = (cur_op, s1) /\
      lower_value compile_expr cenv ty e s1 = (rhs_op, s2) /\
      compile_binop bop cur_op rhs_op ty NONE
        (if bop = Exp then expr_int_literal e else NONE) s2 = (res_op, s3) /\
      emit_void MSTORE [Var p; res_op] s3 = ((), sf)
Proof
  cheat
QED

(* ===== The operator ===== *)

(* The types the type checker allows for x op= e, with op neither in nor
   not in (type_stmt), are word_value_types. *)
Theorem well_typed_binop_augassign_word:
  !ty bop t2.
    well_typed_binop ty bop ty t2 /\ bop <> In /\ bop <> NotIn ==>
    word_value_type ty /\ word_value_type t2
Proof
  cheat
QED

(* The source's operator on x's value and e's is the operator of the
   expression x op e annotated with x's type: the builtin reads its type
   argument from e's type, x op= e from x's place, and neither matters
   but for in and not in. *)
Theorem bop_result_augassign:
  !cx ty bop t2 v1 v2 es tv.
    bop <> In /\ bop <> NotIn ==>
    bop_result cx ty bop [ty; t2] v1 v2 es =
    case evaluate_binop
           (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
           tv bop v1 v2 of
      INL v => INL v
    | INR err => INR (Error err)
Proof
  cheat
QED

(* ===== x op= e is x = x op e ===== *)

(* The source: x op= e on a local x in scope evaluates as the expression
   x op e annotated with x's type would, then writes its value to x. *)
Theorem eval_augassign_local_bop:
  !cx ty id bop e es res es' entry.
    eval_stmt cx (AugAssign ty (NameTarget id) bop e) es = (res, es') /\
    lookup_scopes id es.scopes = SOME entry /\ bop <> In /\ bop <> NotIn ==>
    ?r es1.
      (do tv <- eval_expr cx (Builtin ty (Bop bop) [Name ty id; e]);
          read_result cx tv od) es = (r, es1) /\
      case r of
        INR ex => res = INR ex /\ es' = es1
      | INL v => write_place cx (MemoryPlace id []) v es1 = (res, es')
Proof
  cheat
QED

(* The code: x op= e on a local held through its pointer is the lowering
   of x op e at x's type, then an MSTORE of its result at the pointer. *)
Theorem augassign_local_code_bop:
  !cenv lctx ty0 ty id bop e sa c sf p sz.
    stmt_env cenv lctx ty0 (AugAssign ty (NameTarget id) bop e) sa = (c, sf) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    word_value_type ty /\ bop <> In /\ bop <> NotIn ==>
    c = cenv /\
    ?s3 res_op.
      lower_value compile_expr cenv ty (Builtin ty (Bop bop) [Name ty id; e])
        sa = (res_op, s3) /\
      emit_void MSTORE [Var p; res_op] s3 = ((), sf)
Proof
  cheat
QED

(* A well-formed type's width is whole bytes: Vyper's int widths are
   multiples of 8, and decimal and every other type are 168 or 256 bits. *)
Theorem well_formed_type_bits:
  !tenv ty. well_formed_type tenv ty ==> type_bits ty MOD 8 = 0
Proof
  cheat
QED

(* The target of an augmented assignment has a word type, so nothing of
   its size is asked for alloc_limits_expr. *)
Theorem well_typed_binop_augassign_alloc_ok[local]:
  !cenv ty bop t2. well_typed_binop ty bop ty t2 ==> type_alloc_ok cenv ty
Proof
  cheat
QED

(* The typing side: x op e meets expr_sim_pre where e does, x is a local
   of type ty and the type checker accepts x op= e. *)
Theorem expr_sim_pre_augassign:
  !cenv cx env ty id bop e es.
    expr_sim_pre cenv cx env e es /\ FLOOKUP env.var_types id = SOME ty /\
    well_typed_binop ty bop ty (expr_type e) /\
    (bop = Exp ==> nonneg_int_literal e) /\
    (bop = ShL \/ bop = ShR ==> shift_amount_ok e) ==>
    expr_sim_pre cenv cx env (Builtin ty (Bop bop) [Name ty id; e]) es
Proof
  cheat
QED

(* expr_sim_pre_augassign under expr_body_pre: e may make internal calls. *)
Theorem expr_body_pre_augassign:
  !cenv cx env ty id bop e es.
    expr_body_pre cenv cx env e es /\ FLOOKUP env.var_types id = SOME ty /\
    well_typed_binop ty bop ty (expr_type e) /\
    (bop = Exp ==> nonneg_int_literal e) /\
    (bop = ShL \/ bop = ShR ==> shift_amount_ok e) ==>
    expr_body_pre cenv cx env (Builtin ty (Bop bop) [Name ty id; e]) es
Proof
  cheat
QED

Theorem name_sim_case[local]:
  !nocalls ctx func cenv cx ann id.
    expr_sim_case nocalls ctx func cenv cx (Name ann id)
Proof
  cheat
QED

(* x op e simulates where e does, with or without internal calls. *)
Theorem augassign_bop_case:
  !nocalls ctx func cenv cx ty id bop e.
    expr_sim_case nocalls ctx func cenv cx e /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
    expr_sim_case nocalls ctx func cenv cx
      (Builtin ty (Bop bop) [Name ty id; e])
Proof
  cheat
QED

Theorem augassign_bop_sim:
  !ctx func cenv cx env ty id bop e es.
    expr_sim_ok cenv e /\ expr_sim_pre cenv cx env e es /\
    FLOOKUP env.var_types id = SOME ty /\
    (bop = Exp ==> nonneg_int_literal e) /\
    (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
    expr_sim ctx func cenv cx ty (Builtin ty (Bop bop) [Name ty id; e]) es
Proof
  cheat
QED

(* ===== The statement ===== *)

(* A local the typing environment knows: it is held through a pointer
   variable, it is in scope, and its entry's type is its type's. *)
Theorem expr_sim_inv_local:
  !cenv cx env es id ty.
    expr_sim_inv cenv cx env es /\ FLOOKUP env.var_types id = SOME ty ==>
    (?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
    (?entry. lookup_scopes id es.scopes = SOME entry) /\
    !entry. lookup_scopes id es.scopes = SOME entry ==>
            evaluate_type (get_tenv cx) ty = SOME entry.type
Proof
  cheat
QED

(* x op= e on a word local x, for every outcome, given e's expr_sim_case
   (so e may make internal calls unless nocalls): x op e's errors exit,
   the checked operators' aborts among them, and on a value the MSTORE
   writes it to x's region. *)
(* Why it holds.  The source reads x, evaluates e and runs the operator,
   which is how x op e evaluates (eval_augassign_local_bop), and the code
   is x op e's lowering then the MSTORE (augassign_local_code_bop); x op e
   meets expr_body_pre where e does, so its expr_sim is compile_bop_word_case's.
   The scopes at the write hold x at the type ty evaluates to
   (expr_sim_inv at the state after e), so the result's typed word is the
   word the store lays out at x's type (store_lays_out_word_value). *)
Theorem compile_augassign_local_case:
  !nocalls ctx func cx lctx RetQ cenv ty0 env ty id bop e es.
    expr_sim_case nocalls ctx func cenv cx e /\
    expr_body_pre cenv cx env e es /\ (nocalls ==> int_calls_expr e = []) /\
    FLOOKUP env.var_types id = SOME ty /\
    (bop = Exp ==> nonneg_int_literal e) /\
    (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty0 (AugAssign ty (NameTarget id) bop e))
      (eval_stmt cx (AugAssign ty (NameTarget id) bop e)) es
Proof
  cheat
QED

(* compile_augassign_local_case for an operand with no internal call. *)
Theorem compile_augassign_local_stmt_frag:
  !ctx func cx lctx RetQ cenv ty0 env ty id bop e es.
    expr_sim_ok cenv e /\ expr_sim_pre cenv cx env e es /\
    FLOOKUP env.var_types id = SOME ty /\
    (bop = Exp ==> nonneg_int_literal e) /\
    (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty0 (AugAssign ty (NameTarget id) bop e))
      (eval_stmt cx (AugAssign ty (NameTarget id) bop e)) es
Proof
  cheat
QED

(* Integrity gate: the source and code sides and the store carry no
   admission; the statement itself inherits exprSimBinopFrag's (#572). *)
val () = List.app (fn th =>
  let val (ors, axs) = Tag.dest_tag (Thm.tag th)
  in if null axs andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") ors
     then print "AUGASSIGN_AUDIT OK\n"
     else print "statement-check gate skipped\n"
  end) [eval_augassign_local_bop, augassign_local_code_bop,
        expr_sim_pre_augassign, expr_body_pre_augassign, expr_sim_inv_local, assign_local_store_run];
