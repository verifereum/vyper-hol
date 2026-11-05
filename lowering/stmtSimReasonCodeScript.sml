(*
 * Statement simulation: Raise and Assert with a reason read from an
 * immutable (#637)
 *
 * A reason that compile_expr hands out as a pointer into code (an
 * immutable string, reason_code_vv) reaches the Error(string) encoder of
 * compile_revert_with_reason as a LocatedValue, which the encoder's
 * unwrap_value copies into a buffer of its own (compile_ensure_in_memory:
 * an ALLOCA, then per word a DLOAD from the data section and an MSTORE,
 * compile_imm_copy_to_memory).  The function bodies are runtime code
 * (body_inv), so the copy reads with DLOAD, which is defined at every
 * offset.  As for stmtSimReasonStorage, the REVERT's data is not compared,
 * so only definedness matters.
 *
 * TOP-LEVEL:
 *   compile_raise_code_reason_frag   — raise with such a reason
 *   compile_assert_code_reason_frag  — assert with such a reason
 *
 * Helper: code_copy_frag,
 *   code_alloc_frag, unwrap_code_reason_defined_frag,
 *   unwrap_code_reason_var, code_reason_tail_known,
 *   compile_revert_code_reason_frag, reason_code_expr_revert_frag,
 *   reason_code_expr_revert_forced_frag
 *)

Theory stmtSimReasonCode
Ancestors
  exprSimUnwrapProps
  stmtSimDefs
  exprSimDefs
  loweringPosts
  list rich_list finite_map
  fragExec varsExt freshWrites  exprSimUnwrap exprSimCopy exprSimStorageCopy
  exprOperandVar  stmtSimIf stmtSimReason stmtSimReasonExpr
  stmtSimReasonStorage exprReasonOperand immutableCopyExecution
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  context compileEnv moduleLoweringProps
  vyperInterpreter vyperState venomExecSemantics venomInst venomState
Libs
  monadsyntax

(* ===== The copy out of code ===== *)

(* The copy runs and keeps every variable bound before it. *)
Theorem code_copy_frag[local]:
  !ctx imm src dst n sa sb sbase a b R.
    compile_imm_copy_to_memory F imm src dst n 0 sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src sbase = SOME a /\ eval_operand dst sbase = SOME b ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. !x w. not_fresh_at sa x /\ lookup_var x sbase = SOME w ==>
                 lookup_var x s = SOME w) R
Proof
  cheat
QED

Theorem code_alloc_frag[local]:
  !ctx n sa buf sb sbase R.
    compile_alloc_buffer n sa = (buf,sb) ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. (?w. eval_operand buf.buf_operand s = SOME w) /\
           (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
           s.vs_labels = sbase.vs_labels) R
Proof
  cheat
QED

(* unwrap_value of a pointer into code, at runtime: a buffer, then the
   copy.  The buffer's operand ends defined and every variable bound
   before keeps its value. *)
Theorem unwrap_code_reason_defined_frag:
  !ctx cenv ty p sa op sb sbase a R.
    ~cenv.ce_is_ctor /\ reason_code_vv (LocatedValue ty p) /\
    unwrap_value cenv (LocatedValue ty p) sa = (op,sb) /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
    eval_operand p.ptr_operand sbase = SOME a ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. (?w. eval_operand op s = SOME w) /\
           (!x w. not_fresh_at sa x /\ lookup_var x sbase = SOME w ==>
                  lookup_var x s = SOME w)) R
Proof
  cheat
QED

(* Constructor copy uses the reserved immutable base supplied by the frame. *)
Theorem unwrap_ctor_code_reason_defined_frag:
  !ctx cenv ty p sa op sb sbase a R.
    cenv.ce_is_ctor /\ immutable_base_zero cenv sbase /\
    (!base x. cenv.ce_imm_alloca = SOME base /\ base = Var x ==>
       not_fresh_at sa x) /\
    reason_code_vv (LocatedValue ty p) /\
    unwrap_value cenv (LocatedValue ty p) sa = (op,sb) /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
    eval_operand p.ptr_operand sbase = SOME a ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. (?w. eval_operand op s = SOME w) /\
           (!x w. not_fresh_at sa x /\ lookup_var x sbase = SOME w ==>
                  lookup_var x s = SOME w)) R
Proof
  cheat
QED

Theorem unwrap_code_reason_var:
  !cenv ty p sa op sb.
    reason_code_vv (LocatedValue ty p) /\
    unwrap_value cenv (LocatedValue ty p) sa = (op,sb) ==>
    ?x. op = Var x
Proof
  cheat
QED

(* ===== The encoder ===== *)

Theorem code_reason_tail_known[local]:
  !hs sm t u x w.
    reason_known hs t /\ EVERY (not_fresh_at sm) hs /\
    (!y v. not_fresh_at sm y /\ lookup_var y t = SOME v ==>
           lookup_var y u = SOME v) /\
    eval_operand (Var x) u = SOME w ==>
    reason_known (x::hs) u
Proof
  cheat
QED

Theorem compile_revert_code_reason_frag:
  !ctx cenv ty p mt ms sa sb sbase a R.
    ~cenv.ce_is_ctor /\ reason_code_vv (LocatedValue ty p) /\
    compile_revert_with_reason cenv (LocatedValue ty p) mt ms sa = ((),sb) /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
    eval_operand p.ptr_operand sbase = SOME a /\
    (!t. R (Abort Revert_abort t)) ==>
    frag_exec ctx sa sb (\s. s = sbase) (\s. F) R
Proof
  cheat
QED

Theorem compile_revert_ctor_code_reason_frag:
  !ctx cenv ty p mt ms sa sb sbase a R.
    cenv.ce_is_ctor /\ immutable_base_zero cenv sbase /\
    (!base x. cenv.ce_imm_alloca = SOME base /\ base = Var x ==>
       not_fresh_at sa x) /\
    reason_code_vv (LocatedValue ty p) /\
    compile_revert_with_reason cenv (LocatedValue ty p) mt ms sa = ((),sb) /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
    eval_operand p.ptr_operand sbase = SOME a /\
    (!t. R (Abort Revert_abort t)) ==>
    frag_exec ctx sa sb (\s. s = sbase) (\s. F) R
Proof
  cheat
QED

Theorem reason_code_expr_revert_frag[local]:
  !ctx func cenv cx r es res1 es1 sa vv sm rty msz sb s0 R.
    ~cenv.ce_is_ctor /\
    compile_expr cenv (expr_type r) r sa = (vv, sm) /\
    compile_revert_with_reason cenv vv rty msz sm = ((), sb) /\
    reason_code_vv vv /\
    expr_vv_sim ctx func cenv cx (expr_type r) r es /\
    eval_expr cx r es = (res1, es1) /\ expr_vv_res_ok res1 /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    (!rr. expr_exit res1 rr ==> R rr) /\ (!t. R (Abort Revert_abort t)) ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. F) R
Proof
  cheat
QED

Theorem reason_ctor_code_expr_revert_frag[local]:
  !ctx func cenv cx r es res1 es1 sa vv sm rty msz sb s0 R.
    cenv.ce_is_ctor /\
    compile_expr cenv (expr_type r) r sa = (vv, sm) /\
    compile_revert_with_reason cenv vv rty msz sm = ((), sb) /\
    reason_code_vv vv /\
    expr_vv_sim ctx func cenv cx (expr_type r) r es /\
    eval_expr cx r es = (res1, es1) /\ expr_vv_res_ok res1 /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    (!rr. expr_exit res1 rr ==> R rr) /\ (!t. R (Abort Revert_abort t)) ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. F) R
Proof
  cheat
QED

Theorem reason_code_expr_revert_forced_frag[local]:
  !ctx func cenv cx r es res1 es1 sa vv sm rty msz sb s0 R.
    ~cenv.ce_is_ctor /\
    compile_expr cenv (expr_type r) r sa = (vv, sm) /\
    compile_revert_with_reason cenv vv rty msz sm = ((), sb) /\
    reason_code_vv vv /\
    expr_vv_sim ctx func cenv cx (expr_type r) r es /\
    (do raw <- eval_expr cx r; read_result cx raw od) es = (res1, es1) /\
    expr_res_ok res1 /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    (!rr. expr_exit res1 rr ==> R rr) /\ (!t. R (Abort Revert_abort t)) ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. F) R
Proof
  cheat
QED

Theorem reason_code_expr_revert_shared_frag[local]:
  !ctx func cenv cx r es res1 es1 sa vv sm rty msz sb s0 R.
    compile_expr cenv (expr_type r) r sa = (vv, sm) /\
    compile_revert_with_reason cenv vv rty msz sm = ((), sb) /\
    reason_code_vv vv /\
    expr_vv_sim ctx func cenv cx (expr_type r) r es /\
    eval_expr cx r es = (res1, es1) /\ expr_vv_res_ok res1 /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    (!rr. expr_exit res1 rr ==> R rr) /\ (!t. R (Abort Revert_abort t)) ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. F) R
Proof
  cheat
QED

Theorem reason_code_expr_revert_shared_forced_frag[local]:
  !ctx func cenv cx r es res1 es1 sa vv sm rty msz sb s0 R.
    compile_expr cenv (expr_type r) r sa = (vv, sm) /\
    compile_revert_with_reason cenv vv rty msz sm = ((), sb) /\
    reason_code_vv vv /\
    expr_vv_sim ctx func cenv cx (expr_type r) r es /\
    (do raw <- eval_expr cx r; read_result cx raw od) es = (res1, es1) /\
    expr_res_ok res1 /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    (!rr. expr_exit res1 rr ==> R rr) /\ (!t. R (Abort Revert_abort t)) ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. F) R
Proof
  cheat
QED

(* ===== The statements ===== *)

(* raise r, at runtime, for a reason r that is not a string literal and
   whose value compile_expr hands out as a pointer into code: r's
   fragment, whose errors exit, then the Error(string) encoder, whose
   unwrap_value copies the value into memory, and its REVERT. *)
Theorem compile_raise_code_reason_shared_frag:
  !ctx func cx lctx RetQ cenv ty r es res es'.
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_vv_sim ctx func cenv cx (expr_type r) r es /\
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_code_vv vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Raise (RaiseReason r)))
      (eval_stmt cx (Raise (RaiseReason r))) es
Proof
  cheat
QED

(* Retain the runtime API as a specialization of the shared fragment. *)
Theorem compile_raise_code_reason_frag:
  !ctx func cx lctx RetQ cenv ty r es res es'.
    ~cenv.ce_is_ctor /\
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_vv_sim ctx func cenv cx (expr_type r) r es /\
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_code_vv vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Raise (RaiseReason r)))
      (eval_stmt cx (Raise (RaiseReason r))) es
Proof
  cheat
QED

(* assert e, r for a reason r as compile_raise_code_reason_frag has it:
   the condition and a JNZ to the ok block, where the code ends, and a fail
   block with r's fragment, the encoder and its REVERT.  r's judgment is
   at the source state after a false condition. *)
Theorem compile_assert_code_reason_shared_frag:
  !ctx func cx lctx RetQ cenv ty e r es res es'.
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_type e = BaseT BoolT /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!es1. (do raw <- eval_expr cx e; read_result cx raw od) es =
         (INL (BoolV F), es1) ==>
           expr_vv_sim ctx func cenv cx (expr_type r) r es1) /\
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_code_vv vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assert e (AssertReason r)))
      (eval_stmt cx (Assert e (AssertReason r))) es
Proof
  cheat
QED

Theorem compile_assert_code_reason_frag:
  !ctx func cx lctx RetQ cenv ty e r es res es'.
    ~cenv.ce_is_ctor /\
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_type e = BaseT BoolT /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!es1. (do raw <- eval_expr cx e; read_result cx raw od) es =
         (INL (BoolV F), es1) ==>
           expr_vv_sim ctx func cenv cx (expr_type r) r es1) /\
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_code_vv vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assert e (AssertReason r)))
      (eval_stmt cx (Assert e (AssertReason r))) es
Proof
  cheat
QED
