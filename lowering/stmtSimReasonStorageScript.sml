(*
 * Statement simulation: Raise and Assert with a reason read from storage
 * or transient storage (#637)
 *
 * A reason that compile_expr hands out as a pointer into storage or
 * transient storage (a string state variable, or a string inside one)
 * reaches the Error(string) encoder of compile_revert_with_reason as a
 * LocatedValue, which the encoder's unwrap_value copies into a buffer of
 * its own (compile_ensure_in_memory: an SLOAD or TLOAD for one word, the
 * word copy loop otherwise) before the rest of the encoder runs.  As for
 * the reasons in stmtSimReasonExpr, the REVERT's data is not compared, so
 * only definedness matters: the copy reads and writes words and loops a
 * fixed number of times, whatever storage holds (exprSimStorageCopy).
 *
 * TOP-LEVEL:
 *   reason_storage_vv                   — the reason's value_vv: a pointer
 *                                         into storage or transient storage
 *   compile_raise_storage_reason_frag   — raise with such a reason
 *   compile_assert_storage_reason_frag  — assert with such a reason
 *
 * Helper: unwrap_storage_reason_defined_frag, unwrap_storage_reason_var,
 *   storage_reason_tail_known, compile_revert_storage_reason_frag,
 *   reason_storage_expr_revert_frag
 *)

Theory stmtSimReasonStorage
Ancestors
  exprSimUnwrapProps
  stmtSimDefs
  exprSimDefs
  loweringPosts
  list rich_list finite_map pred_set
  fragExec localPtrsProps  exprSimUnwrap exprSimHyps exprSimWordBuiltins loweringSlice
  exprSimStorageCopy exprOperandVar
   stmtSimIf stmtSimReason stmtSimReasonExpr
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  context compileEnv moduleLoweringProps
  vyperInterpreter vyperState vyperValue vyperExprNoControl
  venomExecSemantics venomInst venomState
Libs
  monadsyntax

(* The reason's value_vv is a pointer to a value of a type that is not a
   word type (a string) in storage or transient storage. *)
Definition reason_storage_vv_def:
  reason_storage_vv vv <=>
    ?t p. vv = LocatedValue t p /\ ~is_word_type t /\
          (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient)
End


Theorem unwrap_storage_reason_defined_frag:
  !ctx cenv ty p sa op sb sbase a R.
    reason_storage_vv (LocatedValue ty p) /\
    unwrap_value cenv (LocatedValue ty p) sa = (op,sb) /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
    eval_operand p.ptr_operand sbase = SOME a ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. (?w. eval_operand op s = SOME w) /\
           (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
           s.vs_labels = sbase.vs_labels) R
Proof
  cheat
QED

Theorem unwrap_storage_reason_var:
  !cenv ty p sa op sb.
    reason_storage_vv (LocatedValue ty p) /\
    unwrap_value cenv (LocatedValue ty p) sa = (op,sb) ==>
    ?x. op = Var x
Proof
  cheat
QED

Theorem storage_reason_tail_known:
  !hs sm t u x w.
    reason_known hs t /\ EVERY (not_fresh_at sm) hs /\
    (!y. not_fresh_at sm y ==> lookup_var y u = lookup_var y t) /\
    eval_operand (Var x) u = SOME w ==>
    reason_known (x::hs) u
Proof
  cheat
QED

Theorem compile_revert_storage_reason_frag:
  !ctx cenv ty p mt ms sa sb sbase a R.
    reason_storage_vv (LocatedValue ty p) /\
    compile_revert_with_reason cenv (LocatedValue ty p) mt ms sa = ((),sb) /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
    eval_operand p.ptr_operand sbase = SOME a /\
    (!t. R (Abort Revert_abort t)) ==>
    frag_exec ctx sa sb (\s. s = sbase) (\s. F) R
Proof
  cheat
QED

Theorem reason_storage_expr_revert_frag:
  !ctx func cenv cx r es res1 es1 sa vv sm rty msz sb s0 R.
    compile_expr cenv (expr_type r) r sa = (vv, sm) /\
    compile_revert_with_reason cenv vv rty msz sm = ((), sb) /\
    reason_storage_vv vv /\
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

Theorem reason_storage_expr_revert_forced_frag[local]:
  !ctx func cenv cx r es res1 es1 sa vv sm rty msz sb s0 R.
    compile_expr cenv (expr_type r) r sa = (vv, sm) /\
    compile_revert_with_reason cenv vv rty msz sm = ((), sb) /\
    reason_storage_vv vv /\
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

(* raise r, for a reason r that is not a string literal and whose value
   compile_expr hands out as a pointer into storage or transient storage:
   r's fragment, whose errors exit, then the Error(string) encoder, whose
   unwrap_value copies the value into memory, and its REVERT. *)

(* Why it holds.  As compile_raise_reason_frag.  On a value, vv_post's
   vv_holds gives the pointer's operand defined (eval_operand p.ptr_operand
   = SOME w).  The encoder's instructions before unwrap_value (an ALLOCA,
   an MSTORE, an ADD, an ALLOCA) run with defined operands; unwrap_value's
   compile_ensure_in_memory allocates a buffer and copies (SLOAD or TLOAD
   then MSTORE for one word; for more, compile_word_copy_loop, whose
   counter runs from 0 until it equals n2w word_count, every step of its
   cond and body blocks defined, ending at the start of its exit block with
   the variables handed out before it unchanged); the rest of the encoder,
   in the block where the copy leaves off, runs to its REVERT as in
   compile_revert_reason_certificate.  No storage invariant is needed:
   SLOAD and TLOAD are defined at every slot and the copy's length is the
   type's, not the stored length. *)
Theorem compile_raise_storage_reason_frag:
  !ctx func cx lctx RetQ cenv ty r es res es'.
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_vv_sim ctx func cenv cx (expr_type r) r es /\
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_storage_vv vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Raise (RaiseReason r)))
      (eval_stmt cx (Raise (RaiseReason r))) es
Proof
  cheat
QED

(* assert e, r for a reason r as compile_raise_storage_reason_frag has it:
   the condition and a JNZ to the ok block, where the code ends, and a fail
   block with r's fragment, the encoder and its REVERT.  r's judgment is
   at the source state after a false condition. *)
Theorem compile_assert_storage_reason_frag:
  !ctx func cx lctx RetQ cenv ty e r es res es'.
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_type e = BaseT BoolT /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!es1. (do raw <- eval_expr cx e; read_result cx raw od) es =
         (INL (BoolV F), es1) ==>
           expr_vv_sim ctx func cenv cx (expr_type r) r es1) /\
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_storage_vv vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assert e (AssertReason r)))
      (eval_stmt cx (Assert e (AssertReason r))) es
Proof
  cheat
QED
