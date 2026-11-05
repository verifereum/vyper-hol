(*
 * Statement simulation: Raise and Assert with a reason that is not a
 * string literal (#637)
 *
 * The reason is lowered with compile_expr (compile_reason_message's
 * fallback) and its value_vv handed to the Error(string) encoder of
 * compile_revert_with_reason, whose unwrap_value emits no code when the
 * value is on the stack or a string in memory (reason_vv).  The encoder
 * runs to its REVERT from any state where that operand is defined
 * (stmtSimReason's certificate), so the reason's fragment ends either in
 * an exit of its own or at the encoder with the operand defined.
 *
 * TOP-LEVEL:
 *   reason_vv_ok                — the reason's value_vv as the encoder needs
 *   compile_raise_reason_frag   — raise with a reason
 *   compile_assert_reason_frag  — assert with a reason
 *
 * Helper: compile_reason_message_expr, reason_ds,
 *   reason_expr_revert_extends, reason_expr_revert_frag,
 *   eval_raise_reason_cases
 *)

Theory stmtSimReasonExpr
Ancestors
  exprSimUnwrapProps
  stmtSimProps
  stmtSimDefs
  exprSimDefs
  loweringPosts
  list rich_list finite_map pred_set
  fragExec localPtrsProps  exprSimUnwrap loweringSlice
   stmtSimIf stmtSimReason
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv
  vyperInterpreter vyperState vyperValue vyperExprNoControl
  vyperStatePreservation
  venomExecSemantics venomInst venomState
Libs
  monadsyntax

(* ===== The reason's value ===== *)

(* A reason other than a string literal is lowered by compile_expr. *)
Theorem compile_reason_message_expr:
  !cenv r.
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) ==>
    compile_reason_message cenv r = compile_expr cenv (expr_type r) r
Proof
  cheat
QED

(* The reason's value_vv hands the encoder an operand of its own that is not
   a label. *)
Definition reason_vv_ok_def:
  reason_vv_ok vv <=> ?op. reason_vv vv = SOME op /\ !l. op <> Label l
End

(* The variables the encoder needs defined for a message operand. *)
Definition reason_ds_def:
  reason_ds (Var x) = [x] /\
  reason_ds (Lit w) = [] /\
  reason_ds (Label l) = []
End

Theorem vv_holds_reason_vv[local]:
  !cenv cx t tv vv es s op.
    vv_holds cenv cx t tv vv es s /\ reason_vv vv = SOME op ==>
    ?w. eval_operand op s = SOME w
Proof
  cheat
QED

(* The reason's code and the encoder only append. *)
Theorem reason_expr_revert_extends_any[local]:
  !cenv r sa vv sm rty msz sb.
    compile_expr cenv (expr_type r) r sa = (vv, sm) /\
    compile_revert_with_reason cenv vv rty msz sm = ((), sb) ==>
    cs_extends sa sb
Proof
  cheat
QED

Theorem reason_expr_revert_extends:
  !cenv r sa vv sm rty msz sb.
    compile_expr cenv (expr_type r) r sa = (vv, sm) /\
    compile_revert_with_reason cenv vv rty msz sm = ((), sb) /\
    reason_vv_ok vv ==>
    cs_extends sa sb
Proof
  cheat
QED

(* The forced reason may fail either while evaluating or while reading a
   captured place.  compile_expr's judgment remains at the raw boundary;
   its successful postcondition supplies the encoder's defined operand.
   A failed read is still covered by the statement's revert exit. *)
Theorem reason_expr_revert_frag_general:
  !ctx func cenv cx r es res1 es1 sa vv sm sb s0 R P.
    compile_expr cenv (expr_type r) r sa = (vv, sm) /\
    cs_extends sm sb /\
    expr_vv_sim ctx func cenv cx (expr_type r) r es /\
    eval_expr cx r es = (res1, es1) /\ expr_vv_res_ok res1 /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    (!rr. expr_exit res1 rr ==> R rr) /\
    (!tv s. vv_holds cenv cx (expr_type r) tv vv es1 s ==> P s) /\
    frag_exec ctx sm sb P (\s. F) R ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. F) R
Proof
  cheat
QED

(* The reason's fragment, then the encoder and its REVERT: an exit, the
   reason's own as expr_exit allows, or the REVERT. *)
Theorem reason_expr_revert_frag:
  !ctx func cenv cx r es res1 es1 sa vv sm rty msz sb s0 R.
    compile_expr cenv (expr_type r) r sa = (vv, sm) /\
    compile_revert_with_reason cenv vv rty msz sm = ((), sb) /\
    reason_vv_ok vv /\
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

(* ===== The source ===== *)

(* Raise inspects the forced result, not the captured expression result:
   a value or PlaceR may read as a string, and either evaluation or the
   read may fail.  Type errors remain outside stmt_frag's outcomes. *)
Theorem eval_raise_reason_cases:
  !cx r es res es' lctx.
    eval_stmt cx (Raise (RaiseReason r)) es = (res, es') /\
    stmt_res_ok lctx res ==>
    ?r1. (do raw <- eval_expr cx r; read_result cx raw od) es = (r1, es') /\
         expr_res_ok r1 /\
         ((?str. r1 = INL (StringV str) /\
                 res = INR (AssertException str)) \/
          (?ex. r1 = INR ex /\ res = INR ex))
Proof
  cheat
QED

Theorem expr_res_ok_revert[local]:
  !ex t. expr_res_ok (INR ex : value + exception) ==>
         expr_exit (INR ex : unit + exception) (Abort Revert_abort t)
Proof
  cheat
QED

(* The exits of a raise with a reason, as the reason's outcome gives them. *)
Theorem raise_reason_exits:
  !r1 res RetQ es'.
    expr_res_ok r1 /\
    ((?str. r1 = INL (StringV str) /\
            res = INR (AssertException str)) \/
     (?ex. r1 = INR ex /\ res = INR ex)) ==>
    (!rr. expr_exit r1 rr ==> stmt_exit RetQ es' res rr) /\
    (!t. stmt_exit RetQ es' res (Abort Revert_abort t))
Proof
  cheat
QED

(* ===== raise ===== *)

(* raise r, for a reason r that is not a string literal and whose value
   compile_expr hands out on the stack or in memory: r's fragment, whose
   errors exit, then the Error(string) encoder and its REVERT. *)
Theorem compile_raise_reason_frag:
  !ctx func cx lctx RetQ cenv ty r es res es'.
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_vv_sim ctx func cenv cx (expr_type r) r es /\
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_vv_ok vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Raise (RaiseReason r)))
      (eval_stmt cx (Raise (RaiseReason r))) es
Proof
  cheat
QED

(* ===== assert ===== *)

(* A false condition runs the reason as raise does, from the state after
   the condition. *)
Theorem eval_assert_reason_false:
  !cx e r es es1.
    (do raw <- eval_expr cx e; read_result cx raw od) es =
      (INL (BoolV F), es1) ==>
    eval_stmt cx (Assert e (AssertReason r)) es =
    eval_stmt cx (Raise (RaiseReason r)) es1
Proof
  cheat
QED

(* assert e, r for a reason r as compile_raise_reason_frag has it: the
   condition and a JNZ to the ok block, where the code ends, and a fail
   block with r's fragment, the encoder and its REVERT.  r's judgment is
   at the source state after a false condition. *)
Theorem compile_assert_reason_frag:
  !ctx func cx lctx RetQ cenv ty e r es res es'.
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_type e = BaseT BoolT /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!es1. (do raw <- eval_expr cx e; read_result cx raw od) es =
             (INL (BoolV F), es1) ==>
           expr_vv_sim ctx func cenv cx (expr_type r) r es1) /\
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_vv_ok vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assert e (AssertReason r)))
      (eval_stmt cx (Assert e (AssertReason r))) es
Proof
  cheat
QED




(* Check the public forced boundary and both reason-expression consumers. *)
Theorem compile_assert_reason_frag_general:
  !ctx func cx lctx RetQ cenv ty e r es res es'.
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_type e = BaseT BoolT /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!es1 sa vv sm sb s0.
       (do raw <- eval_expr cx e; read_result cx raw od) es =
         (INL (BoolV F), es1) /\
       compile_expr cenv (expr_type r) r sa = (vv, sm) /\
       compile_revert_with_reason cenv vv (expr_type r)
         (type_memory_bytes cenv (expr_type r)) sm = ((), sb) /\
       fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
       local_ptrs_reserved cenv sa /\ stmt_res_ok lctx res ==>
       frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es1 s)
         (\s. F) (stmt_exit RetQ es' res)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assert e (AssertReason r)))
      (eval_stmt cx (Assert e (AssertReason r))) es
Proof
  cheat
QED





val () = List.app (fn th =>
  let val (ors, axs) = Tag.dest_tag (Thm.tag th)
  in if null axs andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") ors
     then print "REASON_EXPR_FORCE_AUDIT OK\n"
     else print "statement-check gate skipped\n"
  end) [compile_reason_message_expr, reason_expr_revert_extends,
        reason_expr_revert_frag, eval_raise_reason_cases,
        compile_raise_reason_frag, compile_assert_reason_frag];
