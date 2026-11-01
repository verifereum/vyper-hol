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
  list rich_list finite_map pred_set
  fragExec localPtrsProps exprSim exprSimUnwrap exprSimHyps exprSimWordBuiltins loweringSlice
  exprSimStorageCopy exprOperandVar
  stmtSim stmtSimIf stmtSimReason stmtSimReasonExpr
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
  rpt gen_tac >>
  simp[reason_storage_vv_def] >> strip_tac >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def] >> strip_tac >>
  irule (INST_TYPE [alpha |-> ``:bool``] ensure_storage_memory_defined_frag) >>
  goal_assum (drule_at (Pat `compile_ensure_in_memory _ _ _ _ _ _ _ = _`)) >>
  simp[] >> metis_tac[]
QED

Theorem unwrap_storage_reason_var:
  !cenv ty p sa op sb.
    reason_storage_vv (LocatedValue ty p) /\
    unwrap_value cenv (LocatedValue ty p) sa = (op,sb) ==>
    ?x. op = Var x
Proof
  rpt gen_tac >> simp[reason_storage_vv_def] >> strip_tac >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def, ensure_storage_memory_layout,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  drule storage_copy_alloc_layout >> strip_tac >> gvs[]
QED

Theorem storage_reason_tail_known:
  !hs sm t u x w.
    reason_known hs t /\ EVERY (not_fresh_at sm) hs /\
    (!y. not_fresh_at sm y ==> lookup_var y u = lookup_var y t) /\
    eval_operand (Var x) u = SOME w ==>
    reason_known (x::hs) u
Proof
  simp[reason_known_def, EVERY_MEM, eval_operand_def] >> metis_tac[]
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
  rpt strip_tac >> drule compile_revert_reason_split_certificate >>
  strip_tac >>
  `frag_exec ctx sa sm (\s. s = sbase)
    (\s. reason_known hs s /\
      (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
      s.vs_labels = sbase.vs_labels) R` by
    (irule reason_head_frag >> simp[] >> metis_tac[]) >>
  drule frag_exec_then >> disch_then irule >> simp[] >>
  conj_tac
  >- (qx_gen_tac `t` >> strip_tac >>
      `eval_operand p.ptr_operand t = SOME a` by
        (Cases_on `p.ptr_operand` >> gvs[eval_operand_def] >> metis_tac[]) >>
      `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
        (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
         qexists `sa` >> simp[]) >>
      `frag_exec ctx sm sn (\s. s = t)
        (\s. (?w. eval_operand op s = SOME w) /\
          (!x. not_fresh_at sm x ==> lookup_var x s = lookup_var x t) /\
          s.vs_labels = t.vs_labels) R` by
        (irule unwrap_storage_reason_defined_frag >>
         goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      drule frag_exec_then >> disch_then irule >> simp[] >>
      reverse conj_tac
      >- (irule unwrap_value_extends >> goal_assum (drule_at Any)) >>
      qx_gen_tac `u` >> strip_tac >>
      drule_all unwrap_storage_reason_var >> strip_tac >> gvs[] >>
      rename1 `eval_operand (Var x) u = SOME w` >>
      first_x_assum (qspec_then `x::hs` mp_tac) >>
      simp[reason_operand_def] >> strip_tac >>
      `reason_known (x::hs) u` by
        (irule storage_reason_tail_known >> simp[] >>
         qexistsl_tac [`sm`, `t`] >> simp[]) >>
      `frag_exec ctx sn sb (reason_known (x::hs)) (\s. F) R` by
        (irule reason_prefix_revert_frag >> simp[] >> metis_tac[]) >>
      drule frag_exec_weaken >> disch_then irule >> simp[]) >>
  irule cs_extends_trans >> qexists `sn` >> simp[] >>
  irule unwrap_value_extends >> goal_assum (drule_at Any)
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
  rpt gen_tac >> strip_tac >>
  `cs_extends sm sb` by
    (drule compile_revert_reason_split_certificate >> strip_tac >>
     drule unwrap_value_extends >> strip_tac >>
     metis_tac[cs_extends_trans]) >>
  `!t p. vv = LocatedValue t p ==>
     !x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    (rpt strip_tac >>
     qspecl_then [`cenv`, `expr_type r`, `r`, `sa`, `vv`, `sm`] mp_tac
       (cj 1 compiler_compile_var) >>
     gvs[vv_operand_def]) >>
  `?t p. vv = LocatedValue t p` by metis_tac[reason_storage_vv_def] >>
  gvs[] >>
  irule reason_expr_revert_frag_general >> simp[] >>
  goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  qexists_tac `\s. ?w. eval_operand p.ptr_operand s = SOME w` >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> gvs[vv_holds_def]) >>
  irule frag_exec_pointwise >> simp[] >>
  rpt strip_tac >> irule compile_revert_storage_reason_frag >>
  simp[] >> metis_tac[]
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
  rpt gen_tac >> strip_tac >>
  Cases_on `eval_expr cx r es` >> rename1 `_ = (raw, est)` >>
  `est = es1` by
    (qpat_x_assum `(do raw <- _; _ od) _ = _` mp_tac >>
     simp[bind_def] >> Cases_on `raw` >> simp[] >> strip_tac >>
     metis_tac[read_result_state]) >> gvs[] >>
  `expr_vv_res_ok raw` by
    (qpat_x_assum `(do raw <- _; _ od) _ = _` mp_tac >>
     simp[bind_def] >> Cases_on `raw` >> simp[] >> strip_tac >>
     gvs[expr_vv_res_ok_def, expr_res_ok_def] >>
     rename1 `read_result cx captured es1` >> Cases_on `captured` >>
     gvs[expr_vv_res_ok_def, read_result_def, raise_def, expr_res_ok_def]) >>
  `!rr. expr_exit raw rr ==> R rr` by
    (rpt strip_tac >> Cases_on `raw` >> gvs[] >>
     qpat_x_assum `(do raw <- _; _ od) _ = _` mp_tac >>
     simp[bind_def] >> strip_tac >> gvs[] >>
     metis_tac[expr_exit_exception_transport]) >>
  irule reason_storage_expr_revert_frag >> simp[] >>
  goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >> simp[] >>
  metis_tac[]
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
    eval_stmt cx (Raise (RaiseReason r)) es = (res, es') /\
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_vv_sim ctx func cenv cx (expr_type r) r es /\
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_storage_vv vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Raise (RaiseReason r))) es res es'
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_def] >> rpt gen_tac >>
  strip_tac >> disj2_tac >>
  `compile_reason_message cenv r = compile_expr cenv (expr_type r) r` by
    metis_tac[compile_reason_message_expr] >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  qpat_assum `compile_reason_message _ _ = _` (fn th => rewrite_tac[th]) >>
  Cases_on `compile_expr cenv (expr_type r) r sa` >> rename1 `_ = (vv, sm)` >>
  simp[] >>
  Cases_on `compile_revert_with_reason cenv vv (expr_type r)
              (type_memory_bytes cenv (expr_type r)) sm` >>
  rename1 `_ = (u, sf)` >> Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  rename1 `fn_has_code sa sfin func` >>
  drule_all eval_raise_reason_cases >> disch_then (qx_choose_then `r1` assume_tac) >>
  qspecl_then [`r1`, `res`, `RetQ`, `es'`] mp_tac raise_reason_exits >>
  impl_tac >- fs[] >> strip_tac >>
  `frag_exec ctx sa sfin (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. F) (stmt_exit RetQ es' res)` by
    (irule (INST_TYPE [alpha |-> ``:type``] reason_storage_expr_revert_forced_frag) >> simp[] >>
     goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
     qexistsl_tac [`es'`, `type_memory_bytes cenv (expr_type r)`, `r1`, `expr_type r`] >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` (mp_tac o REWRITE_RULE [frag_exec_def]) >>
  disch_then (qspecl_then [`func`, `s0`] mp_tac) >> simp[]
QED

(* assert e, r for a reason r as compile_raise_storage_reason_frag has it:
   the condition and a JNZ to the ok block, where the code ends, and a fail
   block with r's fragment, the encoder and its REVERT.  r's judgment is
   at the source state after a false condition. *)
Theorem compile_assert_storage_reason_frag:
  !ctx func cx lctx RetQ cenv ty e r es res es'.
    eval_stmt cx (Assert e (AssertReason r)) es = (res, es') /\
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_type e = BaseT BoolT /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!es1. (do raw <- eval_expr cx e; read_result cx raw od) es =
         (INL (BoolV F), es1) ==>
           expr_vv_sim ctx func cenv cx (expr_type r) r es1) /\
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_storage_vv vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assert e (AssertReason r))) es res es'
Proof
  rpt strip_tac >> irule compile_assert_reason_frag_general >> simp[] >>
  rpt strip_tac >>
  `eval_stmt cx (Raise (RaiseReason r)) es1 = (res, es')` by
    metis_tac[eval_assert_reason_false] >>
  drule_all eval_raise_reason_cases >>
  disch_then (qx_choose_then `rr` assume_tac) >>
  qspecl_then [`rr`, `res`, `RetQ`, `es'`] mp_tac raise_reason_exits >>
  impl_tac >- fs[] >> strip_tac >>
  irule (INST_TYPE [alpha |-> ``:type``] reason_storage_expr_revert_forced_frag) >> simp[] >>
  goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >> simp[] >>
  qexistsl_tac [`type_memory_bytes cenv (expr_type r)`, `expr_type r`] >>
  simp[] >> first_x_assum irule >> goal_assum (drule_at Any)
QED
