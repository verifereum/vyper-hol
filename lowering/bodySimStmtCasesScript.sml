(*
 * The body simulation of S1: statement cases (#637)
 *
 * One lemma for each statement case of evaluate_ind that bodySimMain's
 * body_sim_mutual does not close in a line or two.  Those marked GAP are
 * cheated; their comments name the existing lemmas they dispatch to and
 * what is left.
 *
 * TOP-LEVEL:
 *   body_*_case       — one case of the induction each
 *   stmt_expr_body_pre — a statement's expression meets expr_body_pre
 *)

Theory bodySimStmtCases
Ancestors
  list bodySim exprSim exprSimHyps exprLoweringProps stmtSim stmtSimIf
  supportedExprTraverse supportedStmtTraverse supportedStmts
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  vyperTypeCallStackSoundness

(* ===== Helpers ===== *)

(* A statement's expression meets expr_body_pre. *)
Theorem stmt_expr_body_pre:
  !cenv cx env e es calls.
    expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
    ~supported_expr_exists
       (\e. ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) e /\
    call_evaluation_safe cx (int_calls_expr e ++ calls) ==>
    expr_body_pre cenv cx env e es
Proof
  rpt gen_tac >> strip_tac >>
  `byte_widths_expr e /\ alloc_limits_expr cenv e` by
    (CCONTR_TAC >> qpat_x_assum `~supported_expr_exists _ _` mp_tac >>
     simp[] >> irule supported_expr_exists_root >> metis_tac[]) >>
  simp[expr_body_pre_def] >> metis_tac[call_evaluation_safe_append_left]
QED

(* An assertion with no reason: stmtSimIf's compile_assert_frag. *)
Theorem body_assert_case:
  !cx e ak.
    (ak = AssertBare \/ ak = AssertUnreachable) /\ body_expr_ok cx e ==>
    body_stmt_ok cx (Assert e ak)
Proof
  rw[body_stmt_ok_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_assert_exists_def, int_calls_stmt_def,
         int_calls_assert_reason_def] >>
     qexists_tac `[]` >> simp[]) >>
  irule compile_assert_frag >> gvs[type_stmt_def] >>
  fs[body_expr_ok_def] >> metis_tac[compile_expr_grows]
QED

(* ===== Cases ===== *)

(* ===== Statements ===== *)

Theorem body_pass_case:
  !cx. body_stmt_ok cx Pass
Proof
  rw[body_stmt_ok_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, return_def] >> rw[compile_pass_frag]
QED

Theorem body_continue_case:
  !cx. body_stmt_ok cx Continue
Proof
  rw[body_stmt_ok_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, raise_def] >> rw[] >>
  Cases_on `lctx` >> simp[compile_continue_frag] >>
  simp[stmt_frag_def, stmt_res_ok_def]
QED

Theorem body_break_case:
  !cx. body_stmt_ok cx Break
Proof
  rw[body_stmt_ok_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, raise_def] >> rw[] >>
  Cases_on `lctx` >> simp[compile_break_frag] >>
  simp[stmt_frag_def, stmt_res_ok_def]
QED

(* The frame's RetQ (frame_ret_ok). *)
Theorem body_return_none_case:
  !cx. body_stmt_ok cx (Return NONE)
Proof
  rw[body_stmt_ok_def, frame_ret_ok_def] >>
  first_x_assum irule >> simp[same_frame_refl] >>
  qexists_tac `env` >> simp[]
QED

Theorem body_return_case:
  !cx e. body_expr_ok cx e ==> body_stmt_ok cx (Return (SOME e))
Proof
  rw[body_stmt_ok_def, frame_ret_ok_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_expr_exists_def, int_calls_stmt_def, int_calls_expr_def] >>
     qexists_tac `[]` >> simp[]) >>
  first_x_assum irule >> fs[body_expr_ok_def] >>
  conj_tac >- metis_tac[] >> qexists_tac `env` >> simp[]
QED

(* GAP (#637 raise/assert with a reason): stmtSimReasonExpr's
   compile_raise_reason_frag and stmtSimReasonStorage's
   compile_raise_storage_reason_frag cover the reason's forms; they take
   the reason's expr_sim under expr_sim_pre.  Left: the dispatch on the
   reason's form, and the reason's buffer at a frontier after internal
   calls. *)
Theorem body_raise_reason_case:
  !cx e. body_expr_ok cx e ==> body_stmt_ok cx (Raise (RaiseReason e))
Proof
  cheat
QED

(* GAP (#637 raise/assert with a reason): compile_assert_reason_frag
   (stmtSimReasonExpr) and compile_assert_storage_reason_frag
   (stmtSimReasonStorage), as for body_raise_reason_case. *)
Theorem body_assert_reason_case:
  !cx e se.
    (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_expr_ok cx se) /\
    body_expr_ok cx e ==>
    body_stmt_ok cx (Assert e (AssertReason se))
Proof
  cheat
QED

(* GAP (#637 log): no statement lemma for Log yet.  body_inv ties
   ce_event_info to the program's events, and supported_log the
   arguments' types to the event's fields. *)
Theorem body_log_case:
  !cx id es. body_exprs_ok cx es ==> body_stmt_ok cx (Log id es)
Proof
  cheat
QED

(* GAP (#637 declarations): stmtSimDecl's compile_annassign_stmt_frag,
   compile_annassign_word_stmt_frag and compile_annassign_typed_stmt_frag,
   stmtSimDeclMem's compile_annassign_memory_stmt_frag and
   compile_annassign_memory_widen_stmt_frag, and stmtSimDeclEmpty's
   compile_annassign_empty_stmt_frag cover the value's forms.  Left: the
   dispatch on the declared type and the value's form. *)
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

(* GAP (#637 append): no statement lemma for Append yet; the target's
   pointer comes from compile_get_target_ptr. *)
Theorem body_append_case:
  !cx t e.
    (!s'' p t'. eval_target_place cx t s'' = (INL p,t') ==> body_expr_ok cx e) /\
    body_base_target_ok cx t ==>
    body_stmt_ok cx (Append t e)
Proof
  cheat
QED

(* GAP (#637 assignments): stmtSimAssign's compile_assign_local_stmt_frag,
   stmtSimAssignMem's compile_assign_local_memory_stmt_frag and
   stmtSimAssignStorage's compile_assign_storage_stmt_frag and
   compile_assign_storage_typed_stmt_frag cover a name, a local in memory
   and a storage variable.  Left: subscript and attribute targets (the
   simulation of compile_get_target_ptr on eval_target_place), and the
   dispatch. *)
Theorem body_assign_case:
  !cx t e.
    (!s'' pv t'. eval_expr cx e s'' = (INL pv,t') ==> body_base_target_ok cx t) /\
    body_expr_ok cx e ==>
    body_stmt_ok cx (Assign (BaseTarget t) e)
Proof
  cheat
QED

(* GAP (#637 tuple assignments): stmtSimAssignTuple's
   compile_assign_tuple_locals_stmt_frag and stmtSimAssignTupleMem's
   compile_assign_tuple_locals_memory_stmt_frag cover tuples of locals.
   Left: other base targets (compile_tuple_store_all).  A nested
   TupleTarget, which the lowering compiles to INVALID, is not
   supported (supported_assignment). *)
Theorem body_assign_tuple_case:
  !cx gs e.
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_ok cx (TupleTarget gs) v) /\ body_expr_ok cx e ==>
    body_stmt_ok cx (Assign (TupleTarget gs) e)
Proof
  cheat
QED

(* GAP (#637 augmented assignment): stmtSimAugAssign's
   compile_augassign_local_stmt_frag covers a local word.  Left: other
   targets. *)
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

(* GAP (#637 if): stmtSimIf's compile_if_stmt_frag, given the
   branches' judgments at the pushed scope.  Left: cs_mono of stmts_env
   (no lemma that compile_stmt only appends yet), and the branches'
   premises at the pushed scope (expr_sim_inv, the typing). *)
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

(* GAP (#637 for): stmtSimFor's compile_for_range_frag and
   compile_for_range_lit_frag and stmtSimForRange's
   compile_for_range_checked_frag cover a range with literal bounds.
   Left: other ranges, iteration over an array, and the body's premises
   at each iteration's scope. *)
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

(* GAP (#637 expression statements): stmtSim's compile_expr_stmt_frag,
   given the expression's expr_vv_sim (the IH) and that compile_expr
   leaves its block open, which has no lemma yet. *)
Theorem body_expr_stmt_case:
  !cx e. body_expr_ok cx e ==> body_stmt_ok cx (Expr e)
Proof
  cheat
QED

(* ===== Statement lists ===== *)

Theorem body_stmts_nil_case:
  !cx. body_stmts_ok cx []
Proof
  rw[body_stmts_ok_def] >>
  qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, return_def] >> rw[stmt_frag_nil]
QED

(* GAP (#637 statement lists): stmtSim's stmt_frag_cons, given
   cs_mono of compile_stmt and stmts_env (no lemma yet), the head's
   judgment (the IH), and the tail's at every c with
   cenv_top_ext cenv c es1.scopes.  Left: those, and the tail's premises
   at es1: expr_sim_inv at the env the head's typing gives, and at c.
   stmt_frag_cons asks for the tail at every such c, while the
   declarations bind only the c that stmt_env returns; a variant of
   stmt_frag_cons for that c may be needed. *)
Theorem body_stmts_cons_case:
  !cx s ss.
    (!s'' x t. eval_stmt cx s s'' = (INL x,t) ==> body_stmts_ok cx ss) /\
    body_stmt_ok cx s ==>
    body_stmts_ok cx (s::ss)
Proof
  cheat
QED
