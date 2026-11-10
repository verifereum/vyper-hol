(*
 * The predicates of the pointer twin of bodySimMain's body induction:
 * bodySim's body_*_ok with bodyPtrDefs's judgments (expr_sim_ptr,
 * expr_vv_sim_ptr, stmt_frag_ptr, frame_ret_ok_ptr) in place of S1's,
 * for any caller return buffer d and parameter provenance PG.
 *
 * TOP-LEVEL:
 *   body_expr_ptr_ok, body_stmt_ptr_ok, body_stmts_ptr_ok,
 *   body_exprs_ptr_ok, body_results_ptr_ok, body_iterator_ptr_ok,
 *   body_for_ptr_ok, body_base_target_ptr_ok, body_tuple_target_ptr_ok,
 *   body_tuple_targets_ptr_ok -- the eleven predicates, as bodySim's
 *)
Theory bodyPtrPreds
Ancestors
  bodyPtrDefs bodySim exprSimHypsDefs supportedStmts
  vyperInterpreter vyperTypeSystem vyperState vyperAST list

val _ = Parse.hide "body";

(* As bodySim's body_expr_ok, a literal array's elements are ok too. *)
Definition body_expr_ptr_ok_def:
  (body_expr_ptr_ok cx e <=>
    (!d PG tops ctx func cenv env ty es.
      body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es ==>
      expr_sim_ptr d ctx PG func cenv cx ty e es /\
      expr_vv_sim_ptr d ctx PG func cenv cx ty e es) /\
    (!a t n elems.
      e = Builtin a (MakeArray t n) elems /\
      builtin_args_length_ok (MakeArray t n) (LENGTH elems) ==>
      body_exprs_ptr_ok cx elems)) /\
  body_exprs_ptr_ok cx [] = T /\
  body_exprs_ptr_ok cx (e::es) =
    (body_expr_ptr_ok cx e /\
     ((?s tv t s1 v t1. eval_expr cx e s = (INL tv, t) /\
                        read_result cx tv s1 = (INL v, t1)) ==>
      body_exprs_ptr_ok cx es))
Termination
  WF_REL_TAC `measure (\x. case x of
      INL (_, e) => expr_size e
    | INR (_, es) => list_size expr_size es)` >>
  simp[expr_size_def]
End

Theorem body_exprs_ptr_ok_def = CONJUNCT2 body_expr_ptr_ok_def;

(* The elements of an array literal are ok, by the literal's clause. *)
Theorem body_make_array_children_ptr_ok:
  !cx a t n elems.
    body_expr_ptr_ok cx (Builtin a (MakeArray t n) elems) /\
    builtin_args_length_ok (MakeArray t n) (LENGTH elems) ==>
    body_exprs_ptr_ok cx elems
Proof
  rpt strip_tac >>
  qpat_x_assum `body_expr_ptr_ok _ _`
    (mp_tac o CONJUNCT2 o ONCE_REWRITE_RULE [body_expr_ptr_ok_def]) >>
  simp[]
QED

Definition body_stmt_ptr_ok_def:
  body_stmt_ptr_ok cx s <=>
    !d PG tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
      body_inv tops ctx cenv cx /\ supported_stmt tops bindings s /\
      (!target. supported_stmt_expr_exists
         (expr_abi_decode_target_root target) s ==>
         occurs_abi_decode_target target tops) /\
      expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
      locals_alloc_ok cenv env /\
      type_stmt env ret_ty s = SOME env' /\ stmt_exprs_ok cenv s /\
      call_evaluation_safe cx (int_calls_stmt s) /\
      frame_ret_ok_ptr d ctx PG func cx RetQ cenv ret_ty ==>
      stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
        (stmt_env cenv lctx ret_ty s) (eval_stmt cx s) es
End

Definition body_stmts_ptr_ok_def:
  body_stmts_ptr_ok cx ss <=>
    !d PG tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
      body_inv tops ctx cenv cx /\ supported_stmts tops bindings ss /\
      (!target. supported_stmts_expr_exists
         (expr_abi_decode_target_root target) ss ==>
         occurs_abi_decode_target target tops) /\
      expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
      locals_alloc_ok cenv env /\
      type_stmts env ret_ty ss = SOME env' /\
      EVERY (stmt_exprs_ok cenv) ss /\
      call_evaluation_safe cx (int_calls_stmts ss) /\
      frame_ret_ok_ptr d ctx PG func cx RetQ cenv ret_ty ==>
      stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
        (stmts_env cenv lctx ret_ty ss) (eval_stmts cx ss) es
End

Definition body_results_ptr_ok_def:
  body_results_ptr_ok cx [] = T /\
  body_results_ptr_ok cx (e::es) =
    (body_expr_ptr_ok cx e /\
     ((?s res t. eval_expr cx e s = (INL res, t)) ==>
      body_results_ptr_ok cx es))
End

Definition body_iterator_ptr_ok_def:
  body_iterator_ptr_ok cx (Array e) = body_expr_ptr_ok cx e /\
  body_iterator_ptr_ok cx (Range e1 e2) =
    (body_expr_ptr_ok cx e1 /\
     ((?s tv t s1 v t1. eval_expr cx e1 s = (INL tv, t) /\
                        read_result cx tv s1 = (INL v, t1)) ==>
      body_expr_ptr_ok cx e2))
End

Definition body_for_ptr_ok_def:
  body_for_ptr_ok cx (tyv : type_value) (nm : identifier) body (vs : eval_result list)
  <=>
    (?s v t. vs <> [] /\ read_result cx (HD vs) s = (INL v,t)) ==>
    body_stmts_ptr_ok cx body
End

Definition body_base_target_ptr_ok_def:
  body_base_target_ptr_ok cx (NameTarget id) = T /\
  body_base_target_ptr_ok cx (TopLevelNameTarget nid) = T /\
  body_base_target_ptr_ok cx (AttributeTarget t id) = body_base_target_ptr_ok cx t /\
  body_base_target_ptr_ok cx (SubscriptTarget t e) =
    (body_base_target_ptr_ok cx t /\
     ((?s pv s1. eval_base_place cx t s = (INL pv, s1)) ==>
      body_expr_ptr_ok cx e))
End

Definition body_tuple_target_ptr_ok_def:
  body_tuple_target_ptr_ok cx (BaseTarget t) (v : value) =
    body_base_target_ptr_ok cx t /\
  body_tuple_target_ptr_ok cx (TupleTarget gs) v =
    (!vs. v = ArrayV (TupleV vs) ==> body_tuple_targets_ptr_ok cx gs vs) /\
  body_tuple_targets_ptr_ok cx [] vs = T /\
  body_tuple_targets_ptr_ok cx (g::gs) [] = T /\
  body_tuple_targets_ptr_ok cx (g::gs) (v::vs) =
    (body_tuple_target_ptr_ok cx g v /\
     ((?s x t. assign_tuple_targets cx g v s = (INL x, t)) ==>
      body_tuple_targets_ptr_ok cx gs vs))
Termination
  WF_REL_TAC `measure (\x. case x of
    INL (_,t,_) => assignment_target_size t
  | INR (_,ts,_) => list_size assignment_target_size ts)` >>
  simp[assignment_target_size_def, list_size_def]
End
