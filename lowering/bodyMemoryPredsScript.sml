(* Reachability predicates for the additive memory body induction. *)
Theory bodyMemoryPreds
Ancestors
  stmtSimZero stmtSimPass stmtSimJumpMem gasContext
  bodyMemoryDefs bodyExprMemory stmtSimDefs
  bodySim exprSimHypsDefs supportedExprTraverse supportedStmtTraverse
  supportedStmts vyperTypeCallGraph
  vyperInterpreter vyperTypeSystem vyperState vyperAST list

val _ = Parse.hide "body";

(* A literal array's elements are memory-safe too, since membership and
   raw_log compile its elements without compiling the array; as
   bodySim's body_expr_ok. *)
Definition body_expr_mem_ok_mutual_def:
  (body_expr_mem_ok cx e <=>
    (!tops ctx func cenv env ty es.
      body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es ==>
      expr_sim_mem ctx func cenv cx ty e es /\
      expr_vv_sim_mem ctx func cenv cx ty e es) /\
    (!a t n elems.
      e = Builtin a (MakeArray t n) elems /\
      builtin_args_length_ok (MakeArray t n) (LENGTH elems) ==>
      body_exprs_mem_ok cx elems)) /\
  body_exprs_mem_ok cx [] = T /\
  body_exprs_mem_ok cx (e::es) =
    (body_expr_mem_ok cx e /\
     ((?s tv t s1 v t1. eval_expr cx e s = (INL tv, t) /\
                        read_result cx tv s1 = (INL v, t1)) ==>
      body_exprs_mem_ok cx es))
Termination
  WF_REL_TAC `measure (\x. case x of
      INL (_, e) => expr_size e
    | INR (_, es) => list_size expr_size es)` >>
  simp[expr_size_def]
End

Theorem body_expr_mem_ok_def = CONJUNCT1 body_expr_mem_ok_mutual_def;

Theorem body_exprs_mem_ok_def = CONJUNCT2 body_expr_mem_ok_mutual_def;

(* The elements of an array literal are memory-safe, by the literal's
   clause. *)
Theorem body_make_array_children_mem_ok:
  !cx a t n elems.
    body_expr_mem_ok cx (Builtin a (MakeArray t n) elems) /\
    builtin_args_length_ok (MakeArray t n) (LENGTH elems) ==>
    body_exprs_mem_ok cx elems
Proof
  rpt strip_tac >>
  qpat_x_assum `body_expr_mem_ok _ _`
    (mp_tac o CONJUNCT2 o ONCE_REWRITE_RULE [body_expr_mem_ok_def]) >>
  simp[]
QED

(* Introduction form of body_expr_mem_ok, as bodySim's body_expr_ok_intro:
   the array-literal clause first, then the simulation. *)
Theorem body_expr_mem_ok_intro:
  !cx e.
    (!a t n elems.
       e = Builtin a (MakeArray t n) elems /\
       builtin_args_length_ok (MakeArray t n) (LENGTH elems) ==>
       body_exprs_mem_ok cx elems) /\
    (!tops ctx func cenv env ty es.
       body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es ==>
       expr_sim_mem ctx func cenv cx ty e es /\
       expr_vv_sim_mem ctx func cenv cx ty e es) ==>
    body_expr_mem_ok cx e
Proof
  rpt strip_tac >> once_rewrite_tac[body_expr_mem_ok_def] >> metis_tac[]
QED

Definition body_stmt_mem_ok_def:
  body_stmt_mem_ok cx s <=>
    !d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
      body_inv tops ctx cenv cx /\ supported_stmt tops bindings s /\
      (!target. supported_stmt_expr_exists
         (expr_abi_decode_target_root target) s ==>
         occurs_abi_decode_target target tops) /\
      expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
      locals_alloc_ok cenv env /\
      type_stmt env ret_ty s = SOME env' /\ stmt_exprs_ok cenv s /\
      call_evaluation_safe cx (int_calls_stmt s) /\
      frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty ==>
      stmt_frag_mem d ctx func cx lctx RetQ cenv
        (stmt_env cenv lctx ret_ty s) (eval_stmt cx s) es
End

Definition body_stmts_mem_ok_def:
  body_stmts_mem_ok cx ss <=>
    !d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
      body_inv tops ctx cenv cx /\ supported_stmts tops bindings ss /\
      (!target. supported_stmts_expr_exists
         (expr_abi_decode_target_root target) ss ==>
         occurs_abi_decode_target target tops) /\
      expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
      locals_alloc_ok cenv env /\
      type_stmts env ret_ty ss = SOME env' /\
      stmts_exprs_ok cenv ss /\
      call_evaluation_safe cx (int_calls_stmts ss) /\
      frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty ==>
      stmt_frag_mem d ctx func cx lctx RetQ cenv
        (stmts_env cenv lctx ret_ty ss) (eval_stmts cx ss) es
End

Definition body_results_mem_ok_def:
  body_results_mem_ok cx [] = T /\
  body_results_mem_ok cx (e::es) =
    (body_expr_mem_ok cx e /\
     ((?s res t. eval_expr cx e s = (INL res, t)) ==>
      body_results_mem_ok cx es))
End

Definition body_iterator_mem_ok_def:
  body_iterator_mem_ok cx (Array e) = body_expr_mem_ok cx e /\
  body_iterator_mem_ok cx (Range e1 e2) =
    (body_expr_mem_ok cx e1 /\
     ((?s tv t s1 v t1. eval_expr cx e1 s = (INL tv, t) /\
                        read_result cx tv s1 = (INL v, t1)) ==>
      body_expr_mem_ok cx e2))
End

Definition body_for_mem_ok_def:
  body_for_mem_ok cx (tyv : type_value) (nm : identifier) body (vs : value list)
  <=> vs <> [] ==> body_stmts_mem_ok cx body
End

Definition body_base_target_mem_ok_def:
  body_base_target_mem_ok cx (NameTarget id) = T /\
  body_base_target_mem_ok cx (TopLevelNameTarget nid) = T /\
  body_base_target_mem_ok cx (AttributeTarget t id) = body_base_target_mem_ok cx t /\
  body_base_target_mem_ok cx (SubscriptTarget t e) =
    (body_base_target_mem_ok cx t /\
     ((?s pv s1. eval_base_place cx t s = (INL pv, s1)) ==>
      body_expr_mem_ok cx e))
End

Definition body_tuple_target_mem_ok_def:
  body_tuple_target_mem_ok cx (BaseTarget t) (v : value) =
    body_base_target_mem_ok cx t /\
  body_tuple_target_mem_ok cx (TupleTarget gs) v =
    (!vs. v = ArrayV (TupleV vs) ==> body_tuple_targets_mem_ok cx gs vs) /\
  body_tuple_targets_mem_ok cx [] vs = T /\
  body_tuple_targets_mem_ok cx (g::gs) [] = T /\
  body_tuple_targets_mem_ok cx (g::gs) (v::vs) =
    (body_tuple_target_mem_ok cx g v /\
     ((?s x t. assign_tuple_targets cx g v s = (INL x, t)) ==>
      body_tuple_targets_mem_ok cx gs vs))
Termination
  WF_REL_TAC `measure (\x. case x of
    INL (_,t,_) => assignment_target_size t
  | INR (_,ts,_) => list_size assignment_target_size ts)` >>
  simp[assignment_target_size_def, list_size_def]
End

Theorem body_bool_literal_mem_ok:
  !cx b. body_expr_mem_ok cx (Literal (BaseT BoolT) (BoolL b))
Proof
  simp[body_expr_mem_ok_def] >> metis_tac[body_bool_literal_mem]
QED

Theorem body_stmts_mem_projection:
  (!cx ss. body_stmts_mem_ok cx ss) ==>
  !d tops bindings ctx func cenv cx env env' ret_ty lctx RetQ ss es.
    body_inv tops ctx cenv cx /\ supported_stmts tops bindings ss /\
    (!target. supported_stmts_expr_exists
       (expr_abi_decode_target_root target) ss ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmts env ret_ty ss = SOME env' /\
    stmts_exprs_ok cenv ss /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmts_env cenv lctx ret_ty ss) (eval_stmts cx ss) es
Proof
  rw[body_stmts_mem_ok_def] >> metis_tac[]
QED

Theorem body_pass_mem_ok:
  !cx. body_stmt_mem_ok cx Pass
Proof
  rw[body_stmt_mem_ok_def] >>
  irule compile_pass_frag_mem
QED

Theorem body_nil_mem_ok:
  !cx. body_stmts_mem_ok cx []
Proof
  rw[body_stmts_mem_ok_def] >>
  irule stmt_frag_nil_mem
QED

Theorem body_break_mem_ok:
  !cx. body_stmt_mem_ok cx Break
Proof
  rw[body_stmt_mem_ok_def] >>
  Cases_on `lctx`
  >- simp[stmt_frag_mem_def, gas_admissible_def,
          Once evaluate_def, raise_def, stmt_res_ok_def] >>
  irule compile_break_frag_mem
QED

Theorem body_continue_mem_ok:
  !cx. body_stmt_mem_ok cx Continue
Proof
  rw[body_stmt_mem_ok_def] >>
  Cases_on `lctx`
  >- simp[stmt_frag_mem_def, gas_admissible_def,
          Once evaluate_def, raise_def, stmt_res_ok_def] >>
  irule compile_continue_frag_mem
QED

Theorem body_return_none_mem_ok:
  !cx. body_stmt_mem_ok cx (Return NONE)
Proof
  rw[body_stmt_mem_ok_def, frame_ret_ok_mem_def] >>
  first_x_assum irule >> simp[same_frame_refl] >>
  qexists_tac `env` >> simp[]
QED

(* Do not mistake these base cases and projection for the mutual theorem:
   the recursive producer cases remain separate obligations. *)
