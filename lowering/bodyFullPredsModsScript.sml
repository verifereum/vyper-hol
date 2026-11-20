(* Full-body induction predicates for a linked contract and its active module. *)
Theory bodyFullPredsMods
Ancestors
  bodyFullPreds bodyFullShadowBodyInv bodyInvSplit bodySimFull bodySim
  exprSimHypsDefs exprSimMapDefs supportedStmts supportedProgram
  supportedExprTraverse allocLimits placeTypingProps compileEnv exprLowering
  gasShadow gasContext vyperInterpreter vyperTypeSystem vyperTypeCallGraph
  vyperTypeCallStackSoundness vyperState vyperContext vyperAST
  vyperTypeInvariants list alist option pair finite_map

val _ = Parse.hide "body";

Definition body_expr_full_ok_mods_def[nocompute]:
  (body_expr_full_ok_mods mods exps cx e <=>
    (!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
      contract_inv mods exps ctx cenv cx /\
      module_body_inv mods src tops cenv cx /\
      shadow_body_inv_mods mods exps ctx shadow_ctx /\
      expr_body_pre_mods mods cenv cx env e es ==>
      expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cenv cx ty e es /\
      expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cenv cx ty e es) /\
    (!a t n elems.
      e = Builtin a (MakeArray t n) elems /\
      builtin_args_length_ok (MakeArray t n) (LENGTH elems) ==>
      body_exprs_full_ok_mods mods exps cx elems) /\
    (!ann e1 e2 DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
      e = Subscript ann e1 e2 /\
      contract_inv mods exps ctx cenv cx /\
      module_body_inv mods src tops cenv cx /\
      shadow_body_inv_mods mods exps ctx shadow_ctx /\
      expr_map_pre_mods mods cenv cx env e es ==>
      expr_map_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cenv cx ty e es)) /\
  body_exprs_full_ok_mods mods exps cx [] = T /\
  body_exprs_full_ok_mods mods exps cx (e::es) =
    (body_expr_full_ok_mods mods exps cx e /\
     ((?s tv t s1 v t1. eval_expr cx e s = (INL tv, t) /\
                        read_result cx tv s1 = (INL v, t1)) ==>
      body_exprs_full_ok_mods mods exps cx es))
Termination
  WF_REL_TAC `measure (\x. case x of
      INL (_, _, _, e) => expr_size e
    | INR (_, _, _, es) => list_size expr_size es)` >>
  simp[expr_size_def]
End

Definition body_stmt_full_ok_mods_def[nocompute]:
  body_stmt_full_ok_mods mods exps cx s <=>
    !DF lo d PG src tops bindings ctx shadow_ctx func shadow_func cenv env
       env' ret_ty lctx RetQ es.
      contract_inv mods exps ctx cenv cx /\
      module_body_inv mods src tops cenv cx /\
      shadow_body_inv_mods mods exps ctx shadow_ctx /\
      supported_stmt tops bindings s /\
      (!target. supported_stmt_expr_exists
         (expr_abi_decode_target_root target) s ==>
         EXISTS (occurs_abi_decode_target target o SND) mods) /\
      expr_sim_inv_mods mods cenv cx env es /\ ce_locals_declared cenv env /\
      locals_alloc_ok cenv env /\
      type_stmt env ret_ty s = SOME env' /\ stmt_exprs_ok cenv s /\
      call_evaluation_safe cx (int_calls_stmt s) /\
      frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cx RetQ cenv ret_ty ==>
      stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cx lctx RetQ cenv
        (stmt_env cenv lctx ret_ty s)
        (stmt_env cenv lctx ret_ty (gas_shadow_stmt s))
        (eval_stmt cx s) es
End

Definition body_stmts_full_ok_mods_def[nocompute]:
  body_stmts_full_ok_mods mods exps cx ss <=>
    !DF lo d PG src tops bindings ctx shadow_ctx func shadow_func cenv env
       env' ret_ty lctx RetQ es.
      contract_inv mods exps ctx cenv cx /\
      module_body_inv mods src tops cenv cx /\
      shadow_body_inv_mods mods exps ctx shadow_ctx /\
      supported_stmts tops bindings ss /\
      (!target. supported_stmts_expr_exists
         (expr_abi_decode_target_root target) ss ==>
         EXISTS (occurs_abi_decode_target target o SND) mods) /\
      expr_sim_inv_mods mods cenv cx env es /\ ce_locals_declared cenv env /\
      locals_alloc_ok cenv env /\
      type_stmts env ret_ty ss = SOME env' /\
      stmts_exprs_ok cenv ss /\
      call_evaluation_safe cx (int_calls_stmts ss) /\
      frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cx RetQ cenv ret_ty ==>
      stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cx lctx RetQ cenv
        (stmts_env cenv lctx ret_ty ss)
        (stmts_env cenv lctx ret_ty (MAP gas_shadow_stmt ss))
        (eval_stmts cx ss) es
End

Definition body_results_full_ok_mods_def[nocompute]:
  body_results_full_ok_mods mods exps cx [] = T /\
  body_results_full_ok_mods mods exps cx (e::es) =
    (body_expr_full_ok_mods mods exps cx e /\
     ((?s res t. eval_expr cx e s = (INL res, t)) ==>
      body_results_full_ok_mods mods exps cx es))
End

Definition body_iterator_full_ok_mods_def[nocompute]:
  body_iterator_full_ok_mods mods exps cx (Array e) =
    body_expr_full_ok_mods mods exps cx e /\
  body_iterator_full_ok_mods mods exps cx (Range e1 e2) =
    (body_expr_full_ok_mods mods exps cx e1 /\
     ((?s tv t s1 v t1. eval_expr cx e1 s = (INL tv, t) /\
                        read_result cx tv s1 = (INL v, t1)) ==>
      body_expr_full_ok_mods mods exps cx e2))
End

Definition body_for_full_ok_mods_def[nocompute]:
  body_for_full_ok_mods mods exps cx (tyv : type_value) (nm : identifier)
    body (vs : eval_result list) <=>
    (?s v t. vs <> [] /\ read_result cx (HD vs) s = (INL v,t)) ==>
    body_stmts_full_ok_mods mods exps cx body
End

Definition body_base_target_full_ok_mods_def[nocompute]:
  body_base_target_full_ok_mods mods exps cx (NameTarget id) = T /\
  body_base_target_full_ok_mods mods exps cx (TopLevelNameTarget nid) = T /\
  body_base_target_full_ok_mods mods exps cx (AttributeTarget t id) =
    body_base_target_full_ok_mods mods exps cx t /\
  body_base_target_full_ok_mods mods exps cx (SubscriptTarget t e) =
    (body_base_target_full_ok_mods mods exps cx t /\
     ((?s pv s1. eval_base_place cx t s = (INL pv, s1)) ==>
      body_expr_full_ok_mods mods exps cx e))
End

Definition body_tuple_target_full_ok_mods_def[nocompute]:
  body_tuple_target_full_ok_mods mods exps cx (BaseTarget t) (v : value) =
    body_base_target_full_ok_mods mods exps cx t /\
  body_tuple_target_full_ok_mods mods exps cx (TupleTarget gs) v =
    (!vs. v = ArrayV (TupleV vs) ==>
          body_tuple_targets_full_ok_mods mods exps cx gs vs) /\
  body_tuple_targets_full_ok_mods mods exps cx [] vs = T /\
  body_tuple_targets_full_ok_mods mods exps cx (g::gs) [] = T /\
  body_tuple_targets_full_ok_mods mods exps cx (g::gs) (v::vs) =
    (body_tuple_target_full_ok_mods mods exps cx g v /\
     ((?s x t. assign_tuple_targets cx g v s = (INL x, t)) ==>
      body_tuple_targets_full_ok_mods mods exps cx gs vs))
Termination
  WF_REL_TAC `measure (\x. case x of
    INL (_,_,_,t,_) => assignment_target_size t
  | INR (_,_,_,ts,_) => list_size assignment_target_size ts)` >>
  simp[assignment_target_size_def, list_size_def]
End

Theorem body_exprs_full_ok_mods_def =
  CONJUNCT2 body_expr_full_ok_mods_def;

Theorem body_expr_full_ok_mods_singleton:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
  (!e. body_expr_full_ok_mods [(NONE,tops)] [] cx e <=>
         body_expr_full_ok cx e) /\
  (!es. body_exprs_full_ok_mods [(NONE,tops)] [] cx es <=>
         body_exprs_full_ok cx es)
Proof
  cheat
QED

Theorem body_stmt_full_ok_mods_singleton:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
  (body_stmt_full_ok_mods [(NONE,tops)] [] cx s <=>
     body_stmt_full_ok cx s)
Proof
  cheat
QED

Theorem body_stmts_full_ok_mods_singleton:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
  (body_stmts_full_ok_mods [(NONE,tops)] [] cx ss <=>
     body_stmts_full_ok cx ss)
Proof
  cheat
QED

Theorem body_results_full_ok_mods_singleton:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
  (body_results_full_ok_mods [(NONE,tops)] [] cx es <=>
     body_results_full_ok cx es)
Proof
  cheat
QED

Theorem body_iterator_full_ok_mods_singleton:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
  (body_iterator_full_ok_mods [(NONE,tops)] [] cx it <=>
     body_iterator_full_ok cx it)
Proof
  cheat
QED

Theorem body_for_full_ok_mods_singleton:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
  (body_for_full_ok_mods [(NONE,tops)] [] cx tyv nm body vs <=>
     body_for_full_ok cx tyv nm body vs)
Proof
  cheat
QED

Theorem body_base_target_full_ok_mods_singleton:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
  (body_base_target_full_ok_mods [(NONE,tops)] [] cx t <=>
     body_base_target_full_ok cx t)
Proof
  cheat
QED

Theorem body_tuple_target_full_ok_mods_singleton:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
  (!g v. body_tuple_target_full_ok_mods [(NONE,tops)] [] cx g v <=>
         body_tuple_target_full_ok cx g v) /\
  (!gs vs. body_tuple_targets_full_ok_mods [(NONE,tops)] [] cx gs vs <=>
         body_tuple_targets_full_ok cx gs vs)
Proof
  cheat
QED

Theorem expr_body_pre_mods_map_subscript_base:
  !mods cenv cx env ann obj idx kt vt es.
    expr_body_pre_mods mods cenv cx env (Subscript ann obj idx) es /\
    place_type cenv obj = MapPT kt vt ==>
    expr_map_pre_mods mods cenv cx env obj es
Proof
  cheat
QED
