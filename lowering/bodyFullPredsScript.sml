(*
 * The predicates of the full body induction (bodySimFullMain): bodyPtrPredsAt's
 * eleven body_*_ptr_ok_at over bodySimFull's joint judgments (expr_sim_full,
 * expr_vv_sim_full, stmt_frag_full, frame_ret_ok_full), whose source GAS
 * marks, target execution, memory posts and pointer ghosts share one
 * witness.  The shadow side compiles the gas_shadow_* image of the same
 * statement or expression.  One induction covers runtime frames and
 * constructor frames alike: the horizon-indexed dead mask DF and the bound are quantified.
 *
 * TOP-LEVEL:
 *   body_expr_full_ok, body_stmt_full_ok, body_stmts_full_ok,
 *   body_exprs_full_ok, body_results_full_ok, body_iterator_full_ok,
 *   body_for_full_ok, body_base_target_full_ok,
 *   body_tuple_target_full_ok, body_tuple_targets_full_ok
 *)
Theory bodyFullPreds
Ancestors bodyFullShadowBodyInv
  constSubstCorrect constSubstStmts vyperCallOutcomeFrame gasContext
  bodySimFull gasShadow bodySim exprSimHypsDefs supportedStmts
  vyperInterpreter vyperTypeSystem vyperState vyperAST list
  vyperTypeContract vyperTypeConstantFold alist finite_map

val _ = Parse.hide "body";

Definition body_const_cells_agree_def:
  body_const_cells_agree mods cx env es <=>
    ?roots art imms A.
      check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
      ALOOKUP cx.sources cx.txn.target = SOME mods /\
      ALOOKUP mods NONE = SOME (cx_tops cx) /\
      constants_fold_module mods imms NONE (cx_tops cx) FEMPTY = SOME A /\
      frame_maps env art /\
      const_subst_context roots cx env (module_consts_env (cx_tops cx) [])
        mods art /\
      const_cells_agree roots es
End

Theorem body_const_cells_agree_immutables:
  st.immutables = st'.immutables ==>
  (body_const_cells_agree mods cx env st <=>
   body_const_cells_agree mods cx env st')
Proof
  simp[body_const_cells_agree_def, const_cells_agree_def]
QED

Theorem body_const_cells_agree_state_updates[simp]:
  (body_const_cells_agree mods cx env (st with gas_obs := obs) =
   body_const_cells_agree mods cx env st) /\
  (body_const_cells_agree mods cx env (st with scopes := scopes) =
   body_const_cells_agree mods cx env st) /\
  (body_const_cells_agree mods cx env (st with outcomes := outcomes) =
   body_const_cells_agree mods cx env st) /\
  (body_const_cells_agree mods cx env (st with requests := requests) =
   body_const_cells_agree mods cx env st)
Proof
  rpt conj_tac >> irule body_const_cells_agree_immutables >> simp[]
QED

Theorem body_const_cells_agree_expr:
  body_const_cells_agree mods cx env st /\
  (well_typed_expr env e \/ IS_SOME (type_place_expr env e)) /\
  eval_expr cx e st = (res,st') ==>
  body_const_cells_agree mods cx env st'
Proof
  rw[body_const_cells_agree_def] >>
  qexistsl_tac [`roots`, `art`, `imms`, `A`] >> simp[] >>
  metis_tac[const_subst_context_expr_frame]
QED

Theorem body_const_cells_agree_exprs:
  body_const_cells_agree mods cx env st /\
  well_typed_exprs env es /\ eval_exprs cx es st = (res,st') ==>
  body_const_cells_agree mods cx env st'
Proof
  rw[body_const_cells_agree_def] >>
  qexistsl_tac [`roots`, `art`, `imms`, `A`] >> simp[] >>
  metis_tac[const_subst_context_exprs_frame]
QED

Theorem body_const_cells_agree_base:
  body_const_cells_agree mods cx env st /\
  IS_SOME (type_place_target env bt) /\
  eval_base_place cx bt st = (res,st') ==>
  body_const_cells_agree mods cx env st'
Proof
  rw[body_const_cells_agree_def] >>
  qexistsl_tac [`roots`, `art`, `imms`, `A`] >> simp[] >>
  metis_tac[const_subst_context_base_frame]
QED

Theorem body_const_cells_agree_read:
  body_const_cells_agree mods cx env st /\
  read_result cx pv st = (res,st') ==>
  body_const_cells_agree mods cx env st'
Proof
  rw[body_const_cells_agree_def] >>
  qexistsl_tac [`roots`, `art`, `imms`, `A`] >> simp[] >>
  irule protected_cell_frame_cells_agree >>
  qexists_tac `st` >> simp[] >> rpt strip_tac >>
  mp_tac (CONJUNCT1 protected_cell_frame_reads) >>
  simp[state_rel_frame_result] >> disch_then drule >> simp[]
QED

Theorem body_const_cells_agree_expr_read:
  body_const_cells_agree mods cx env st /\
  (well_typed_expr env e \/ IS_SOME (type_place_expr env e)) /\
  bind (eval_expr cx e) (read_result cx) st = (res,st') ==>
  body_const_cells_agree mods cx env st'
Proof
  strip_tac >>
  Cases_on `eval_expr cx e st` >> Cases_on `q` >> fs[bind_def] >>
  metis_tac[body_const_cells_agree_expr, body_const_cells_agree_read]
QED

Theorem body_const_cells_agree_frame[local]:
  body_const_cells_agree mods cx env st /\
  (!art addr src id.
     checked_frame_context cx mods art src id env ==>
     protected_cell_frame addr src id st st') ==>
  body_const_cells_agree mods cx env st'
Proof
  rw[body_const_cells_agree_def] >>
  qexistsl_tac [`roots`, `art`, `imms`, `A`] >> simp[] >>
  irule protected_cell_frame_cells_agree >>
  qexists_tac `st` >> simp[] >>
  rpt strip_tac >>
  qpat_assum `const_subst_context _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [const_subst_context_def]) >>
  metis_tac[]
QED

Theorem body_const_cells_agree_target:
  body_const_cells_agree mods cx env st /\
  IS_SOME (type_place_target env bt) /\
  eval_target_place cx bt st = (res,st') ==>
  body_const_cells_agree mods cx env st'
Proof
  strip_tac >> irule body_const_cells_agree_frame >>
  qexists_tac `st` >> simp[] >>
  metis_tac[cj 8 checked_protected_cell_frame_mutual]
QED

Theorem body_const_cells_agree_assign_tuple:
  body_const_cells_agree mods cx env st /\
  writable_atarget env g /\ assign_tuple_targets cx g v st = (res,st') ==>
  body_const_cells_agree mods cx env st'
Proof
  strip_tac >> irule body_const_cells_agree_frame >>
  qexists_tac `st` >> simp[] >>
  metis_tac[cj 9 checked_protected_cell_frame_mutual]
QED

Theorem body_const_cells_agree_stmt:
  body_const_cells_agree mods cx env st /\
  type_stmt env ret s = SOME env' /\ eval_stmt cx s st = (res,st') ==>
  body_const_cells_agree mods cx env' st'
Proof
  strip_tac >>
  `body_const_cells_agree mods cx env st'` by
    (irule body_const_cells_agree_frame >> qexists_tac `st` >> simp[] >>
     metis_tac[cj 1 checked_protected_cell_frame_mutual, optionTheory.IS_SOME_DEF]) >>
  qpat_x_assum `body_const_cells_agree mods cx env st'`
    (strip_assume_tac o REWRITE_RULE [body_const_cells_agree_def]) >>
  pure_once_rewrite_tac [body_const_cells_agree_def] >>
  qexistsl_tac [`roots`, `art`, `imms`, `A`] >> simp[] >>
  metis_tac[const_subst_context_type_stmt, type_stmt_frame_maps]
QED

Theorem body_const_cells_agree_stmts:
  body_const_cells_agree mods cx env st /\
  IS_SOME (type_stmts env ret ss) /\ eval_stmts cx ss st = (res,st') ==>
  body_const_cells_agree mods cx env st'
Proof
  strip_tac >> irule body_const_cells_agree_frame >>
  qexists_tac `st` >> simp[] >>
  metis_tac[cj 2 checked_protected_cell_frame_mutual]
QED

Theorem body_const_cells_agree_iterator:
  body_const_cells_agree mods cx env st /\
  well_typed_iterator env ty it /\ eval_iterator cx it st = (res,st') ==>
  body_const_cells_agree mods cx env st'
Proof
  strip_tac >> irule body_const_cells_agree_frame >>
  qexists_tac `st` >> simp[] >>
  metis_tac[cj 3 checked_protected_cell_frame_mutual]
QED

Theorem body_const_cells_agree_extend_local[simp]:
  body_const_cells_agree mods cx (extend_local env nm ty b) st <=>
  body_const_cells_agree mods cx env st
Proof
  simp[body_const_cells_agree_def] >> EQ_TAC >> strip_tac >>
  qexistsl_tac [`roots`, `art`, `imms`, `A`] >> simp[] >>
  irule const_subst_context_static >>
  first_assum (irule_at Any) >> simp[extend_local_def]
QED

Theorem body_const_cells_agree_stk:
  body_const_cells_agree mods cx env st ==>
  body_const_cells_agree mods (cx with stk := stk) env st
Proof
  rw[body_const_cells_agree_def, cx_tops_stk] >>
  qexistsl_tac [`roots`, `art`, `imms`, `A`] >> simp[] >>
  irule const_subst_context_stk >> simp[] >>
  qpat_assum `const_subst_context _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [const_subst_context_def]) >>
  metis_tac[]
QED

Theorem body_const_cells_agree_current_src:
  body_const_cells_agree mods cx env st ==>
  body_const_cells_agree mods cx (env with current_src := src) st
Proof
  rw[body_const_cells_agree_def] >>
  qexistsl_tac [`roots`, `art`, `imms`, `A`] >> simp[] >>
  conj_tac
  >- (qpat_assum `frame_maps env art`
        (strip_assume_tac o REWRITE_RULE [frame_maps_def]) >>
      simp[frame_maps_def]) >>
  irule const_subst_context_static >> qexists_tac `env` >> simp[]
QED

(* As bodySim's body_expr_ok, a literal array's elements are ok too. *)
Definition body_expr_full_ok_def:
  (body_expr_full_ok cx e <=>
    (!DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es.
      body_inv tops ctx cenv cx /\
      shadow_body_inv tops ctx shadow_ctx /\
      body_const_cells_agree [(NONE,tops)] cx env es /\
      expr_body_pre cenv cx env e es ==>
      expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cenv cx ty e es /\
      expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cenv cx ty e es) /\
    ((!a t n elems.
       e = Builtin a (MakeArray t n) elems /\
       builtin_args_length_ok (MakeArray t n) (LENGTH elems) ==>
       body_exprs_full_ok cx elems) /\
     (!t c a b.
       e = IfExp t c a b ==>
       body_expr_full_ok cx c /\
       ((?s tv s'. eval_expr cx c s = (INL tv, s')) ==>
        body_expr_full_ok cx a /\ body_expr_full_ok cx b))) /\
    (!ann e1 e2 DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es.
      e = Subscript ann e1 e2 /\
      body_inv tops ctx cenv cx /\
      shadow_body_inv tops ctx shadow_ctx /\
      body_const_cells_agree [(NONE,tops)] cx env es /\
      expr_map_pre cenv cx env e es ==>
      expr_map_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cenv cx ty e es)) /\
  body_exprs_full_ok cx [] = T /\
  body_exprs_full_ok cx (e::es) =
    (body_expr_full_ok cx e /\
     ((?s tv t s1 v t1. eval_expr cx e s = (INL tv, t) /\
                        read_result cx tv s1 = (INL v, t1)) ==>
      body_exprs_full_ok cx es))
Termination
  WF_REL_TAC `measure (\x. case x of
      INL (_, e) => expr_size e
    | INR (_, es) => list_size expr_size es)` >>
  simp[expr_size_def]
End

Theorem body_exprs_full_ok_def = CONJUNCT2 body_expr_full_ok_def;

(* The elements of an array literal are ok, by the literal's clause. *)
Theorem body_make_array_children_full_ok:
  !cx a t n elems.
    body_expr_full_ok cx (Builtin a (MakeArray t n) elems) /\
    builtin_args_length_ok (MakeArray t n) (LENGTH elems) ==>
    body_exprs_full_ok cx elems
Proof
  rpt strip_tac >>
  qpat_x_assum `body_expr_full_ok _ _`
    (mp_tac o CONJUNCT1 o CONJUNCT1 o CONJUNCT2 o
      ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
  simp[]
QED

(* A conditional's test is ok, and its arms are when the test evaluates. *)
Theorem body_ifexp_children_full_ok:
  !cx t c a b.
    body_expr_full_ok cx (IfExp t c a b) ==>
    body_expr_full_ok cx c /\
    ((?s tv s'. eval_expr cx c s = (INL tv, s')) ==>
     body_expr_full_ok cx a /\ body_expr_full_ok cx b)
Proof
  rpt gen_tac >>
  disch_then (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
  qpat_x_assum `!t' c' a' b'. IfExp _ _ _ _ = IfExp t' c' a' b' ==> _`
    (qspecl_then [`t`, `c`, `a`, `b`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Definition body_stmt_full_ok_def:
  body_stmt_full_ok cx s <=>
    !DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env
       env' ret_ty lctx RetQ es.
      body_inv tops ctx cenv cx /\
      shadow_body_inv tops ctx shadow_ctx /\
      supported_stmt tops bindings s /\
      (!target. supported_stmt_expr_exists
         (expr_abi_decode_target_root target) s ==>
         occurs_abi_decode_target target tops) /\
      body_const_cells_agree [(NONE,tops)] cx env es /\
      expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
      locals_alloc_ok cenv env /\
      type_stmt env ret_ty s = SOME env' /\ stmt_exprs_ok cenv s /\
      call_evaluation_safe cx (int_calls_stmt s) /\
      frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cx RetQ cenv ret_ty ==>
      stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cx lctx RetQ cenv
        (stmt_env cenv lctx ret_ty s)
        (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt s))
        (eval_stmt cx s) es
End

Definition body_stmts_full_ok_def:
  body_stmts_full_ok cx ss <=>
    !DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env
       env' ret_ty lctx RetQ es.
      body_inv tops ctx cenv cx /\
      shadow_body_inv tops ctx shadow_ctx /\
      supported_stmts tops bindings ss /\
      (!target. supported_stmts_expr_exists
         (expr_abi_decode_target_root target) ss ==>
         occurs_abi_decode_target target tops) /\
      body_const_cells_agree [(NONE,tops)] cx env es /\
      expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
      locals_alloc_ok cenv env /\
      type_stmts env ret_ty ss = SOME env' /\
      stmts_exprs_ok cenv ss /\
      call_evaluation_safe cx (int_calls_stmts ss) /\
      frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cx RetQ cenv ret_ty ==>
      stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cx lctx RetQ cenv
        (stmts_env cenv lctx ret_ty ss)
        (stmts_env (gas_shadow_env T cenv) lctx ret_ty (MAP gas_shadow_stmt ss))
        (eval_stmts cx ss) es
End

Definition body_results_full_ok_def:
  body_results_full_ok cx [] = T /\
  body_results_full_ok cx (e::es) =
    (body_expr_full_ok cx e /\
     ((?s res t. eval_expr cx e s = (INL res, t)) ==>
      body_results_full_ok cx es))
End

Definition body_iterator_full_ok_def:
  body_iterator_full_ok cx (Array e) = body_expr_full_ok cx e /\
  body_iterator_full_ok cx (Range e1 e2) =
    (body_expr_full_ok cx e1 /\
     ((?s tv t s1 v t1. eval_expr cx e1 s = (INL tv, t) /\
                        read_result cx tv s1 = (INL v, t1)) ==>
      body_expr_full_ok cx e2))
End

Definition body_for_full_ok_def:
  body_for_full_ok cx (tyv : type_value) (nm : identifier) body (vs : eval_result list)
  <=>
    (?s v t. vs <> [] /\ read_result cx (HD vs) s = (INL v,t)) ==>
    body_stmts_full_ok cx body
End

Definition body_base_target_full_ok_def:
  body_base_target_full_ok cx (NameTarget id) = T /\
  body_base_target_full_ok cx (TopLevelNameTarget nid) = T /\
  body_base_target_full_ok cx (AttributeTarget t id) = body_base_target_full_ok cx t /\
  body_base_target_full_ok cx (SubscriptTarget t e) =
    (body_base_target_full_ok cx t /\
     ((?s pv s1. eval_base_place cx t s = (INL pv, s1)) ==>
      body_expr_full_ok cx e))
End

Definition body_tuple_target_full_ok_def:
  body_tuple_target_full_ok cx (BaseTarget t) (v : value) =
    body_base_target_full_ok cx t /\
  body_tuple_target_full_ok cx (TupleTarget gs) v =
    (!vs. v = ArrayV (TupleV vs) ==> body_tuple_targets_full_ok cx gs vs) /\
  body_tuple_targets_full_ok cx [] vs = T /\
  body_tuple_targets_full_ok cx (g::gs) [] = T /\
  body_tuple_targets_full_ok cx (g::gs) (v::vs) =
    (body_tuple_target_full_ok cx g v /\
     ((?s x t. assign_tuple_targets cx g v s = (INL x, t)) ==>
      body_tuple_targets_full_ok cx gs vs))
Termination
  WF_REL_TAC `measure (\x. case x of
    INL (_,t,_) => assignment_target_size t
  | INR (_,ts,_) => list_size assignment_target_size ts)` >>
  simp[assignment_target_size_def, list_size_def]
End
