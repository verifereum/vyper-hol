(* Full-body induction predicates for a linked contract and its active module. *)
Theory bodyFullPredsMods
Ancestors
  bodyCallSupport bodyFullPreds bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit bodySim
  exprSimHypsDefs exprSimMapDefs supportedStmts supportedProgram
  supportedExprTraverse allocLimits allocLimitsProps[qualified] placeTypingProps
  compileEnv exprLowering
  gasShadow gasContext bodySimFull vyperInterpreter vyperTypeSystem vyperTypeCallGraph
  vyperTypeCallStackSoundness vyperState vyperContext vyperAST
  vyperTypeInvariants vyperSubscriptOverlap constSubstCorrect constSubstMods
  constSubst list alist option pair finite_map

val _ = Parse.hide "body";

(* Constant cells and replacement evaluation agree at every qualified key. *)
Definition body_const_cells_agree_mods_def[nocompute]:
  body_const_cells_agree_mods mods cx env es <=>
    ?roots art imms.
      check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
      ALOOKUP cx.sources cx.txn.target = SOME mods /\
      frame_maps env art /\ env.type_defs = get_tenv cx /\
      imms = (case ALOOKUP es.immutables cx.txn.target of
                NONE => empty_immutables | SOME cells => cells) /\
      (!src tops. MEM (src,tops) mods ==>
        ?A. constants_fold_module mods imms src tops FEMPTY = SOME A /\
            A SUBMAP get_source_immutables src imms) /\
      (!addr src id tv root. MEM (addr,src,id,tv,root) roots ==>
        checked_frame_context cx mods art src id env) /\
      (!src id r. ALOOKUP (consts_env_mods mods) (src,id) = SOME r ==>
        declared_constant mods src id /\ constant_expr mods r /\
        vyperSubscriptOverlap$accesses_expr r = [] /\
        FLOOKUP env.bare_globals (src,id) = SOME (expr_type r) /\
        FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type (expr_type r)) /\
        (?pv v. const_result_at roots cx (expr_type r)
                  (PlaceR (ImmutablePlace src id [])) v /\
                const_result_at roots cx (expr_type r) pv v /\
                !st. const_cells_agree roots st ==>
                  lookup_global cx src id st =
                    (INL (PlaceR (ImmutablePlace src id [])),st) /\
                  eval_expr cx r st = (INL pv,st))) /\
      const_cells_agree roots es
End

Theorem body_const_cells_agree_mods_sources:
  body_const_cells_agree_mods mods cx env es ==>
  ALOOKUP cx.sources cx.txn.target = SOME mods
Proof
  simp[body_const_cells_agree_mods_def] >> metis_tac[]
QED

Theorem alookup_none_const_key[local]:
  !cs id. ALOOKUP (MAP (\(k,v). ((NONE,k),v)) cs) (NONE,id) = ALOOKUP cs id
Proof
  Induct >> simp[] >> PairCases >> simp[]
QED

Theorem body_const_cells_agree_mods_singleton:
  body_const_cells_agree_mods [(NONE,tops)] cx env es ==>
  body_const_cells_agree [(NONE,tops)] cx env es
Proof
  strip_tac >>
  qpat_x_assum `body_const_cells_agree_mods _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [body_const_cells_agree_mods_def]) >>
  `get_module_code cx NONE = SOME tops` by simp[get_module_code_def] >>
  `cx_tops cx = tops` by simp[cx_tops_def] >>
  qpat_x_assum `!src ts. MEM (src,ts) [(NONE,tops)] ==> _`
    (qspecl_then [`NONE`,`tops`] mp_tac) >> simp[] >> strip_tac >>
  rewrite_tac[body_const_cells_agree_def] >>
  qexistsl_tac [`roots`, `art`, `imms`, `A`] >> asm_rewrite_tac[] >>
  simp[const_subst_context_def] >> conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!addr src id tv root. MEM _ roots ==> _`
        (qspecl_then [`addr`, `src`, `id`, `tv`, `root`] mp_tac) >>
      simp[]) >>
  rpt gen_tac >> strip_tac >>
  `ALOOKUP [((NONE:num option),tops)] NONE = SOME tops` by simp[] >>
  `const_local_refs r = []` by
    (drule_all_then strip_assume_tac checked_module_consts_env_replacement >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!src id r. ALOOKUP (consts_env_mods _) _ = _ ==> _`
    (qspecl_then [`NONE`, `id`, `r`] mp_tac) >>
  PURE_REWRITE_TAC[consts_env_mods_singleton, alookup_none_const_key] >>
  impl_tac >- first_assum ACCEPT_TAC >>
  strip_tac >>
  qpat_x_assum `!st. const_cells_agree _ st ==> _ /\ _`
    (strip_assume_tac o SIMP_RULE bool_ss [IMP_CONJ_THM, FORALL_AND_THM]) >>
  asm_rewrite_tac[] >>
  qexists_tac `pv` >> asm_rewrite_tac[const_results_related_def] >>
  disj2_tac >> qexists_tac `v` >> asm_rewrite_tac[]
QED

Definition body_expr_full_ok_mods_def[nocompute]:
  (body_expr_full_ok_mods mods exps cx e <=>
    (!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
      contract_inv mods exps ctx cenv cx /\
      module_body_inv mods src tops cenv cx /\
      shadow_body_inv_mods mods exps ctx shadow_ctx /\
      body_const_cells_agree_mods mods cx env es /\
      expr_body_pre_mods mods cenv cx env e es ==>
      expr_sim_full_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cenv cx ty e es /\
      expr_vv_sim_full_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
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
      body_const_cells_agree_mods mods cx env es /\
      expr_map_pre_mods mods cenv cx env e es ==>
      expr_map_sim_full_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
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
      body_const_cells_agree_mods mods cx env es /\
      expr_sim_inv_mods mods cenv cx env es /\ ce_locals_declared cenv env /\
      locals_alloc_ok cenv env /\
      type_stmt env ret_ty s = SOME env' /\ stmt_exprs_ok cenv s /\
      ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env) s /\
      (!key. MEM (vyperSubscriptOverlap$WriteAcc (vyperSubscriptOverlap$StateRef key))
                  (vyperSubscriptOverlap$accesses_stmt s) /\
             IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
             IS_SOME (FLOOKUP cenv.ce_module_vars key)) /\
      call_evaluation_safe cx (int_calls_stmt s) /\
      frame_ret_ok_full_mods mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cx RetQ cenv ret_ty ==>
      stmt_frag_full_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cx lctx RetQ cenv
        (stmt_env cenv lctx ret_ty s)
        (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt s))
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
      body_const_cells_agree_mods mods cx env es /\
      expr_sim_inv_mods mods cenv cx env es /\ ce_locals_declared cenv env /\
      locals_alloc_ok cenv env /\
      type_stmts env ret_ty ss = SOME env' /\
      stmts_exprs_ok cenv ss /\
      ~supported_stmts_expr_exists (unallocated_bare_global_root cenv env) ss /\
      (!key. MEM (vyperSubscriptOverlap$WriteAcc (vyperSubscriptOverlap$StateRef key))
                  (vyperSubscriptOverlap$accesses_stmts ss) /\
             IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
             IS_SOME (FLOOKUP cenv.ce_module_vars key)) /\
      call_evaluation_safe cx (int_calls_stmts ss) /\
      frame_ret_ok_full_mods mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cx RetQ cenv ret_ty ==>
      stmt_frag_full_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cx lctx RetQ cenv
        (stmts_env cenv lctx ret_ty ss)
        (stmts_env (gas_shadow_env T cenv) lctx ret_ty (MAP gas_shadow_stmt ss))
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

Theorem expr_body_pre_mods_map_subscript_base:
  !mods cenv cx env ann obj idx kt vt es.
    expr_body_pre_mods mods cenv cx env (Subscript ann obj idx) es /\
    place_type cenv obj = MapPT kt vt ==>
    expr_map_pre_mods mods cenv cx env obj es
Proof
  rpt gen_tac >> strip_tac >>
  `place_map_tables_agree_on_defined cenv env /\
   (!nsid ty. FLOOKUP env.bare_globals nsid = SOME ty ==>
              cenv.ce_hashmap_info nsid = NONE)` by
    gvs[expr_body_pre_mods_def, expr_sim_inv_mods_def] >>
  gvs[expr_body_pre_mods_def, Once well_typed_expr_def,
      byte_widths_expr_def, alloc_limits_expr_def, int_calls_expr_def,
      expr_has_evm_run_thm, EVERY_APPEND] >>
  (* the value-typed base contradicts the map place type, slot base or not *)
  TRY (drule_all place_type_well_typed_on_defined >> simp[] >> NO_TAC) >>
  drule_all place_type_checked_place_on_defined >> strip_tac >>
  rename1 `type_place_expr env obj = SOME bty` >>
  Cases_on `bty` >> gvs[value_type_place_def] >>
  drule_then assume_tac allocLimitsPropsTheory.type_place_hashmap_not_array_slot_base >>
  gvs[] >>
  simp[expr_map_pre_mods_def] >>
  gvs[supported_expr_exists_def] >>
  metis_tac[call_evaluation_safe_append_left]
QED
