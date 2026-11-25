(* Full-body induction predicates for a linked contract and its active module. *)
Theory bodyFullPredsMods
Ancestors
  bodyCallSupport bodyFullPreds bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit bodySim
  exprSimHypsDefs exprSimMapDefs supportedStmts supportedProgram
  supportedExprTraverse allocLimits allocLimitsProps[qualified] placeTypingProps
  compileEnv exprLowering
  gasShadow gasContext bodySimFull vyperInterpreter vyperTypeSystem vyperTypeCallGraph
  vyperTypeCallStackSoundness vyperState vyperContext vyperAST
  vyperTypeInvariants list alist option pair finite_map

val _ = Parse.hide "body";

Definition body_expr_full_ok_mods_def[nocompute]:
  (body_expr_full_ok_mods mods exps cx e <=>
    (!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
      contract_inv mods exps ctx cenv cx /\
      module_body_inv mods src tops cenv cx /\
      shadow_body_inv_mods mods exps ctx shadow_ctx /\
      body_const_cells_agree mods cx env es /\
      expr_body_pre_mods mods cenv cx env e es ==>
      expr_sim_full_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cenv cx ty e es /\
      expr_vv_sim_full_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cenv cx ty e es) /\
    ((!a t n elems.
       e = Builtin a (MakeArray t n) elems /\
       builtin_args_length_ok (MakeArray t n) (LENGTH elems) ==>
       body_exprs_full_ok_mods mods exps cx elems) /\
     (!t c a b.
       e = IfExp t c a b ==>
       body_expr_full_ok_mods mods exps cx c /\
       ((?s tv s'. eval_expr cx c s = (INL tv, s')) ==>
        body_expr_full_ok_mods mods exps cx a /\
        body_expr_full_ok_mods mods exps cx b))) /\
    (!ann e1 e2 DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
      e = Subscript ann e1 e2 /\
      contract_inv mods exps ctx cenv cx /\
      module_body_inv mods src tops cenv cx /\
      shadow_body_inv_mods mods exps ctx shadow_ctx /\
      body_const_cells_agree mods cx env es /\
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
      body_const_cells_agree mods cx env es /\
      expr_sim_inv_mods mods cenv cx env es /\ ce_locals_declared cenv env /\
      locals_alloc_ok cenv env /\
      type_stmt env ret_ty s = SOME env' /\ stmt_exprs_ok cenv s /\
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
      body_const_cells_agree mods cx env es /\
      expr_sim_inv_mods mods cenv cx env es /\ ce_locals_declared cenv env /\
      locals_alloc_ok cenv env /\
      type_stmts env ret_ty ss = SOME env' /\
      stmts_exprs_ok cenv ss /\
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

(* A conditional's test is ok, and its arms are when the test evaluates. *)
Theorem body_ifexp_children_full_ok_mods:
  !mods exps cx t c a b.
    body_expr_full_ok_mods mods exps cx (IfExp t c a b) ==>
    body_expr_full_ok_mods mods exps cx c /\
    ((?s tv s'. eval_expr cx c s = (INL tv, s')) ==>
     body_expr_full_ok_mods mods exps cx a /\
     body_expr_full_ok_mods mods exps cx b)
Proof
  rpt gen_tac >>
  disch_then (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  qpat_x_assum `!t' c' a' b'. IfExp _ _ _ _ = IfExp t' c' a' b' ==> _`
    (qspecl_then [`t`, `c`, `a`, `b`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem contract_inv_singleton_pins[local]:
  contract_inv [(NONE,tops)] [] ctx cenv cx ==>
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
  cenv.ce_modules = [(NONE,tops)] /\
  immutable_section_layout_mods [(NONE,tops)] cenv /\
  cx_tops cx = tops
Proof
  simp[contract_inv_def, cenv_module_pins_mods_def] >>
  strip_tac >> simp[cx_tops_def, get_module_code_def, ALOOKUP_def]
QED

Theorem contract_inv_singleton_guard[local]:
  (contract_inv [(NONE,tops)] [] ctx cenv cx ==> P) <=>
  (contract_inv [(NONE,tops)] [] ctx cenv cx ==>
   cenv.ce_modules = [(NONE,tops)] ==> cx_tops cx = tops ==>
   immutable_section_layout_mods [(NONE,tops)] cenv ==> P)
Proof
  metis_tac[contract_inv_singleton_pins]
QED

Theorem body_inv_singleton[local]:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
  !ts ctx cenv. body_inv ts ctx cenv cx <=>
    ts = tops /\ contract_inv [(NONE,tops)] [] ctx cenv cx /\
    cenv.ce_module = NONE
Proof
  strip_tac >> rpt gen_tac >>
  `!ts. contract_inv [(NONE,ts)] [] ctx cenv cx ==>
        ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] /\
        cenv_module_pins_mods [(NONE,ts)] cenv` by
    simp[contract_inv_def] >>
  simp[body_inv_split_def, module_body_inv_def, ALOOKUP_def,
       cenv_module_pins_split_def, SF CONJ_ss] >>
  eq_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `!ts. contract_inv _ _ _ _ _ ==> _` (qspec_then `ts` mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem int_calls_expr_main_singleton[local]:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
  EVERY (source_body_call_supported cx)
    (int_calls_expr e) ==>
  EVERY (\c. FST c = NONE) (int_calls_expr e)
Proof
  simp[EVERY_MEM, FORALL_PROD, source_body_call_supported_def,
       get_module_code_def, ALOOKUP_def] >>
  rpt strip_tac >> res_tac >> gvs[AllCaseEqs()]
QED

fun expr_pre_mods_singleton_tac split_def mods_def =
  strip_tac >>
  `cx_tops cx = tops` by simp[cx_tops_def, get_module_code_def, ALOOKUP_def] >>
  simp[split_def] >>
  qpat_assum `ALOOKUP cx.sources _ = _`
    (assume_tac o MATCH_MP int_calls_expr_main_singleton) >>
  simp[mods_def, expr_sim_inv_mods_singleton, source_body_calls_main,
       type_env_def, type_env_all_modules_def, FUNION_FEMPTY_2,
       SF CONJ_ss] >>
  metis_tac[];

Theorem expr_body_pre_mods_singleton[local]:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
  cenv.ce_module = NONE /\ immutable_section_layout_mods [(NONE,tops)] cenv ==>
  (expr_body_pre_mods [(NONE,tops)] cenv cx env e es <=>
   expr_body_pre cenv cx env e es)
Proof
  expr_pre_mods_singleton_tac expr_body_pre_split_def expr_body_pre_mods_def
QED

Theorem expr_map_pre_mods_singleton[local]:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
  cenv.ce_module = NONE /\ immutable_section_layout_mods [(NONE,tops)] cenv ==>
  (expr_map_pre_mods [(NONE,tops)] cenv cx env e es <=>
   expr_map_pre cenv cx env e es)
Proof
  expr_pre_mods_singleton_tac expr_map_pre_split_def expr_map_pre_mods_def
QED

Theorem body_expr_full_ok_mods_singleton:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
  (!e. body_expr_full_ok_mods [(NONE,tops)] [] cx e <=>
         body_expr_full_ok cx e) /\
  (!es. body_exprs_full_ok_mods [(NONE,tops)] [] cx es <=>
         body_exprs_full_ok cx es)
Proof
  strip_tac >>
  `(!mods exps cx e. mods = [(NONE,tops)] /\ exps = [] /\
      ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
      (body_expr_full_ok_mods mods exps cx e <=> body_expr_full_ok cx e)) /\
    (!mods exps cx es. mods = [(NONE,tops)] /\ exps = [] /\
      ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
      (body_exprs_full_ok_mods mods exps cx es <=> body_exprs_full_ok cx es))` by
    (ho_match_mp_tac body_expr_full_ok_mods_ind >> rpt conj_tac >>
     rpt strip_tac >> gvs[]
     >- (rename1 `body_expr_full_ok_mods _ _ cx' e <=> _` >>
         `!t c a b. e = IfExp t c a b ==>
            (((?s tv s'. eval_expr cx' c s = (INL tv,s')) ==>
              body_expr_full_ok_mods [(NONE,tops)] [] cx' a /\
              body_expr_full_ok_mods [(NONE,tops)] [] cx' b) <=>
             ((?s tv s'. eval_expr cx' c s = (INL tv,s')) ==>
              body_expr_full_ok cx' a /\ body_expr_full_ok cx' b))` by
           (rpt gen_tac >> disch_tac >>
            Cases_on `?s tv s'. eval_expr cx' c s = (INL tv,s')` >>
            simp[] >> metis_tac[]) >>
         drule body_inv_singleton >> strip_tac >>
         once_rewrite_tac[body_expr_full_ok_mods_def, body_expr_full_ok_def] >>
         simp[module_body_inv_def, ALOOKUP_def] >>
         simp[FORALL_OPTION, GSYM shadow_body_inv_split_def, GSYM AND_IMP_INTRO] >>
         once_rewrite_tac[contract_inv_singleton_guard] >>
         simp[expr_body_pre_mods_singleton, expr_map_pre_mods_singleton,
             expr_sim_full_mods_singleton, expr_vv_sim_full_mods_singleton,
             expr_map_sim_full_mods_singleton]) >>
     once_rewrite_tac[body_expr_full_ok_mods_def, body_expr_full_ok_def] >>
     simp[] >>
     Cases_on `?s tv t s1 v t1. eval_expr cx' e s = (INL tv,t) /\
                              read_result cx' tv s1 = (INL v,t1)` >>
     simp[] >>
     qpat_x_assum `_ ==> (body_exprs_full_ok_mods _ _ _ _ <=> _)` mp_tac >>
     simp[]) >>
  conj_tac >> gen_tac >> first_x_assum irule >> simp[]
QED

Theorem body_stmt_full_ok_mods_singleton:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
  (body_stmt_full_ok_mods [(NONE,tops)] [] cx s <=>
     body_stmt_full_ok cx s)
Proof
  strip_tac >>
  qpat_assum `ALOOKUP cx.sources _ = SOME [(NONE,tops)]`
    (assume_tac o MATCH_MP body_inv_singleton) >>
  simp[body_stmt_full_ok_mods_def, body_stmt_full_ok_def,
       module_body_inv_def, ALOOKUP_def,
       FORALL_OPTION, GSYM shadow_body_inv_split_def,
       GSYM AND_IMP_INTRO] >>
  once_rewrite_tac[contract_inv_singleton_guard] >>
  simp[expr_sim_inv_mods_singleton, frame_ret_ok_full_mods_singleton,
       stmt_frag_full_mods_singleton]
QED

Theorem body_stmts_full_ok_mods_singleton:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
  (body_stmts_full_ok_mods [(NONE,tops)] [] cx ss <=>
     body_stmts_full_ok cx ss)
Proof
  strip_tac >>
  qpat_assum `ALOOKUP cx.sources _ = SOME [(NONE,tops)]`
    (assume_tac o MATCH_MP body_inv_singleton) >>
  simp[body_stmts_full_ok_mods_def, body_stmts_full_ok_def,
       module_body_inv_def, ALOOKUP_def,
       FORALL_OPTION, GSYM shadow_body_inv_split_def,
       GSYM AND_IMP_INTRO] >>
  once_rewrite_tac[contract_inv_singleton_guard] >>
  simp[expr_sim_inv_mods_singleton, frame_ret_ok_full_mods_singleton,
       stmt_frag_full_mods_singleton]
QED

Theorem body_results_full_ok_mods_singleton:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
  (body_results_full_ok_mods [(NONE,tops)] [] cx es <=>
     body_results_full_ok cx es)
Proof
  strip_tac >> Induct_on `es` >>
  simp[body_results_full_ok_mods_def, body_results_full_ok_def,
       body_expr_full_ok_mods_singleton]
QED

Theorem body_iterator_full_ok_mods_singleton:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
  (body_iterator_full_ok_mods [(NONE,tops)] [] cx it <=>
     body_iterator_full_ok cx it)
Proof
  strip_tac >> Cases_on `it` >>
  simp[body_iterator_full_ok_mods_def, body_iterator_full_ok_def,
       body_expr_full_ok_mods_singleton]
QED

Theorem body_for_full_ok_mods_singleton:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
  (body_for_full_ok_mods [(NONE,tops)] [] cx tyv nm body vs <=>
     body_for_full_ok cx tyv nm body vs)
Proof
  strip_tac >>
  simp[body_for_full_ok_mods_def, body_for_full_ok_def,
       body_stmts_full_ok_mods_singleton]
QED

Theorem body_base_target_full_ok_mods_singleton:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
  (body_base_target_full_ok_mods [(NONE,tops)] [] cx t <=>
     body_base_target_full_ok cx t)
Proof
  strip_tac >>
  completeInduct_on `base_assignment_target_size t` >>
  Cases_on `t` >>
  gvs[body_base_target_full_ok_mods_def, body_base_target_full_ok_def,
      body_expr_full_ok_mods_singleton, expr_size_def] >>
  first_x_assum irule >> simp[]
QED

Theorem body_tuple_target_full_ok_mods_singleton:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
  (!g v. body_tuple_target_full_ok_mods [(NONE,tops)] [] cx g v <=>
         body_tuple_target_full_ok cx g v) /\
  (!gs vs. body_tuple_targets_full_ok_mods [(NONE,tops)] [] cx gs vs <=>
         body_tuple_targets_full_ok cx gs vs)
Proof
  strip_tac >>
  `(!mods exps cx g v. mods = [(NONE,tops)] /\ exps = [] /\
      ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
      (body_tuple_target_full_ok_mods mods exps cx g v <=>
       body_tuple_target_full_ok cx g v)) /\
    (!mods exps cx gs vs. mods = [(NONE,tops)] /\ exps = [] /\
      ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
      (body_tuple_targets_full_ok_mods mods exps cx gs vs <=>
       body_tuple_targets_full_ok cx gs vs))` by
    (ho_match_mp_tac body_tuple_target_full_ok_mods_ind >> rpt conj_tac >>
     rpt strip_tac >>
     once_rewrite_tac[body_tuple_target_full_ok_mods_def, body_tuple_target_full_ok_def] >>
     gvs[body_base_target_full_ok_mods_singleton]) >>
  conj_tac >> rpt gen_tac >> first_x_assum irule >> simp[]
QED

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
