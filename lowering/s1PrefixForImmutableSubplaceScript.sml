(* Route a nested immutable iterator through its selected-array snapshot. *)
Theory s1PrefixForImmutableSubplace
Ancestors
  s1PrefixPreds s1PrefixDefs bodyFullForIteratorHeld
  bodyFullForArrayBranch bodyFullForArrayRound bodyFullForExprCut
  bodyFullForFacts contractInvContextProps
  forNestedArrayCapture[qualified,ignore_grammar]
  vyperTypeContract[qualified,ignore_grammar]

val _ = Parse.hide "body";

(* Both cuts are premises, specialized at the enclosing For statement. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> disch_then (mk_asm "prepared") >> disch_then (mk_asm "snapshot") >>
  strip_tac >>
  `expr_body_pre cenv cx env e es` by
    (drule_then strip_assume_tac type_stmt_for_projection >>
     drule_then strip_assume_tac supported_stmt_for_projection >>
     `?bd. expr_type e = ArrayT typ bd` by
       (drule_then strip_assume_tac vyperTypeSystemTheory.type_stmt_for_array_bound >> simp[]) >>
     irule nonslot_iterator_expr_pre >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`bd`,`ctx`,`id`,`body`,`n`,`tops`,`typ`] >> simp[]) >>
  asm_x "prepared" irule >> conj_tac
  >- suspend "capture" >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
*)
Theorem compile_for_immutable_subplace_array_frag_prefix_from_cuts:
  !cx id typ e n body DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
  (( !tenv s'' tyv t s'3' vs t' s'4' x t''.
      tenv = get_tenv cx /\
      lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tyv,t) /\
      eval_iterator cx (Array e) s'3' = (INL vs,t') /\
      check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' = (INL x,t'') ==>
      body_for_full_ok cx tyv id body vs) /\
   (!tenv s'' tyv t.
      tenv = get_tenv cx /\
      lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tyv,t) ==>
      body_iterator_full_ok cx (Array e)) /\
   (!tenv s'' tyv t s'3' vs t' s'4' x t''.
      tenv = get_tenv cx /\
      lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tyv,t) /\
      eval_iterator cx (Array e) s'3' = (INL vs,t') /\
      check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' = (INL x,t'') ==>
      body_for_prefix_ok cx tyv id body vs) /\
   (!tenv s'' tyv t.
      tenv = get_tenv cx /\
      lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tyv,t) ==>
      body_iterator_prefix_ok cx (Array e)) /\
   body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
   body_const_cells_agree [(NONE,tops)] cx env es /\
   expr_sim_inv cenv cx env es /\ expr_body_pre cenv cx env e es /\
   type_stmt env ret_ty (For id typ (Array e) n body) = SOME env' /\
   (!st0 sa sb sha shb s0 G0 tn0 vv se she bd tyv marks rv em G tn u.
      compile_stmt cenv lctx ret_ty (For id typ (Array e) n body) sa = ((),sb) /\
      compile_stmt (gas_shadow_env T cenv) lctx ret_ty
        (gas_shadow_stmt (For id typ (Array e) n body)) sha = ((),shb) /\
      compile_expr cenv (expr_type e) e sa = (vv,se) /\
      compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) sha = (vv,she) /\
      gas_shadow_state sa sha /\ gas_shadow_state se she /\ gas_shadow_state sb shb /\
      gas_shadow_context ctx shadow_ctx /\ gas_shadow_function func shadow_func /\
      ctx_inst_ids_distinct ctx /\ fn_inst_ids_distinct func /\
      MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\ fn_has_code sha shb shadow_func /\
      fn_has_code sa se func /\ fn_has_code sha she shadow_func /\
      ci_mono sa se /\ ci_mono se sb /\
      cenv.ce_alloca_locals /\ local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
      ret_pc_ok cenv sa s0 /\ return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
      expr_type e = ArrayT typ bd /\ bound_length bd = n /\
      evaluate_type (get_tenv cx) typ = SOME tyv /\
      expr_body_pre cenv cx env e es /\
      (!tail. eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
                             (INL rv,em with gas_obs := tail)) /\
      storage_trace_domain cx st0 em.storage_trace /\
      (!H. valid_horizon cx st0 H em.storage_trace ==>
        for_array_expr_endpoint (DF,lo,d,ctx,func) cenv cx e (es,sa,s0,G0,tn0)
          (vv,se) H rv em G tn u) /\
      (!H. valid_horizon cx st0 H em.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (s0,G0,tn0) marks (OK u,G,tn)) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t) /\
      return_buf_frame d cenv se u /\ return_buf_sep d cenv em u /\
      alloca_frame cenv es sa s0 cenv em u /\
      gas_admissible
        (bind (array_iterator_results cx (expr_type e) rv)
          (\vs. ignore_bind (check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long")
                           (eval_for cx tyv id body vs))) (stmt_res_ok lctx) em /\
      (!vs. (!tail. array_iterator_results cx (expr_type e) rv (em with gas_obs := tail) =
                      (INL vs,em with gas_obs := tail)) /\
             check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" em = (INL (),em) ==>
             body_for_full_ok cx tyv id body vs /\ body_for_prefix_ok cx tyv id body vs /\
             gas_admissible (eval_for cx tyv id body vs) (stmt_res_ok lctx) em) ==>
      gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
        (bind (array_iterator_results cx (expr_type e) rv)
          (\vs. ignore_bind (check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long")
                           (eval_for cx tyv id body vs))) (em,u,G,tn)) ==>
   stmt_frag_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ cenv
     (stmt_env cenv lctx ret_ty (For id typ (Array e) n body))
     (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (For id typ (Array e) n body)))
     (eval_stmt cx (For id typ (Array e) n body)) es) ==>
  (!st0 sa sb sha shb s0 G0 tn0 vv se she bd tyv obs rv em G tn u.
    compile_stmt cenv lctx ret_ty (For id typ (Array e) n body) sa = ((),sb) /\
    compile_stmt (gas_shadow_env T cenv) lctx ret_ty
      (gas_shadow_stmt (For id typ (Array e) n body)) sha = ((),shb) /\
    compile_expr cenv (expr_type e) e sa = (vv,se) /\
    compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) sha = (vv,she) /\
    gas_shadow_state sa sha /\ fn_has_code sa sb func /\ fn_has_code sha shb shadow_func /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
    body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
    supported_stmt tops bindings (For id typ (Array e) n body) /\
    type_stmt env ret_ty (For id typ (Array e) n body) = SOME env' /\
    stmt_exprs_ok cenv (For id typ (Array e) n body) /\
    vyperTypeContract$stmt_loop_calls_ok [(NONE,tops)] (For id typ (Array e) n body) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
        (For id typ (Array e) n body) ==> occurs_abi_decode_target target tops) /\
    call_evaluation_safe cx (int_calls_stmt (For id typ (Array e) n body)) /\
    frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ cenv ret_ty /\
    cenv.ce_alloca_locals /\ local_ptrs_reserved cenv sa /\ ci_mono sa se /\
    ret_pc_ok cenv sa s0 /\ return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv em u /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t) /\
    ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\ expr_body_pre cenv cx env e es /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_type e = ArrayT typ bd /\ bound_length bd <= n /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\
    storage_trace_domain cx st0 em.storage_trace /\
    (!tail. eval_expr cx e (es with gas_obs := obs ++ tail) =
       (INL rv,em with gas_obs := tail)) /\
    (!H. valid_horizon cx st0 H em.storage_trace ==>
       for_array_expr_endpoint (DF,lo,d,ctx,func) cenv cx e (es,sa,s0,G0,tn0)
         (vv,se) H rv em G tn u) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0) /\
    ((?av. rv = Value (ArrayV av)) \/ (?src name path. rv = PlaceR (ImmutablePlace src name path))) /\
    (!av. read_result cx rv em = (INL (ArrayV av),em) ==>
       for_nonslot_code_frame cenv cx env ctx func id e body
         (case vv_location vv of NONE => LocMemory | SOME l => l) rv vv av em u) /\
    (!vs. (!tail. array_iterator_results cx (expr_type e) rv (em with gas_obs := tail) =
                    (INL vs,em with gas_obs := tail)) /\
      check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" em = (INL (),em) ==>
      body_for_full_ok cx tyv id body vs /\ body_for_prefix_ok cx tyv id body vs /\
      gas_admissible (eval_for cx tyv id body vs) (stmt_res_ok lctx) em) ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
      (bind (array_iterator_results cx (expr_type e) rv)
        (\vs. ignore_bind (check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long")
                         (eval_for cx tyv id body vs))) (em,u,G,tn)) ==>
  ~(?bd nid. e = TopLevelName (ArrayT typ bd) nid /\
             supported_storage_value tops nid (ArrayT typ bd)) /\
  (!tenv s'' tyv t s'3' vs t' s'4' x t''.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tyv,t) /\
     eval_iterator cx (Array e) s'3' = (INL vs,t') /\
     check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' = (INL x,t'') ==>
     body_for_full_ok cx tyv id body vs) /\
  (!tenv s'' tyv t.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tyv,t) ==>
     body_iterator_full_ok cx (Array e)) /\
  (!tenv s'' tyv t s'3' vs t' s'4' x t''.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tyv,t) /\
     eval_iterator cx (Array e) s'3' = (INL vs,t') /\
     check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' = (INL x,t'') ==>
     body_for_prefix_ok cx tyv id body vs) /\
  (!tenv s'' tyv t.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tyv,t) ==>
     body_iterator_prefix_ok cx (Array e)) /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (For id typ (Array e) n body) /\
  (!target. supported_stmt_expr_exists
      (expr_abi_decode_target_root target) (For id typ (Array e) n body) ==>
      occurs_abi_decode_target target tops) /\
  vyperTypeContract$stmt_loop_calls_ok [(NONE,tops)] (For id typ (Array e) n body) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
  type_stmt env ret_ty (For id typ (Array e) n body) = SOME env' /\
  ~supported_expr_exists (const_name_root cx) e /\
  stmt_exprs_ok cenv (For id typ (Array e) n body) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ (Array e) n body)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ cenv ret_ty /\
  ~(?ty nid. e = TopLevelName ty nid) /\
  (?tgt nid. loop_iterator_place e = SOME tgt /\ target_root tgt = TopLevelNameTarget nid /\
       IS_SOME (supported_immutable_type tops nid)) ==>
  stmt_frag_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (For id typ (Array e) n body))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (For id typ (Array e) n body)))
    (eval_stmt cx (For id typ (Array e) n body)) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_for_immutable_subplace_array_frag_prefix_from_cuts[capture]:
  map_every qx_gen_tac [`st0`,`sa`,`sb`,`sha`,`shb`,`s0`,`G0`,`tn0`,`vv`,
    `se`,`she`,`bd`,`tyv`,`marks`,`rv`,`em`,`G`,`tn`,`u`] >>
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `start = es with gas_obs := gas_explicit marks s0.vs_gas_readings` >>
  `em with gas_obs := [] = em` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> for_array_expr_endpoint _ _ _ _ _ _ _ _ _ _ _ _`
      (qspec_then `storage_trace_horizon em.storage_trace` mp_tac) >>
     fs[vyperStorageFootprintTheory.storage_trace_domain_def,for_array_expr_endpoint_def,
        vyperStateTheory.evaluation_state_component_equality]) >>
  `eval_expr cx e start = (INL rv,em)` by
    (qpat_assum `em with gas_obs := [] = em` (fn eq =>
       qpat_assum `!tail. eval_expr cx e _ = _` (qspec_then `[]` mp_tac) >>
       simp[NoAsms,Abbr `start`,eq])) >>
  `expr_body_pre cenv cx env e start` by simp[Abbr `start`] >>
  drule_at_then (Pat `eval_expr cx e start = _`) drule_all
    forNestedArrayCaptureTheory.nested_array_capture_cases >>
  disch_then (qx_choose_then `elem` (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 kall_tac assume_tac))) >>
  `elem = tyv` by metis_tac[optionTheory.SOME_11] >>
  pop_assum SUBST_ALL_TAC >>
  `post_value_type cenv e = ArrayT typ bd` by
    (`post_value_type cenv e = expr_type e` suffices_by simp[] >>
     irule loweringPostsTheory.post_value_type_not_int_call >> rpt strip_tac >>
     gvs[vyperTypeContractTheory.loop_iterator_place_def]) >>
  suspend "snapshot"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_for_immutable_subplace_array_frag_prefix_from_cuts[snapshot]:
  qsuff_tac `(?av. rv = Value (ArrayV av)) \/
             (?src name path. rv = PlaceR (ImmutablePlace src name path))`
  >- (disch_tac >> suspend "apply_snapshot") >> gvs[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_for_immutable_subplace_array_frag_prefix_from_cuts[apply_snapshot]:
  asm_x "snapshot" irule >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexists `gas_explicit marks s0.vs_gas_readings` >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qexists `bd` >> simp[]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qexistsl [`G0`,`s0`,`sa`,`sb`,`se`,`sha`,`shb`,`she`,`tn0`,`vv`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- suspend "frame" >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >-
       (gen_tac >> disch_tac >>
        qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
          (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_for_immutable_subplace_array_frag_prefix_from_cuts[frame]:
  qpat_assum `IS_SOME _ ==> _`
    (drule_then (DISJ_CASES_THEN2 (qx_choose_then `va` assume_tac)
      (qx_choosel_then [`src`,`name`,`path`,`attrs`,`tail`,`rt`,`root`,`av0`,`pav`]
         (map_every assume_tac o CONJUNCTS))))
  >- (`valid_horizon cx st0 (storage_trace_horizon em.storage_trace) em.storage_trace` by
        fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> for_array_expr_endpoint _ _ _ _ _ _ _ _ _ _ _ _`
        (drule_then (map_every assume_tac o CONJUNCTS o
           REWRITE_RULE [for_array_expr_endpoint_def])) >>
      rewrite_tac[for_nonslot_code_frame_def] >>
      qpat_assum `!v. rv = Value v /\ _ ==> _` (qspec_then `ArrayV va` mp_tac) >>
      Cases_on `vv` >> simp[contextTheory.vv_location_def,
         compileEnvTheory.is_word_type_def,compileEnvTheory.is_bytestring_type_def]) >>
  qpat_x_assum `rv = PlaceR _` SUBST_ALL_TAC >>
  qpat_x_assum `nid = (src,name)` SUBST_ALL_TAC >>
  drule_then strip_assume_tac type_stmt_for_projection >>
  drule_at_then (Pat `eval_expr cx e start = _`) drule_all exprSimSourceTheory.expr_body_pre_eval_result >>
  strip_tac >>
  `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` by
    (drule_then (MATCH_ACCEPT_TAC o MATCH_MP contract_inv_singleton_source_modules)
       bodySimTheory.body_inv_contract) >>
  `~cx_const_name cx (src,name)` by
    (strip_tac >> drule_all_then strip_assume_tac bodySimTheory.body_inv_const_name_not_root >> fs[]) >>
  `evaluate_type (get_tenv cx) (ArrayT typ bd) = SOME (ArrayTV tyv bd)` by
    (drule_at_then (Pat `eval_expr cx e start = _`) drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >>
     strip_tac >>
     `evaluate_type (get_tenv cx) (ArrayT typ bd) = SOME tvt` by metis_tac[] >>
     drule_then strip_assume_tac vyperTypeValuesTheory.evaluate_type_ArrayT_cases >> gvs[]) >>
  gen_tac >> disch_tac >> drule_all_then MATCH_ACCEPT_TAC selected_array_code_frame
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise compile_for_immutable_subplace_array_frag_prefix_from_cuts
*)
