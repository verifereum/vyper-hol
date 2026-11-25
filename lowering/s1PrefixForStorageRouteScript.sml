(* A bare storage-array iterator reaches the live loop at a captured slot. *)
Theory s1PrefixForStorageRoute
Ancestors
  s1PrefixPreds s1PrefixDefs
  forStorageLiteralPre forStorageLiteralCapture
  bodyFullForExprCut bodySimFull vyperAST vyperStorageFootprint

(* The two callback premises are the prepared expression cut, specialized
   to this statement, and the live storage continuation for the resulting slot. *)
Theorem compile_for_storage_array_frag_prefix_from_continue:
  !cx id typ bd nid n loop_body DF lo d PG tops bindings ctx shadow_ctx func
    shadow_func cenv env env' ret_ty lctx RetQ es e.
  e = TopLevelName (ArrayT typ bd) nid /\
  supported_storage_value tops nid (ArrayT typ bd) /\
  (!tenv s'' tyv t s'3' vs t' s'4' x t''.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tyv,t) /\
     eval_iterator cx (Array e) s'3' = (INL vs,t') /\
     check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' = (INL x,t'') ==>
     body_for_full_ok cx tyv id loop_body vs) /\
  (!tenv s'' tyv t s'3' vs t' s'4' x t''.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tyv,t) /\
     eval_iterator cx (Array e) s'3' = (INL vs,t') /\
     check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' = (INL x,t'') ==>
     body_for_prefix_ok cx tyv id loop_body vs) /\
  (!tenv s'' tyv t.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tyv,t) ==>
     body_iterator_full_ok cx (Array e)) /\
  (!tenv s'' tyv t.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tyv,t) ==>
     body_iterator_prefix_ok cx (Array e)) /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (For id typ (Array e) n loop_body) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (For id typ (Array e) n loop_body) ==> occurs_abi_decode_target target tops) /\
  stmt_loop_calls_ok [(NONE,tops)] (For id typ (Array e) n loop_body) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (For id typ (Array e) n loop_body) = SOME env' /\
  stmt_exprs_ok cenv (For id typ (Array e) n loop_body) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ (Array e) n loop_body)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ cenv ret_ty /\
  (expr_body_pre cenv cx env e es ==>
   (!st0 sa sb sha shb s0 G0 tn0 vv se she bound tyv marks rv em G tn u.
      compile_stmt cenv lctx ret_ty (For id typ (Array e) n loop_body) sa = ((),sb) /\
      compile_stmt (gas_shadow_env T cenv) lctx ret_ty
        (gas_shadow_stmt (For id typ (Array e) n loop_body)) sha = ((),shb) /\
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
      expr_type e = ArrayT typ bound /\ bound_length bound = n /\
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
                           (eval_for cx tyv id loop_body vs))) (stmt_res_ok lctx) em /\
      (!vs. (!tail. array_iterator_results cx (expr_type e) rv (em with gas_obs := tail) =
                      (INL vs,em with gas_obs := tail)) /\
             check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" em = (INL (),em) ==>
             body_for_full_ok cx tyv id loop_body vs /\
             body_for_prefix_ok cx tyv id loop_body vs /\
             gas_admissible (eval_for cx tyv id loop_body vs) (stmt_res_ok lctx) em) ==>
      gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
        (bind (array_iterator_results cx (expr_type e) rv)
          (\vs. ignore_bind (check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long")
                           (eval_for cx tyv id loop_body vs))) (em,u,G,tn)) ==>
   stmt_frag_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ cenv
     (stmt_env cenv lctx ret_ty (For id typ (Array e) n loop_body))
     (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (For id typ (Array e) n loop_body)))
     (eval_stmt cx (For id typ (Array e) n loop_body)) es) /\
  (!st0 sa sb sha shb s0 G0 tn0 vv se tyv obs tr slot em Gu tu u.
     compile_stmt cenv lctx ret_ty (For id typ (Array e) n loop_body) sa = ((),sb) /\
     compile_stmt (gas_shadow_env T cenv) lctx ret_ty
       (gas_shadow_stmt (For id typ (Array e) n loop_body)) sha = ((),shb) /\
     compile_expr cenv (expr_type e) e sa = (vv,se) /\
     gas_shadow_state sa sha /\ fn_has_code sa sb func /\ fn_has_code sha shb shadow_func /\
     gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
     gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
     MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
     cenv.ce_alloca_locals /\ local_ptrs_reserved cenv sa /\
     ret_pc_ok cenv sa s0 /\ return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv em u /\
     (!H. dead_lo_ok H (DF H) lo cenv cx) /\
     (!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t) /\
     expr_body_pre cenv cx env e es /\ expr_type e = ArrayT typ bd /\ bound_length bd <= n /\
     evaluate_type (get_tenv cx) typ = SOME tyv /\
     storage_trace_domain cx st0 em.storage_trace /\
     (!tail. eval_expr cx e (es with gas_obs := obs ++ tail) =
        (INL (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))),em with gas_obs := tail)) /\
     (!H. valid_horizon cx st0 H em.storage_trace ==>
        for_array_expr_endpoint (DF,lo,d,ctx,func) cenv cx e (es,sa,s0,G0,tn0)
          (vv,se) H (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))) em Gu tu u) /\
     (!H. valid_horizon cx st0 H es.storage_trace ==> storage_well_formed_on cx es (FST H)) /\
     alloca_frame cenv es sa s0 cenv em u /\ (?w. vv_operand vv = Lit w) /\
     (!vs. (!tail. array_iterator_results cx (expr_type e)
                     (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))) (em with gas_obs := tail) =
                     (INL vs,em with gas_obs := tail)) /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" em = (INL (),em) ==>
       body_for_full_ok cx tyv id loop_body vs /\ body_for_prefix_ok cx tyv id loop_body vs /\
       gas_admissible (eval_for cx tyv id loop_body vs) (stmt_res_ok lctx) em) ==>
     gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
       (bind (array_iterator_results cx (expr_type e) (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))))
         (\items. ignore_bind (check (compatible_bound (Dynamic n) (LENGTH items)) "For too long")
                            (eval_for cx tyv id loop_body items))) (em,u,Gu,tu)) ==>
  stmt_frag_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (For id typ (Array e) n loop_body))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (For id typ (Array e) n loop_body)))
    (eval_stmt cx (For id typ (Array e) n loop_body)) es
Proof
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env e es` by
    (qpat_assum `e = TopLevelName _ _` SUBST_ALL_TAC >>
     drule_all_then ACCEPT_TAC for_storage_literal_expr_pre) >>
  qpat_x_assum `expr_body_pre _ _ _ _ _ ==> _` (drule_then match_mp_tac) >>
  map_every qx_gen_tac [`st0`,`sa`,`sb`,`sha`,`shb`,`s0`,`G0`,`tn0`,`vv`,
    `se`,`she`,`bound`,`tyv`,`marks`,`rv`,`em`,`G`,`tn`,`u`] >>
  strip_tac >>
  `bound = bd` by
    (qpat_assum `expr_type e = ArrayT typ bound` mp_tac >>
     qpat_assum `e = TopLevelName _ _` SUBST_ALL_TAC >>
     simp[NoAsms,expr_type_def] >> disch_then (ACCEPT_TAC o SYM)) >>
  qpat_x_assum `bound = bd` SUBST_ALL_TAC >>
  `valid_horizon cx st0 (storage_trace_horizon em.storage_trace) em.storage_trace` by
    fs[storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  `?tr off. rv = PlaceR (StoragePlace tr (n2w off) (ArrayTV tyv bd)) /\
            vv_operand vv = Lit (n2w off)` by
    (qpat_assum `e = TopLevelName _ _` SUBST_ALL_TAC >>
     drule_at_then (Pat `valid_horizon _ _ _ _`) drule_all for_storage_literal_capture >>
     disch_then (qx_choosel_then [`tr`,`off`] strip_assume_tac) >>
     qexistsl [`tr`,`off`] >> simp[]) >>
  qpat_x_assum `rv = PlaceR _` SUBST_ALL_TAC >>
  `bound_length bd <= n` by simp[] >>
  qpat_x_assum `!st0 sa sb sha shb s0 G0 tn0 vv se tyv obs tr slot em Gu tu u. _`
    irule >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qexists `gas_explicit marks s0.vs_gas_readings` >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2))) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl [`G0`,`s0`,`sa`,`sb`,`se`,`sha`,`shb`,`tn0`,`vv`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qexists `n2w off` >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
