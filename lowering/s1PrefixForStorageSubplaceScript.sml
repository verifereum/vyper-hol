(* Route a nested storage-root iterator by its actual evaluated result. *)
Theory s1PrefixForStorageSubplace
Ancestors
  s1PrefixPreds s1PrefixDefs bodyFullForIteratorHeld bodyFullForFacts
  bodyFullForArray bodyFullForArrayRound bodyFullForExprCut bodyFullForArrayBranch
  forNestedArrayCapture[qualified,ignore_grammar]
  vyperTypeContract[qualified,ignore_grammar]
  vyperTypeSystem vyperState vyperInterpreter vyperStorageFootprint vyperAST
  bodyFullShadowBodyInv bodySimFull bodySim
  gasContext gasExplicitSites fragGasOriginPtr ptrDiscipline
  stmtLowering loweringPosts compileEnv context

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  disch_then (mk_asm "prepared") >> disch_then (mk_asm "snapshot") >>
  disch_then (mk_asm "live") >>
  qpat_x_assum `?tgt nid. loop_iterator_place _ = _ /\ _`
    (qx_choosel_then [`tgt`,`nid`] (map_every assume_tac o CONJUNCTS)) >>
  asm "prepared" irule >> reverse conj_tac
  >- (drule_then strip_assume_tac type_stmt_for_projection >>
      drule_then strip_assume_tac supported_stmt_for_projection >>
      `?bd. expr_type e = ArrayT typ bd` by
        (drule_then strip_assume_tac type_stmt_for_array_bound >> simp[]) >>
      irule nonslot_iterator_expr_pre >> conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl [`bd`,`ctx`,`id`,`loop_body`,`n`,`tops`,`typ`] >> simp[]) >>
  map_every qx_gen_tac [`st0`,`sa`,`sb`,`sha`,`shb`,`s0`,`G0`,`tn0`,`vv`,
    `se`,`she`,`bd`,`tyv`,`marks`,`rv`,`em`,`G`,`tn`,`u`] >>
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `obs = gas_explicit marks s0.vs_gas_readings` >>
  `valid_horizon cx st0 (storage_trace_horizon em.storage_trace) em.storage_trace` by
    fs[storage_trace_domain_def] >>
  `em with gas_obs := [] = em` by
    (qpat_assum `!H. valid_horizon _ _ H em.storage_trace ==> for_array_expr_endpoint _ _ _ _ _ _ _ _ _ _ _ _`
       (drule_then (mp_tac o REWRITE_RULE [for_array_expr_endpoint_def])) >>
     simp[evaluation_state_component_equality]) >>
  `eval_expr cx e (es with gas_obs := obs) = (INL rv,em)` by
    (qpat_assum `em with gas_obs := [] = em` (fn eq =>
       qpat_assum `!tail. eval_expr cx e _ = _` (qspec_then `[]` mp_tac) >>
       simp[NoAsms,Abbr `obs`,eq])) >>
  `expr_body_pre cenv cx env e (es with gas_obs := obs)` by simp[] >>
  drule_at_then (Pat `eval_expr _ _ _ = _`) drule_all
    forNestedArrayCaptureTheory.nested_array_capture_cases >>
  disch_then (qx_choose_then `elem` (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 mp_tac kall_tac))) >>
  `elem = tyv` by
    (qpat_assum `evaluate_type (get_tenv cx) typ = SOME elem` mp_tac >>
     qpat_assum `evaluate_type (get_tenv cx) typ = SOME tyv`
       (fn th => simp[NoAsms,th])) >>
  pop_assum SUBST_ALL_TAC >> impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (DISJ_CASES_THEN2 (qx_choose_then `av` assume_tac)
    (qx_choosel_then [`tr`,`slot`] assume_tac))
  >- suspend "snapshot"
  >> suspend "storage"
QED
*)
Theorem compile_for_storage_subplace_array_frag_prefix_from_cuts:
  !cx id typ e n loop_body DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
  ~(?bd nid. e = TopLevelName (ArrayT typ bd) nid /\
             supported_storage_value tops nid (ArrayT typ bd)) /\
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
  vyperTypeContract$stmt_loop_calls_ok [(NONE,tops)] (For id typ (Array e) n loop_body) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
  type_stmt env ret_ty (For id typ (Array e) n loop_body) = SOME env' /\
  ~supported_expr_exists (const_name_root cx) e /\
  stmt_exprs_ok cenv (For id typ (Array e) n loop_body) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ (Array e) n loop_body)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ cenv ret_ty /\
  ~(?ty nid. e = TopLevelName ty nid) /\
  (?tgt nid. loop_iterator_place e = SOME tgt /\ target_root tgt = TopLevelNameTarget nid /\
     ((?vis kind ty slot.
        supported_variable_decl tops nid = SOME (vis,kind,ty,SOME slot) /\
        (kind = Storage \/ kind = Transient)) \/
      (?vis transient kt vt slot.
        supported_hashmap_decl tops nid = SOME (vis,transient,kt,vt,SOME slot)))) ==>
  (* The prepared iterator cut, specialized to this statement. *)
  (expr_body_pre cenv cx env e es /\
   (!st0 sa sb sha shb s0 G0 tn0 vv se she bd tyv marks rv em G tn u.
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
                           (eval_for cx tyv id loop_body vs))) (stmt_res_ok lctx) em /\
      (!vs. (!tail. array_iterator_results cx (expr_type e) rv (em with gas_obs := tail) =
                      (INL vs,em with gas_obs := tail)) /\
             check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" em = (INL (),em) ==>
             body_for_full_ok cx tyv id loop_body vs /\ body_for_prefix_ok cx tyv id loop_body vs /\
             gas_admissible (eval_for cx tyv id loop_body vs) (stmt_res_ok lctx) em) ==>
      gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
        (bind (array_iterator_results cx (expr_type e) rv)
          (\vs. ignore_bind (check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long")
                           (eval_for cx tyv id loop_body vs))) (em,u,G,tn)) ==>
   stmt_frag_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ cenv
     (stmt_env cenv lctx ret_ty (For id typ (Array e) n loop_body))
     (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (For id typ (Array e) n loop_body)))
     (eval_stmt cx (For id typ (Array e) n loop_body)) es) ==>
  (* The snapshot cut; static premises are in the outer context. *)
  (!st0 sa sb sha shb s0 G0 tn0 vv se she bd tyv obs rv em G tn u.
     compile_stmt cenv lctx ret_ty (For id typ (Array e) n loop_body) sa = ((),sb) /\
     compile_stmt (gas_shadow_env T cenv) lctx ret_ty
       (gas_shadow_stmt (For id typ (Array e) n loop_body)) sha = ((),shb) /\
     compile_expr cenv (expr_type e) e sa = (vv,se) /\
     compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) sha = (vv,she) /\
     gas_shadow_state sa sha /\ fn_has_code sa sb func /\ fn_has_code sha shb shadow_func /\
     gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
     gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
     MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
     cenv.ce_alloca_locals /\ local_ptrs_reserved cenv sa /\ ci_mono sa se /\
     ret_pc_ok cenv sa s0 /\ return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv em u /\
     (!H. dead_lo_ok H (DF H) lo cenv cx) /\
     (!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t) /\
     expr_body_pre cenv cx env e es /\
     expr_type e = ArrayT typ bd /\ bound_length bd <= n /\
     evaluate_type (get_tenv cx) typ = SOME tyv /\ storage_trace_domain cx st0 em.storage_trace /\
     (!tail. eval_expr cx e (es with gas_obs := obs ++ tail) = (INL rv,em with gas_obs := tail)) /\
     (!H. valid_horizon cx st0 H em.storage_trace ==>
        for_array_expr_endpoint (DF,lo,d,ctx,func) cenv cx e (es,sa,s0,G0,tn0)
          (vv,se) H rv em G tn u) /\
     (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
     ((?av. rv = Value (ArrayV av)) \/ (?src name path. rv = PlaceR (ImmutablePlace src name path))) /\
     (!av. read_result cx rv em = (INL (ArrayV av),em) ==>
        for_nonslot_code_frame cenv cx env ctx func id e loop_body
          (case vv_location vv of NONE => LocMemory | SOME l => l) rv vv av em u) /\
     (!vs. (!tail. array_iterator_results cx (expr_type e) rv (em with gas_obs := tail) =
                     (INL vs,em with gas_obs := tail)) /\
            check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" em = (INL (),em) ==>
            body_for_full_ok cx tyv id loop_body vs /\ body_for_prefix_ok cx tyv id loop_body vs /\
            gas_admissible (eval_for cx tyv id loop_body vs) (stmt_res_ok lctx) em) ==>
     gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
       (bind (array_iterator_results cx (expr_type e) rv)
         (\vs. ignore_bind (check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long")
                          (eval_for cx tyv id loop_body vs))) (em,u,G,tn)) ==>
  (* The live-storage cut. *)
  (!st0 sa sb sha shb s0 G0 tn0 vv se bd tyv obs tr slot em G tn u.
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
     expr_body_pre cenv cx env e es /\
     expr_type e = ArrayT typ bd /\ bound_length bd <= n /\
     evaluate_type (get_tenv cx) typ = SOME tyv /\ storage_trace_domain cx st0 em.storage_trace /\
     (!tail. eval_expr cx e (es with gas_obs := obs ++ tail) =
        (INL (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))),em with gas_obs := tail)) /\
     (!H. valid_horizon cx st0 H em.storage_trace ==>
        for_array_expr_endpoint (DF,lo,d,ctx,func) cenv cx e (es,sa,s0,G0,tn0)
          (vv,se) H (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))) em G tn u) /\
     (!H. valid_horizon cx st0 H es.storage_trace ==> storage_well_formed_on cx es (FST H)) /\
     alloca_frame cenv es sa s0 cenv em u /\
     ((?w. vv_operand vv = Lit w) \/
      (?tgt nid. loop_iterator_place e = SOME tgt /\ target_root tgt = TopLevelNameTarget nid /\
                ~(?ty i. e = TopLevelName ty i))) /\
     (!vs. (!tail. array_iterator_results cx (expr_type e)
                     (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))) (em with gas_obs := tail) =
                     (INL vs,em with gas_obs := tail)) /\
            check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" em = (INL (),em) ==>
            body_for_full_ok cx tyv id loop_body vs /\ body_for_prefix_ok cx tyv id loop_body vs /\
            gas_admissible (eval_for cx tyv id loop_body vs) (stmt_res_ok lctx) em) ==>
     gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
       (bind (array_iterator_results cx (expr_type e) (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))))
         (\vs. ignore_bind (check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long")
                          (eval_for cx tyv id loop_body vs))) (em,u,G,tn)) ==>
  stmt_frag_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (For id typ (Array e) n loop_body))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (For id typ (Array e) n loop_body)))
    (eval_stmt cx (For id typ (Array e) n loop_body)) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_for_storage_subplace_array_frag_prefix_from_cuts[snapshot]:
  `post_value_type cenv e = ArrayT typ bd` by
    (`post_value_type cenv e = expr_type e` suffices_by simp[] >>
     irule loweringPostsTheory.post_value_type_not_int_call >> rpt strip_tac >>
     gvs[vyperTypeContractTheory.loop_iterator_place_def]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  qpat_assum `!H. valid_horizon _ _ H em.storage_trace ==> for_array_expr_endpoint _ _ _ _ _ _ _ _ _ _ _ _`
    (drule_then (map_every assume_tac o CONJUNCTS o REWRITE_RULE [for_array_expr_endpoint_def])) >>
  asm "snapshot" irule >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC)
  >- (qexists `obs` >> simp[Abbr `obs`])
  >- (qexists `bd` >> simp[])
  >- (disj1_tac >> qexists `av` >> first_assum ACCEPT_TAC) >>
  qexistsl [`G0`,`s0`,`sa`,`sb`,`se`,`sha`,`shb`,`she`,`tn0`,`vv`] >>
  asm_rewrite_tac[] >>
  rewrite_tac[for_nonslot_code_frame_def] >>
  qpat_assum `!v. rv = Value v /\ _ ==> _` (qspec_then `ArrayV av` mp_tac) >>
  Cases_on `vv` >> simp[vv_location_def,is_word_type_def,is_bytestring_type_def]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_for_storage_subplace_array_frag_prefix_from_cuts[storage]:
  qpat_x_assum `rv = PlaceR _` SUBST_ALL_TAC >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> storage_well_formed_on cx es (FST H)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2))) >>
  `bound_length bd <= n` by simp[] >>
  asm "live" irule >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC)
  >- (qexists `obs` >> simp[Abbr `obs`]) >>
  qexistsl [`G0`,`s0`,`sa`,`sb`,`se`,`sha`,`shb`,`tn0`,`vv`] >>
  asm_rewrite_tac[] >>
  disj2_tac >> qexistsl [`tgt`,`nid`] >> asm_rewrite_tac[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise compile_for_storage_subplace_array_frag_prefix_from_cuts
*)
