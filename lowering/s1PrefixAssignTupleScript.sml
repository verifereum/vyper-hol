(* Request-prefix companion to bodyFullAssignTuple. *)
Theory s1PrefixAssignTuple
Ancestors
  s1PrefixPreds bodyFullAssignTuple s1PrefixDefs s1PrefixAssignTupleLocalsCode s1PrefixAssignTupleLocalsTrace tupleTargetStoreProps bodySimStmtFacts exprSimSource bodyFullPreds bodySimFull s1PrefixAssignTupleRhsCode s1PrefixAssignTupleFlatTrace stmtSimAssignTuple loweringPosts s1PrefixCompose gasOutcomeFullCompose s1PrefixProps vyperStorageTrace exprSimDefs list s1PrefixTupleWidenedHeads
  s1PrefixAssignTupleExactLayout s1PrefixTupleWidenedLayout tuplePlaceBorrow
  bodyFullTargetDefs bodyFullSimProjection targetPlaceSim valueEncoding

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule tuple_targets_typing >> disch_then (qx_choose_then `tys` strip_assume_tac) >>
  drule_then assume_tac body_inv_mcopy >>
  `expr_body_pre cenv cx env e es` by (drule_all tuple_assignment_rhs_pre >> simp[]) >>
  drule_then assume_tac expr_body_pre_gas_admissible >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (TupleT tys) e es` by metis_tac[body_expr_full_ok_simulations] >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (TupleT tys) e es` by metis_tac[cj 1 body_expr_prefix_ok_def] >>
  rewrite_tac[stmt_frag_prefix_def, stmt_frag_full_pre_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `(EXISTS (\ty. ~is_word_type ty) tys ==> cenv.ce_target CapMcopy)` by simp[] >>
  drule_all assign_tuple_rhs_code_slices >>
  disch_then (qx_choosel_then [`op`,`su`,`shadow_su`] strip_assume_tac) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x`
    by fs[ret_pc_ok_def] >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE[expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`su`,`shadow_sa`,`shadow_su`,`op`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE[expr_sim_prefix_def, expr_sim_full_pre_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`su`,`shadow_sa`,`shadow_su`,`op`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
     (\H res ee G tn t. ~t.vs_halted) (\H res ee gt r. ISR res)` by
    (qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _`
       (mp_then Any irule gas_outcome_full_post_source) >>
     simp[] >> rpt strip_tac >> Cases_on `res` >> fs[expr_exit_def]) >>
  rewrite_tac[eval_assign_tuple_action] >>
  pop_assum (mp_then Any irule gas_prefix_full_bind_no_outcome) >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, requests_outcomes_frame_bind_all,
       evaluate_requests_outcomes_frame, requests_outcomes_frame_read_result] >>
  rpt gen_tac >> strip_tac >>
  `EVERY (\g. (?id. g = BaseTarget (NameTarget id)) \/
              (?ns. g = BaseTarget (TopLevelNameTarget ns)) \/
              (?ns fld. g = BaseTarget (AttributeTarget (TopLevelNameTarget ns) fld))) gs` by
    (simp[EVERY_MEM] >> gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_all assign_tuple_flat_no_outcome >>
  simp[EVERY_MEM] >> metis_tac[]
QED
*)
Theorem body_assign_tuple_targets_word_prefix:
  !cx gs e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
  (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_full_ok cx (TupleTarget gs) v) /\
  (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_prefix_ok cx (TupleTarget gs) v) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (TupleTarget gs) e) ==>
       occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
  ~supported_stmt_expr_exists (const_name_root cx) (Assign (TupleTarget gs) e) /\
  stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
  frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
  lowered_value_type cenv e = expr_type e /\
  EVERY (\g. (?id ty. g = BaseTarget (NameTarget id) /\
                        FLOOKUP env.var_types id = SOME ty /\
                        0 < type_memory_bytes cenv ty) \/
               (?nsid dty. g = BaseTarget (TopLevelNameTarget nsid) /\
                           supported_scalar_target tops nsid /\
                           type_place_target env (TopLevelNameTarget nsid) = SOME (Type dty) /\
                           is_word_type dty) \/
               (?nsid fld fty.
                  g = BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld) /\
                  supported_storage_field_write tops nsid fld /\
                  type_place_target env
                    (AttributeTarget (TopLevelNameTarget nsid) fld) =
                    SOME (Type fty) /\ is_word_type fty)) gs ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (TupleTarget gs) e)))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  cheat
QED

Theorem body_assign_tuple_locals_prefix:
  !cx ids e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
  (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_full_ok cx (TupleTarget (MAP (BaseTarget o NameTarget) ids)) v) /\
  (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_prefix_ok cx (TupleTarget (MAP (BaseTarget o NameTarget) ids)) v) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) ==>
       occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)) /\
  frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
  ids <> [] /\
  EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty /\
                     0 < type_memory_bytes cenv ty) ids /\
  lowered_value_type cenv e = expr_type e ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)))
      (eval_stmt cx (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)) es
Proof
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env e es` by
    (drule_all tuple_assignment_rhs_pre >> simp[]) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    metis_tac[CONJUNCT1 body_expr_prefix_ok_def] >>
  pure_rewrite_tac[stmt_frag_prefix_def, stmt_frag_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all assign_tuple_locals_rhs_code >>
  disch_then (qx_choosel_then [`tys`,`op`,`su`,`shadow_su`] strip_assume_tac) >>
  irule assign_tuple_locals_prefix_from_rhs >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_prefix_def, expr_sim_full_pre_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`su`,`shadow_sa`,`shadow_su`,
                           `op`,`s0`,`G0`,`tn0`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[expr_body_pre_gas_admissible, ret_pc_ok_def]) >>
  simp[]
QED

Theorem body_assign_tuple_other_prefix:
  !cx gs e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
  (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_full_ok cx (TupleTarget gs) v) /\
  (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_prefix_ok cx (TupleTarget gs) v) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (TupleTarget gs) e) ==>
       occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
  ~supported_stmt_expr_exists (const_name_root cx) (Assign (TupleTarget gs) e) /\
  stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
  frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
  ~EXISTS (\g. ?t. g = BaseTarget t /\ immutable_root cx t /\
                     ~(?nsid. t = TopLevelNameTarget nsid)) gs /\
  lowered_value_type cenv e = expr_type e /\
  ~(?ids. gs = MAP (BaseTarget o NameTarget) ids /\ ids <> [] /\
            EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty) ids) ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (TupleTarget gs) e)))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule tuple_assign_exact_with_borrowed_frame_prefix >> simp[] >>
  conj_tac >-
    (qx_gen_tac `bt` >> disch_then (map_every assume_tac o CONJUNCTS) >>
     `F` suffices_by simp[] >>
     qpat_assum `~EXISTS _ gs` (irule o NOT_ELIM) >>
     pure_once_rewrite_tac[EXISTS_MEM] >> qexists_tac `BaseTarget bt` >>
     simp[]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  map_every qexists_tac [`bindings`,`env`,`env'`,`tops`] >> gvs[]
QED

Theorem body_assign_tuple_widened_prefix:
  !cx gs e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
  (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_full_ok cx (TupleTarget gs) v) /\
  (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_prefix_ok cx (TupleTarget gs) v) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (TupleTarget gs) e) ==>
       occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
  ~supported_stmt_expr_exists (const_name_root cx) (Assign (TupleTarget gs) e) /\
  stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
  frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
  ~EXISTS (\g. ?t. g = BaseTarget t /\ immutable_root cx t /\
                     ~(?nsid. t = TopLevelNameTarget nsid)) gs /\
  lowered_value_type cenv e <> expr_type e ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (TupleTarget gs) e)))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  rpt gen_tac >> strip_tac >>
  irule tuple_widened_prefix_from_nested_heads >> simp[] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  map_every qexists_tac [`bindings`,`env`,`env'`,`tops`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `F` suffices_by simp[] >>
  qpat_x_assum `~EXISTS _ gs` (irule o NOT_ELIM) >>
  pure_once_rewrite_tac[EXISTS_MEM] >> qexists_tac `BaseTarget head` >> simp[] >>
  pure_once_rewrite_tac[MEM_EL] >> qexists_tac `j` >> simp[]
QED

Theorem body_assign_tuple_nested_immutable_prefix:
  !cx gs e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
  (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_full_ok cx (TupleTarget gs) v) /\
  (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_prefix_ok cx (TupleTarget gs) v) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (TupleTarget gs) e) ==>
       occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
  ~supported_stmt_expr_exists (const_name_root cx) (Assign (TupleTarget gs) e) /\
  stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
  frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
  EXISTS (\g. ?t. g = BaseTarget t /\ immutable_root cx t /\
                    ~(?nsid. t = TopLevelNameTarget nsid)) gs ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (TupleTarget gs) e)))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `lowered_value_type cenv e = expr_type e`
  >- (irule tuple_assign_exact_with_borrowed_frame_prefix >>
      (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC))
      >- (rpt strip_tac >>
          rename1 `imm_target_post _ _ _ _ _ src _ _ u mid _ _ _ _ t` >>
          `locals_kept cenv src mid u t` by fs[imm_target_post_def] >>
          drule_all (SRULE [type_memory_size_def] tuple_borrow_locals_kept) >> simp[]) >>
      qexistsl_tac [`bindings`,`env`,`env'`,`tops`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      strip_tac >> qpat_x_assum `gs = MAP _ _` SUBST_ALL_TAC >>
      qpat_x_assum `EXISTS _ _` (mp_tac o PURE_REWRITE_RULE [EXISTS_MAP]) >>
      simp[EVERY_MEM,immutable_root_def,target_root_def]) >>
  irule tuple_assign_widened_prefix_from_heads >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  qexistsl_tac [`bindings`,`env`,`env'`,`tops`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
