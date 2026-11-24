(*
 * Construct-free facts the joint (full) expression leaves share.
 *
 * TOP-LEVEL:
 *   expr_vv_sim_stack_full -- an expression that compiles to a stack value
 *     and evaluates to a value gets its vv judgment from its value judgment
 *   gas_shadow_compiles_alloc_buffer -- a static buffer allocation compiles
 *     alike on both sides of the shadow
 *)
Theory bodyFullExprGeneric
Ancestors
  bodySimFull gasShadowState gasShadow context exprLowering compileEnv
  vyperInterpreter vyperState exprSimStack exprSimMemDefs gasOutcomeFull gasStorage
  bodyPtrDefs loweringPosts exprSimDefs gasOutcomeFullCompose

Theorem gas_outcome_full_force_value:
  (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn) Q R ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (eval_expr cx e) (es,s,G,tn)
    (\H raw ee G tn t. ?res.
      raw = (case res of INL v => INL (Value v) | INR ex => INR ex) /\
      Q H res ee G tn t)
    (\H raw ee gt r. ?res.
      raw = (case res of INL v => INL (Value v) | INR ex => INR ex) /\
      R H res ee gt r)
Proof
  strip_tac >>
  ho_match_mp_tac (GEN_ALL gas_outcome_full_source_map) >>
  qexists_tac `bind (eval_expr cx e) (read_result cx)` >> simp[] >>
  qx_gen_tac `st` >>
  Cases_on `bind (eval_expr cx e) (read_result cx) st` >>
  drule_all eval_expr_force_value >> simp[]
QED

(* The semantic stack post depends only on the physical endpoint and the
   lowered layout, not on the path summary used to get to that endpoint. *)
Theorem expr_stack_value_post:
  compile_expr cenv ty e sa = (StackValue ann op,sb) /\
  (~is_word_type (post_value_type cenv e) ==>
    !tvt. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tvt ==>
          type_memory_size tvt = 0) /\
  expr_post H ctx func cenv cx e es sa sb s0 ee v op t /\
  expr_store_bound cx (post_value_type cenv e) v op t ==>
  vv_post H ctx func cenv cx e es sa sb s0 ee (Value v) (StackValue ann op) t /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
    ee (Value v) (StackValue ann op) t /\
  (~is_word_type (post_value_type cenv e) /\ ~is_bytestring_type (post_value_type cenv e) ==>
   vv_own cenv cx (post_value_type cenv e) sa sb ee (Value v) (StackValue ann op) t)
Proof
  strip_tac >> conj_tac
  >- (gvs[expr_post_def, vv_post_def, vv_holds_def, vv_at_def, vv_own_def,
          read_result_def, return_def] >> first_assum ACCEPT_TAC) >>
  conj_tac >- (irule vv_store_bound_stack_value >> simp[]) >>
  simp[vv_own_def, read_result_def, return_def, expr_val_own_def] >>
  rpt strip_tac >>
  `post_value_type cenv e = lowered_value_type cenv e` by
    (qpat_x_assum `compile_expr cenv ty e sa = _` mp_tac >>
     qpat_x_assum `~is_word_type _` mp_tac >>
     qpat_x_assum `~is_bytestring_type _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     map_every qid_spec_tac [`sa`, `ty`, `e`, `cenv`] >>
     ho_match_mp_tac lowered_value_type_ind >>
     rw[post_value_type_def, lowered_value_type_def,
        vyperASTTheory.expr_type_def, is_bytestring_type_def]
     >~ [`compile_expr _ _ (Builtin _ (Concat _) _) _ = _`]
     >- (qpat_x_assum `compile_expr _ _ (Builtin _ (Concat _) _) _ = _` mp_tac >>
         rpt (pop_assum kall_tac) >>
         `!n args. ~exprSimHypsDefs$names_builtin (Concat n) args` by
           (`!bt args. exprSimHypsDefs$names_builtin bt args ==>
                       !n. bt <> Concat n` suffices_by metis_tac[] >>
            ho_match_mp_tac exprSimHypsDefsTheory.names_builtin_ind >>
            simp[exprSimHypsDefsTheory.names_builtin_def]) >>
         simp[exprSimHypsDefsTheory.compile_expr_builtin_dispatch] >>
         ONCE_REWRITE_TAC [compile_builtin_dispatch_component_eq] >>
         simp[] >> strip_tac >> rpt (pairarg_tac >> gvs[])) >>
     qpat_x_assum `compile_expr _ _ (TypeBuiltin _ (AbiEncode _ _) _ _) _ = _`
       mp_tac >> rpt (pop_assum kall_tac) >>
     ONCE_REWRITE_TAC [compile_expr_component_eq] >>
     simp[vyperASTTheory.expr_type_def, vyperASTTheory.expr_size_def] >>
     ONCE_REWRITE_TAC [compile_type_builtin_dispatch_component_eq] >>
     simp[AllCaseEqs(), as_ptr_val_def] >> rpt strip_tac >>
     rpt (pairarg_tac >> gvs[as_ptr_val_def]) >>
     qmatch_asmsub_abbrev_tac `as_ptr_val _ _ encoded` >>
     Cases_on `encoded` >> gvs[as_ptr_val_def]) >>
  `type_memory_size tv = 0` by metis_tac[] >>
  `val_footprint tv v = 0` by
    (Cases_on `v` >> simp[val_footprint_def] >>
     Cases_on `tv` >> gvs[valueEncodingTheory.type_memory_size_def] >>
     rename1 `BaseTV bt` >> Cases_on `bt` >>
     gvs[valueEncodingTheory.type_memory_size_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[valueEncodingTheory.type_memory_size_def]) >>
  gvs[expr_post_def, expr_val_rel_def]
QED

(* The full twin of exprStackPtr's expr_vv_sim_stack_ptr.  As in the memory
   twin (exprSimMemoryStack's body_expr_vv_sim_mem_stack), a non-word stack
   value's lowered type must take no memory: expr_sim_full bounds only the
   value's footprint, and vv_store_bound also wants the whole lowered
   type's region below the frontier. *)
Theorem expr_vv_sim_stack_full:
  !DF lo d ctx shadow_ctx PG func shadow_func cenv cx ty e es.
    (~is_word_type (post_value_type cenv e) ==>
     !tvt. evaluate_type (get_tenv cx) (lowered_value_type cenv e) =
             SOME tvt ==>
           type_memory_size tvt = 0) /\
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty e es /\
    (!sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op,sb)) /\
    (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) ==>
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty e es
Proof
  rw[expr_vv_sim_full_def] >>
  qpat_x_assum `!sa. ?t op sb. _` (qspec_then `sa` strip_assume_tac) >> gvs[] >>
  `lower_value compile_expr cenv ty e sa = (op,sb)` by
    simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
  `lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa =
     (op,shadow_sb)` by
    simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[eval_expr_force_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  simp[expr_sim_full_def] >> disch_then drule_all >> disch_tac >>
  drule_all gas_outcome_full_force_value >> strip_tac >>
  irule gas_outcome_full_post_mono >> goal_assum (drule_at Any) >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
      qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
      drule_all expr_stack_value_post >> strip_tac >>
      simp[ptr_vv_ok_def, vv_location_def, read_result_def, return_def] >>
      metis_tac[]) >>
  rpt strip_tac >> gvs[AllCaseEqs(), expr_exit_success_map, halt_exit_def] >>
  rename1 `expr_exit (INR exc) result` >>
  Cases_on `result` >> Cases_on `exc` >> gvs[expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[expr_exit_def]
QED

Theorem gas_shadow_compiles_alloc_buffer:
  !size. gas_shadow_compiles (compile_alloc_buffer size)
           (compile_alloc_buffer size)
Proof
  simp[compile_alloc_buffer_def] >> gen_tac >>
  irule gas_shadow_compiles_bind >>
  simp[gas_shadow_compiles_emit_op, gas_shadow_compiles_return]
QED
