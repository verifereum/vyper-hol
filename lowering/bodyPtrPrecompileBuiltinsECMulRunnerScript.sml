Theory bodyPtrPrecompileBuiltinsECMulRunner
Ancestors bodyPtrPrecompileBuiltinsCases bodyPtrPrecompileBuiltinsOperandCompose
          bodyPtrPrecompileBuiltinsOperandTransport
          bodyPtrPrecompileBuiltinsTailSummary bodyPtrPrecompileBuiltinsArithmeticTail
          bodyPtrPrecompileBuiltinsCompilerStages
          bodyPtrPrecompileBuiltinsPlacement exprSimHypsDefs
          vyperTypeSystem exprLoweringProps exprLowering emitHelper compileEnv exprSimWordArgs exprSimECArith vyperInterpreter vyperState vyperContext

Theorem ecmul_body_pre_shape[local]:
  expr_body_pre cenv cx env (Builtin ann ECMul args) es ==>
  ann = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  ?a b. args = [a;b] /\
    expr_type a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
    expr_type b = BaseT (UintT 256)
Proof
  simp[expr_body_pre_def, well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `well_typed_builtin_app _ ECMul _` mp_tac >>
  simp[well_typed_builtin_app_def] >>
  Cases_on `args` >> gvs[] >> Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[]
QED

Theorem ecmul_compile_operands[local]:
  compile_expr cenv ty (Builtin ann ECMul [a;b]) sa = (vv,sb) ==>
  ?p scalar s1 sm res.
    lower_value compile_expr cenv (expr_type a) a sa = (p,s1) /\
    lower_value compile_expr cenv (BaseT (UintT 256)) b s1 = (scalar,sm) /\
    compile_ecmul_point p scalar sm = (res,sb) /\
    vv = FST (as_ptr_val ann LocMemory (res,sb))
Proof
  `compile_expr cenv ty (Builtin ann ECMul [a;b]) sa =
    compile_builtin_dispatch cenv ann ty ECMul [a;b] sa` by
    (irule compile_expr_builtin_dispatch >>
     Cases_on `a` >> simp[names_builtin_def] >>
     Cases_on `b` >> simp[names_builtin_def]) >>
  simp[] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def, lower_value_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `as_ptr_val ann LocMemory result` >>
  Cases_on `result` >> gvs[as_ptr_val_def]
QED

Theorem ec_eval_source_bind:
  (bt = ECAdd \/ bt = ECMul) ==>
  eval_expr cx (Builtin ann bt [a;b]) =
  bind (bind (eval_expr cx a) (read_result cx))
    (\v1. bind (bind (eval_expr cx b) (read_result cx))
      (\v2. ec_source_tail cx ann bt [expr_type a;expr_type b] [v1;v2]))
Proof
  strip_tac >>
  `eval_expr cx (Builtin ann bt [a;b]) =
   bind (eval_exprs cx [a;b])
     (\vs. ec_source_tail cx ann bt (MAP expr_type [a;b]) vs)` by
    (simp[FUN_EQ_THM, Once evaluate_def, bind_def, ignore_bind_def,
          type_check_def, assert_def, return_def, raise_def,
          builtin_args_length_ok_def] >>
     gen_tac >> Cases_on `eval_exprs cx [a;b] x` >>
     rename1 `eval_exprs cx [a;b] x = (rr,ee)` >> Cases_on `rr` >>
     simp[bind_def, return_def, get_accounts_def, lift_sum_def,
          builtin_result_def, ec_source_tail_def, ignore_bind_def] >>
     Cases_on `evaluate_builtin cx ee.accounts ann bt [expr_type a;expr_type b] x'` >>
     Cases_on `precompile_call_success bt ee` >>
     rename1 `precompile_call_success bt ee = (out,ee2)` >>
     Cases_on `out` >>
     gvs[return_def, raise_def, ignore_bind_def, bind_def, AllCaseEqs()] >>
     metis_tac[]) >>
  `eval_exprs cx [] = return []` by
    simp[FUN_EQ_THM, eval_exprs_nil, return_def] >>
  asm_rewrite_tac[eval_exprs_cons_action] >>
  simp[bind_assoc, bind_return]
QED

Theorem precompile_operand_source_facts:
  expr_body_pre cenv cx env e es /\
  gas_outcome_ptr D tops (ctx,fn) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0) Q R ==>
  gas_outcome_ptr D tops (ctx,fn) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\rr ee G tn t. Q rr ee G tn t /\ expr_sim_inv cenv cx env ee /\
       (!v. rr = INL v ==> expr_result_typed env e (Value v)) /\
       MAP FDOM es.scopes = MAP FDOM ee.scopes /\
       ee.gas_obs = [] /\ ~t.vs_halted) R
Proof
  strip_tac >>
  irule gasSummaryComposePtrTheory.gas_outcome_ptr_conseq >>
  irule_at Any typedWordArgsFactsPtrTheory.gas_outcome_ptr_source_facts >>
  goal_assum (drule_at Any) >>
  qexists `\rr ee. expr_sim_inv cenv cx env ee /\
    (!v. rr = INL v ==> expr_result_typed env e (Value v)) /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes` >>
  simp[] >> rpt strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by
    fs[expr_body_pre_def] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV)
    exprSimSourceTheory.expr_body_pre_eval) >> strip_tac >> simp[] >>
  drule (CONV_RULE (DEPTH_CONV ETA_CONV)
    forced_eval_expr_preserves_scopes_dom) >> simp[]
QED

Theorem ecmul_expr_vv_sim_ptr:
  (builtin_args_length_ok ECMul (LENGTH args) ==> body_exprs_ptr_ok cx args) /\
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann ECMul args) es ==>
  expr_vv_sim_ptr d ctx PG fn cenv cx ty (Builtin ann ECMul args) es
Proof
  strip_tac >> drule ecmul_body_pre_shape >> strip_tac >> gvs[] >>
  `body_exprs_ptr_ok cx [a;b]` by
    fs[builtin_args_length_ok_def] >>
  rewrite_tac[bodyPtrDefsTheory.expr_vv_sim_ptr_def] >> rpt strip_tac >>
  drule ecmul_compile_operands >> strip_tac >> gvs[] >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `expr_body_pre cenv cx env a es` by
    (drule exprSimSourceTheory.expr_body_pre_builtin_arg >>
     simp[expr_body_pre_def] >>
     disch_then (qspecl_then [`a`, `es`] mp_tac) >> simp[]) >>
  `post_value_type cenv a = expr_type a` by
    (irule exprSimHypsTheory.post_value_type_ec_point >> simp[] >>
     qexistsl_tac [`cx`,`env`,`es`] >> fs[expr_body_pre_def]) >>
  `expr_sim_ptr d ctx PG fn cenv cx (expr_type a) a es` by
    metis_tac[body_expr_ptr_frame, body_exprs_ptr_head] >>
  drule bodyPtrPrecompileBuiltinsArithmeticTailTheory.ecmul_compiler_append >>
  strip_tac >>
  `cs_extends sm sb` by
    (simp[cs_extends_def] >> qexists `[]` >>
     gvs[rich_listTheory.IS_PREFIX_APPEND, same_blocks_def]) >>
  qpat_assum `lower_value _ _ _ a _ = _`
    (mp_then Any mp_tac (cj 2 compile_expr_grows)) >> strip_tac >>
  qpat_assum `lower_value _ _ _ b _ = _`
    (mp_then Any mp_tac (cj 2 compile_expr_grows)) >> strip_tac >>
  `cs_extends s1 sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 fn /\ fn_has_code s1 sb fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `gas_admissible (bind (eval_expr cx a) (read_result cx)) expr_res_ok es` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.expr_sim_ptr_def]) >>
  simp[] >> disch_then drule >> simp[] >>
  disch_then (qspecl_then [`s0`, `G0`, `tn0`] mp_tac) >> simp[] >>
  strip_tac >>
  drule_all precompile_operand_source_facts >> strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ (\res ee G tn t. ?v. _) _` kall_tac >>
  simp[ec_eval_source_bind] >>
  qmatch_asmsub_abbrev_tac `gas_outcome_ptr _ _ _ _ _ _ P _` >>
  irule pointer_outcome_bind_success >> qexists `P` >>
  reverse conj_tac
  >- (irule gasSummaryComposePtrTheory.gas_outcome_ptr_conseq >>
      goal_assum (drule_at Any) >>
      simp[exprSimDefsTheory.expr_exit_def] >>
      rpt strip_tac >> Cases_on `res'` >>
      gvs[exprSimDefsTheory.expr_exit_def, stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt strip_tac >> suspend "point_continuation"
QED

Resume ecmul_expr_vv_sim_ptr[point_continuation]:
  gvs[Abbr `P`] >>
  `body_exprs_ptr_ok cx [b]` by
    metis_tac[body_exprs_ptr_tail_force] >>
  `expr_body_pre cenv cx env b ee` by
    (drule exprSimSourceTheory.expr_body_pre_builtin_arg >>
     disch_then (qspecl_then [`b`, `ee`] mp_tac) >> simp[]) >>
  `expr_sim_ptr d ctx PG fn cenv cx (expr_type b) b ee` by
    metis_tac[body_expr_ptr_frame, body_exprs_ptr_head] >>
  `local_ptrs_reserved cenv s1` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `fn_has_code s1 sm fn /\ fn_has_code sm sb fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `stmt_state_rel ctx fn cenv cx ee t` by
    fs[loweringPostsTheory.expr_post_def] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at s1 x` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at s1 x` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `gas_admissible (bind (eval_expr cx b) (read_result cx)) expr_res_ok ee` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.expr_sim_ptr_def]) >>
  simp[] >> disch_then drule >> simp[] >>
  disch_then (qspecl_then [`t`, `G`, `tn`] mp_tac) >> simp[] >>
  strip_tac >>
  drule_all precompile_operand_source_facts >> strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ (\res ee G tn t. ?v. _) _` kall_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ (es,_,_,_) _ _` kall_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_ptr _ _ _ _ _ _ P2 _` >>
  irule pointer_outcome_bind_success >> qexists `P2` >>
  reverse conj_tac
  >- (irule gasSummaryComposePtrTheory.gas_outcome_ptr_conseq >>
      goal_assum (drule_at Any) >>
      simp[exprSimDefsTheory.expr_exit_def] >>
      rpt strip_tac >> Cases_on `res'` >>
      gvs[exprSimDefsTheory.expr_exit_def, stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt strip_tac >> gvs[Abbr `P2`] >> suspend "scalar_continuation"
QED

Resume ecmul_expr_vv_sim_ptr[scalar_continuation]:
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` kall_tac >>
  `value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v /\
   value_has_type (BaseTV (UintT 256)) v'` by
    gvs[vyperTypeExprResultTheory.expr_result_typed_def,
        vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
        vyperTypeExprSoundnessTheory.value_runtime_typed_def,
        vyperTypeInvariantsTheory.value_result_typed_def, vyperValueTheory.evaluate_type_def] >>
  `!z. p = Var z ==> not_fresh_at s1 z` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `?w. eval_operand p t = SOME w` by
    fs[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def] >>
  `?z. p = Var z` by
    (qpat_assum `ptr_val_ok _ (ArrayT _ _) _ _ _ _ _`
       (mp_then Any mp_tac representationCleanPtrTheory.ptr_val_ok_read_covers) >>
     simp[is_word_type_def, vyperValueTheory.evaluate_type_def,
          loweringPostsTheory.val_footprint_def, valueEncodingTheory.type_memory_size_def] >>
     Cases_on `v` >>
     simp[vyperValueTheory.type_slot_size_def, wordsTheory.dimword_def] >>
     disch_then (qspec_then `0` mp_tac) >> simp[] >> metis_tac[]) >>
  `!l. p <> Label l` by simp[] >>
  `!w. eval_operand p t = SOME w ==> eval_operand p t' = SOME w` by
    metis_tac[exprSimOperandsTheory.expr_post_operand_word, optionTheory.SOME_11] >>
  `post_value_type cenv a = expr_type a` by fs[] >>
  `expr_val_rel cx (expr_type a) v p t' /\
   expr_val_at cenv cx (expr_type a) sa sm ee' v p t'` by
    (drule_all ec_point_operand_kept >> simp[]) >>
  `ptr_val_ok cx (expr_type a) v p G tn t` by fs[] >>
  `ptr_val_ok cx (expr_type a) v p G' tn' t'` by
    (drule_all ec_point_ptr_operand_kept >> simp[]) >>
  suspend "tail_frame"
QED

Resume ecmul_expr_vv_sim_ptr[tail_frame]:
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `stmt_state_rel ctx fn cenv cx ee' t'` by fs[loweringPostsTheory.expr_post_def] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `!x. MEM (Var x) [p;scalar] ==> not_fresh_at sm x` by
    (simp[] >> metis_tac[exprOperandVarTheory.compile_lower_value_var,
                        stmtFragPtrTheory.not_fresh_at_mono]) >>
  `op_taint tn' scalar = {}` by
    fs[bodyPtrDefsTheory.ptr_val_ok_def, is_word_type_def] >>
  `safe_operand sm scalar` by
    (irule exprWordOperandTheory.lower_value_word_safe_operand >>
     goal_assum (drule_at Any) >> simp[is_word_type_def] >>
     metis_tac[exprSimSourceTheory.expr_body_pre_var_types_well_formed,
               expr_body_pre_def]) >>
  `!l. scalar <> Label l` by fs[exprSafeOperandTheory.safe_operand_def] >>
  `!i. MEM i (emitted_insts sm sb) ==> MEM i (fn_insts fn)` by
    metis_tac[exprSimHashTheory.hash_emitted_inst_mem] >>
  drule_all precompile_tail_placement >> strip_tac >>
  Cases_on `ec_source_tail cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECMul
    [ArrayT (BaseT (UintT 256)) (Fixed 2); BaseT (UintT 256)] [v;v'] ee'` >>
  rename1 `ec_source_tail _ _ _ _ _ _ = (rr,fin)` >>
  `expr_val_rel cx (BaseT (UintT 256)) v' scalar t'` by
    (`post_value_type cenv b = expr_type b` by
       (irule loweringPostsTheory.post_value_type_word >> fs[is_word_type_def]) >>
     fs[loweringPostsTheory.expr_post_def] >>
     qpat_x_assum `expr_val_rel _ (expr_type b) _ _ _` mp_tac >>
     qpat_assum `expr_type b = _` (fn th => rewrite_tac[th])) >>
  `stor_taint_ok cx tn' t'` by fs[bodyPtrDefsTheory.ghost_inv_def] >>
  fs[bodyPtrDefsTheory.stor_taint_ok_def] >>
  `expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) sa sm ee' v p t' /\
   ptr_val_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v p G' tn' t' /\
   expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v p t'` by
    (qpat_assum `expr_type a = _` (fn th => pure_rewrite_tac[GSYM th]) >> simp[]) >>
  gvs[] >> suspend "tail_path"
QED

Resume ecmul_expr_vv_sim_ptr[tail_path]:
  qpat_assum `compile_ecmul_point _ _ _ = _`
    (mp_then Any (fn th =>
      qpat_assum `stmt_state_rel _ _ _ _ ee' t'`
        (mp_then Any (fn th =>
          qpat_assum `ghost_inv _ _ _ ee' G' tn' t'`
            (mp_then Any (fn th =>
              qpat_assum `expr_val_at _ _ (ArrayT _ _) sa sm ee' _ _ t'`
                (mp_then Any (fn th =>
                  qpat_assum `ec_source_tail _ _ _ _ _ ee' = _`
                    (mp_then Any mp_tac th)) th)) th)) th))
      ecmul_source_tail_ptr_path) >>
  disch_then (qspecl_then [`bb`,`[a;b]`,`PG`,`cx_dead cx`] mp_tac) >>
  simp[] >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  suspend "tail_outcome"
QED

Resume ecmul_expr_vv_sim_ptr[tail_outcome]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  `ee' with gas_obs := [] = ee'` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `fin with gas_obs := [] = fin` by
    (drule ec_source_tail_gas_obs >> disch_then (qspec_then `[]` mp_tac) >>
     simp[] >> gvs[]) >>
  irule ec_source_tail_pointer_outcome >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[] >>
  simp[vyperASTTheory.expr_type_def, as_ptr_val_def] >> suspend "entry_rebase"
QED

Resume ecmul_expr_vv_sim_ptr[entry_rebase]:
  `wb_frame cenv es sa s0 t` by metis_tac[expr_post_frame] >>
  `wb_frame cenv ee s1 t t'` by metis_tac[expr_post_frame] >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by decide_tac >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by metis_tac[] >>
  `wb_frame cenv es sa s0 t'` by
    (drule_all wb_frame_trans >> simp[]) >>
  `ghost_kept cenv es sa G0 tn0 s0 G' tn'` by
    (irule wordArgsPtrTheory.ghost_kept_wb_trans >>
     qpat_assum `ghost_kept _ ee s1 _ _ _ G' tn'` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  `ghost_kept cenv es sa G0 tn0 s0 G'' tn''` by
    (irule wordArgsPtrTheory.ghost_kept_wb_trans >>
     qpat_assum `ghost_kept _ ee' sm _ _ _ G'' tn''` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  fs[as_ptr_val_def, contextTheory.mk_ptr_def] >>
  irule exprSimCalldataSliceTheory.vv_post_prefix_frame >>
  qpat_assum `vv_post _ _ _ _ _ ee' sm _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> metis_tac[]
QED

Finalise ecmul_expr_vv_sim_ptr
