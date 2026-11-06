Theory bodyPtrPrecompileBuiltinsECAddRunner
Ancestors bodyPtrPrecompileBuiltinsArithmeticCompose
          bodyPtrPrecompileBuiltinsOperandTransport
          bodyPtrPrecompileBuiltinsTailSummary bodyPtrPrecompileBuiltinsArithmeticTail
          bodyPtrPrecompileBuiltinsCompilerStages bodyPtrPrecompileBuiltinsPlacement
          vyperTypeSystem exprLoweringProps exprLowering emitHelper compileEnv
          exprSimHypsDefs exprSimECArith vyperInterpreter vyperState vyperContext

Theorem ecadd_body_pre_shape[local]:
  expr_body_pre cenv cx env (Builtin ann ECAdd args) es ==>
  ann = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  ?a b. args = [a;b] /\
    expr_type a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
    expr_type b = ArrayT (BaseT (UintT 256)) (Fixed 2)
Proof
  simp[expr_body_pre_def, well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `well_typed_builtin_app _ ECAdd _` mp_tac >>
  simp[well_typed_builtin_app_def] >>
  Cases_on `args` >> gvs[] >> Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[]
QED

Theorem ecadd_compile_operands[local]:
  compile_expr cenv ty (Builtin ann ECAdd [a;b]) sa = (vv,sb) ==>
  ?p q s1 sm res.
    lower_value compile_expr cenv (expr_type a) a sa = (p,s1) /\
    lower_value compile_expr cenv (expr_type b) b s1 = (q,sm) /\
    compile_ecadd_points p q sm = (res,sb) /\
    vv = FST (as_ptr_val ann LocMemory (res,sb))
Proof
  `compile_expr cenv ty (Builtin ann ECAdd [a;b]) sa =
    compile_builtin_dispatch cenv ann ty ECAdd [a;b] sa` by
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

local
fun ecadd_start () = (
  strip_tac >> drule ecadd_body_pre_shape >> strip_tac >> gvs[] >>
  `body_exprs_ptr_ok cx [a;b]` by fs[builtin_args_length_ok_def] >>
  rewrite_tac[bodyPtrDefsTheory.expr_vv_sim_ptr_def] >> rpt strip_tac >>
  drule ecadd_compile_operands >> strip_tac >> gvs[] >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `expr_body_pre cenv cx env a es` by
    (drule exprSimSourceTheory.expr_body_pre_builtin_arg >>
     simp[expr_body_pre_def] >>
     disch_then (qspecl_then [`a`,`es`] mp_tac) >> simp[]) >>
  `expr_sim_ptr d ctx PG fn cenv cx (expr_type a) a es` by
    metis_tac[bodyPtrPrecompileBuiltinsCasesTheory.body_expr_ptr_frame,
              bodyPtrPrecompileBuiltinsCasesTheory.body_exprs_ptr_head] >>
  drule ecadd_compiler_append >> strip_tac >>
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
  simp[bodyPtrPrecompileBuiltinsECMulRunnerTheory.ec_eval_source_bind] >>
  irule precompile_operand_bind_ptr >> simp[] >>
  qexistsl [`cenv`,`d`,`env`,`p`,`sa`,`s1`,`expr_type a`] >>
  simp[] >> rpt strip_tac);

fun ecadd_second () = (
  `body_exprs_ptr_ok cx [b]` by
    metis_tac[bodyPtrPrecompileBuiltinsCasesTheory.body_exprs_ptr_tail_force] >>
  `expr_body_pre cenv cx env b ee` by
    (drule exprSimSourceTheory.expr_body_pre_builtin_arg >>
     disch_then (qspecl_then [`b`,`ee`] mp_tac) >> simp[]) >>
  `expr_sim_ptr d ctx PG fn cenv cx (expr_type b) b ee` by
    metis_tac[bodyPtrPrecompileBuiltinsCasesTheory.body_expr_ptr_frame,
              bodyPtrPrecompileBuiltinsCasesTheory.body_exprs_ptr_head] >>
  `local_ptrs_reserved cenv s1` by metis_tac[local_ptrs_reserved_next_var] >>
  `fn_has_code s1 sm fn /\ fn_has_code sm sb fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `stmt_state_rel ctx fn cenv cx ee t` by fs[loweringPostsTheory.expr_post_def] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at s1 x` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at s1 x` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `gas_admissible (bind (eval_expr cx b) (read_result cx)) expr_res_ok ee` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  irule precompile_operand_bind_ptr >> simp[] >>
  qexistsl [`cenv`,`d`,`env`,`q`,`s1`,`sm`,`expr_type b`] >>
  simp[] >> rpt strip_tac);
in
fun ecadd_prefix () = ecadd_start () >> ecadd_second ();
end

Theorem ecadd_expr_vv_sim_ptr:
  (builtin_args_length_ok ECAdd (LENGTH args) ==> body_exprs_ptr_ok cx args) /\
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann ECAdd args) es ==>
  expr_vv_sim_ptr d ctx PG fn cenv cx ty (Builtin ann ECAdd args) es
Proof
  ecadd_prefix () >> suspend "points"
QED

Resume ecadd_expr_vv_sim_ptr[points]:
  `value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v /\
   value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v'` by
    gvs[vyperTypeExprResultTheory.expr_result_typed_def,
        vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
        vyperTypeExprSoundnessTheory.value_runtime_typed_def,
        vyperTypeInvariantsTheory.value_result_typed_def, vyperValueTheory.evaluate_type_def] >>
  `!z. p = Var z ==> not_fresh_at s1 z` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `?w. eval_operand p t = SOME w` by
    fs[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def] >>
  `?z. p = Var z` by
    (qpat_assum `ptr_val_ok _ (ArrayT _ _) _ p _ _ _`
       (mp_then Any mp_tac representationCleanPtrTheory.ptr_val_ok_read_covers) >>
     simp[is_word_type_def, vyperValueTheory.evaluate_type_def,
          loweringPostsTheory.val_footprint_def, valueEncodingTheory.type_memory_size_def] >>
     Cases_on `v` >>
     simp[vyperValueTheory.type_slot_size_def, wordsTheory.dimword_def] >>
     disch_then (qspec_then `0` mp_tac) >> simp[] >> metis_tac[]) >>
  `!l. p <> Label l` by simp[] >>
  `!w. eval_operand p t = SOME w ==> eval_operand p t' = SOME w` by
    metis_tac[exprSimOperandsTheory.expr_post_operand_word, optionTheory.SOME_11] >>
  `expr_val_rel cx (expr_type a) v p t' /\
   expr_val_at cenv cx (expr_type a) sa sm ee' v p t'` by
    (drule_all ec_point_operand_kept >> simp[]) >>
  `ptr_val_ok cx (expr_type a) v p G tn t` by fs[] >>
  `ptr_val_ok cx (expr_type a) v p G' tn' t'` by
    (drule_all ec_point_ptr_operand_kept >> simp[]) >>
  suspend "tail_frame"
QED

Resume ecadd_expr_vv_sim_ptr[tail_frame]:
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `stmt_state_rel ctx fn cenv cx ee' t'` by fs[loweringPostsTheory.expr_post_def] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `!x. MEM (Var x) [p;q] ==> not_fresh_at sm x` by
    (simp[] >> metis_tac[exprOperandVarTheory.compile_lower_value_var,
                        stmtFragPtrTheory.not_fresh_at_mono]) >>
  `!i. MEM i (emitted_insts sm sb) ==> MEM i (fn_insts fn)` by
    metis_tac[exprSimHashTheory.hash_emitted_inst_mem] >>
  drule_all precompile_tail_placement >> strip_tac >>
  `expr_val_at cenv cx (expr_type b) sa sm ee' v' q t'` by
    (irule exprSimPropsTheory.expr_val_at_start_mono >>
     qexists `s1` >> fs[loweringPostsTheory.expr_post_def]) >>
  `expr_val_at cenv cx (expr_type a) sa sm ee' v p t' /\
   ptr_val_ok cx (expr_type a) v p G' tn' t' /\
   expr_val_rel cx (expr_type a) v p t' /\
   expr_val_rel cx (expr_type b) v' q t'` by fs[loweringPostsTheory.expr_post_def] >>
  `stor_taint_ok cx tn' t'` by fs[bodyPtrDefsTheory.ghost_inv_def] >>
  fs[bodyPtrDefsTheory.stor_taint_ok_def] >>
  Cases_on `ec_source_tail cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECAdd
    [expr_type a;expr_type b] [v;v'] ee'` >>
  rename1 `ec_source_tail _ _ _ _ _ _ = (rr,fin)` >>
  gvs[] >> suspend "tail_path"
QED

Resume ecadd_expr_vv_sim_ptr[tail_path]:
  qpat_assum `ec_source_tail _ _ _ _ _ _ = _`
    (mp_then Any mp_tac ecadd_source_tail_ptr_path) >>
  disch_then (fn th => qpat_assum `compile_ecadd_points _ _ _ = _`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `stmt_state_rel _ _ _ _ ee' t'`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `ghost_inv _ _ _ ee' G' tn' t'`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `expr_val_at _ _ _ sa sm ee' v _ t'`
    (mp_then Any mp_tac th)) >>
  disch_then (qspecl_then [`bb`,`[a;b]`,`PG`,`cx_dead cx`] mp_tac) >>
  simp[] >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  suspend "tail_outcome"
QED

Resume ecadd_expr_vv_sim_ptr[tail_outcome]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  `ee' with gas_obs := [] = ee'` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `fin with gas_obs := [] = fin` by
    (drule ec_source_tail_gas_obs >> disch_then (qspec_then `[]` mp_tac) >>
     simp[] >> gvs[]) >>
  irule ec_source_tail_pointer_outcome >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[] >>
  simp[vyperASTTheory.expr_type_def, as_ptr_val_def] >>
  suspend "entry_rebase"
QED

Resume ecadd_expr_vv_sim_ptr[entry_rebase]:
  fs[as_ptr_val_def, contextTheory.mk_ptr_def] >>
  irule precompile_two_operand_entry_rebase >>
  qpat_assum `vv_post _ _ _ _ _ ee' sm _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_post _ _ _ _ b _ s1 sm _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_post _ _ _ _ a _ sa s1 _ _ _ _ _` (irule_at Any) >>
  simp[] >> metis_tac[]
QED

Finalise ecadd_expr_vv_sim_ptr
