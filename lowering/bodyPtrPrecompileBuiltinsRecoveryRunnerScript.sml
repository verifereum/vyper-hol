Theory bodyPtrPrecompileBuiltinsRecoveryRunner
Ancestors bodyPtrPrecompileBuiltinsArithmeticCompose bodyPtrPrecompileBuiltinsRecoveryTail
          bodyPtrPrecompileBuiltinsWordRetention bodyPtrPrecompileBuiltinsTailSummary
          vyperTypeSystem exprLoweringProps exprLowering emitHelper compileEnv
          exprSimHypsDefs exprSimWordArgs exprSimPrecompiles vyperInterpreter vyperState vyperContext

Theorem recovery_body_pre_shape:
  expr_body_pre cenv cx env (Builtin ann ECRecover args) es ==>
  ann = BaseT AddressT /\
  ?ah av ar aq. args = [ah;av;ar;aq] /\
    expr_type ah = BaseT (BytesT (Fixed 32)) /\
    (expr_type av = BaseT (UintT 8) \/ expr_type av = BaseT (UintT 256) \/
     expr_type av = BaseT (BytesT (Fixed 32))) /\
    (expr_type ar = BaseT (UintT 256) \/ expr_type ar = BaseT (BytesT (Fixed 32))) /\
    (expr_type aq = BaseT (UintT 256) \/ expr_type aq = BaseT (BytesT (Fixed 32)))
Proof
  simp[expr_body_pre_def, well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `well_typed_builtin_app _ ECRecover _` mp_tac >>
  simp[well_typed_builtin_app_def] >>
  Cases_on `args` >> gvs[] >> Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >> Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[]
QED

Theorem recovery_compile_operands:
  compile_expr cenv ty (Builtin ann ECRecover [ah;av;ar;aq]) sa = (vv,sb) ==>
  ?h v r q s1 s2 s3 sm res.
    lower_value compile_expr cenv ty ah sa = (h,s1) /\
    lower_value compile_expr cenv ty av s1 = (v,s2) /\
    lower_value compile_expr cenv ty ar s2 = (r,s3) /\
    lower_value compile_expr cenv ty aq s3 = (q,sm) /\
    compile_ecrecover h v r q sm = (res,sb) /\ vv = StackValue ann res
Proof
  `compile_expr cenv ty (Builtin ann ECRecover [ah;av;ar;aq]) sa =
    compile_builtin_dispatch cenv ann ty ECRecover [ah;av;ar;aq] sa` by
    (irule compile_expr_builtin_dispatch >>
     Cases_on `ah` >> simp[names_builtin_def] >>
     Cases_on `av` >> simp[names_builtin_def] >>
     Cases_on `ar` >> simp[names_builtin_def]) >>
  simp[] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def, lower_value_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  Cases_on `compile_ecrecover vh vv' vr vs' st4` >>
  gvs[as_stack_val_def]
QED

Theorem recovery_eval_source_bind:
  eval_expr cx (Builtin ann ECRecover [ah;av;ar;aq]) =
  bind (bind (eval_expr cx ah) (read_result cx))
    (\vh. bind (bind (eval_expr cx av) (read_result cx))
      (\vv. bind (bind (eval_expr cx ar) (read_result cx))
        (\vr. bind (bind (eval_expr cx aq) (read_result cx))
          (\vq. ec_source_tail cx ann ECRecover
            [expr_type ah;expr_type av;expr_type ar;expr_type aq] [vh;vv;vr;vq]))))
Proof
  `eval_expr cx (Builtin ann ECRecover [ah;av;ar;aq]) =
   bind (eval_exprs cx [ah;av;ar;aq])
     (\vs. ec_source_tail cx ann ECRecover
       (MAP expr_type [ah;av;ar;aq]) vs)` by
    (simp[FUN_EQ_THM, Once evaluate_def, bind_def, ignore_bind_def,
          type_check_def, assert_def, return_def, raise_def,
          builtin_args_length_ok_def] >>
     gen_tac >> Cases_on `eval_exprs cx [ah;av;ar;aq] x` >>
     rename1 `eval_exprs cx [ah;av;ar;aq] x = (rr,ee)` >> Cases_on `rr` >>
     simp[bind_def, return_def, get_accounts_def, lift_sum_def,
          builtin_result_def, exprSimECArithTheory.ec_source_tail_def, ignore_bind_def] >>
     Cases_on `evaluate_builtin cx ee.accounts ann ECRecover
       [expr_type ah;expr_type av;expr_type ar;expr_type aq] x'` >>
     Cases_on `precompile_call_success ECRecover ee` >>
     rename1 `precompile_call_success ECRecover ee = (out,ee2)` >>
     Cases_on `out` >>
     gvs[return_def, raise_def, ignore_bind_def, bind_def, AllCaseEqs()] >>
     metis_tac[]) >>
  `eval_exprs cx [] = return []` by
    simp[FUN_EQ_THM, eval_exprs_nil, return_def] >>
  asm_rewrite_tac[eval_exprs_cons_action] >>
  simp[bind_assoc, bind_return]
QED

local
fun recovery_start () = (
  strip_tac >> drule recovery_body_pre_shape >> strip_tac >> gvs[] >>
  `body_exprs_ptr_ok cx [ah;av;ar;aq]` by fs[builtin_args_length_ok_def] >>
  rewrite_tac[bodyPtrDefsTheory.expr_vv_sim_ptr_def] >> rpt strip_tac >>
  drule recovery_compile_operands >> strip_tac >> gvs[] >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `expr_body_pre cenv cx env ah es` by
    (drule exprSimSourceTheory.expr_body_pre_builtin_arg >>
     simp[expr_body_pre_def] >>
     disch_then (qspecl_then [`ah`,`es`] mp_tac) >> simp[]) >>
  `expr_sim_ptr d ctx PG fn cenv cx ty ah es` by
    metis_tac[bodyPtrPrecompileBuiltinsCasesTheory.body_expr_ptr_frame,
              bodyPtrPrecompileBuiltinsCasesTheory.body_exprs_ptr_head] >>
  drule recovery_compiler_append >> strip_tac >>
  `cs_extends sm sb` by
    (simp[cs_extends_def] >> qexists `[]` >>
     gvs[rich_listTheory.IS_PREFIX_APPEND, same_blocks_def]) >>
  qpat_assum `lower_value _ _ _ ah _ = _`
    (mp_then Any mp_tac (cj 2 compile_expr_grows)) >> strip_tac >>
  qpat_assum `lower_value _ _ _ av _ = _`
    (mp_then Any mp_tac (cj 2 compile_expr_grows)) >> strip_tac >>
  qpat_assum `lower_value _ _ _ ar _ = _`
    (mp_then Any mp_tac (cj 2 compile_expr_grows)) >> strip_tac >>
  qpat_assum `lower_value _ _ _ aq _ = _`
    (mp_then Any mp_tac (cj 2 compile_expr_grows)) >> strip_tac >>
  `cs_extends s1 sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 fn /\ fn_has_code s1 sb fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `gas_admissible (bind (eval_expr cx ah) (read_result cx)) expr_res_ok es` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  simp[recovery_eval_source_bind] >>
  irule precompile_operand_bind_ptr >> simp[] >>
  qexistsl [`cenv`,`d`,`env`,`h`,`sa`,`s1`,`ty`] >>
  simp[] >> rpt strip_tac);

fun recovery_hash () = (
  `body_exprs_ptr_ok cx [av;ar;aq]` by
    metis_tac[bodyPtrPrecompileBuiltinsCasesTheory.body_exprs_ptr_tail_force] >>
  `expr_body_pre cenv cx env av ee` by
    (drule exprSimSourceTheory.expr_body_pre_builtin_arg >>
     disch_then (qspecl_then [`av`,`ee`] mp_tac) >> simp[]) >>
  `expr_sim_ptr d ctx PG fn cenv cx ty av ee` by
    metis_tac[bodyPtrPrecompileBuiltinsCasesTheory.body_expr_ptr_frame,
              bodyPtrPrecompileBuiltinsCasesTheory.body_exprs_ptr_head] >>
  `local_ptrs_reserved cenv s1` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `cs_extends s2 sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code s1 s2 fn /\ fn_has_code s2 sb fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `stmt_state_rel ctx fn cenv cx ee t` by
    fs[loweringPostsTheory.expr_post_def] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at s1 x` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at s1 x` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `gas_admissible (bind (eval_expr cx av) (read_result cx)) expr_res_ok ee` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  irule precompile_operand_bind_ptr >> simp[] >>
  qexistsl [`cenv`,`d`,`env`,`v`,`s1`,`s2`,`ty`] >>
  simp[] >> rpt strip_tac);

fun recovery_v () = (
  `body_exprs_ptr_ok cx [ar;aq]` by
    metis_tac[bodyPtrPrecompileBuiltinsCasesTheory.body_exprs_ptr_tail_force] >>
  `expr_body_pre cenv cx env ar ee'` by
    (drule exprSimSourceTheory.expr_body_pre_builtin_arg >>
     disch_then (qspecl_then [`ar`,`ee'`] mp_tac) >> simp[]) >>
  `expr_sim_ptr d ctx PG fn cenv cx ty ar ee'` by
    metis_tac[bodyPtrPrecompileBuiltinsCasesTheory.body_expr_ptr_frame,
              bodyPtrPrecompileBuiltinsCasesTheory.body_exprs_ptr_head] >>
  `local_ptrs_reserved cenv s2` by metis_tac[local_ptrs_reserved_next_var] >>
  `cs_extends s3 sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code s2 s3 fn /\ fn_has_code s3 sb fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `stmt_state_rel ctx fn cenv cx ee' t'` by fs[loweringPostsTheory.expr_post_def] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at s2 x` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at s2 x` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `gas_admissible (bind (eval_expr cx ar) (read_result cx)) expr_res_ok ee'` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  irule precompile_operand_bind_ptr >> simp[] >>
  qexistsl [`cenv`,`d`,`env`,`r`,`s2`,`s3`,`ty`] >>
  simp[] >> rpt strip_tac);

fun recovery_r () = (
  `body_exprs_ptr_ok cx [aq]` by
    metis_tac[bodyPtrPrecompileBuiltinsCasesTheory.body_exprs_ptr_tail_force] >>
  `expr_body_pre cenv cx env aq ee''` by
    (drule exprSimSourceTheory.expr_body_pre_builtin_arg >>
     disch_then (qspecl_then [`aq`,`ee''`] mp_tac) >> simp[]) >>
  `expr_sim_ptr d ctx PG fn cenv cx ty aq ee''` by
    metis_tac[bodyPtrPrecompileBuiltinsCasesTheory.body_expr_ptr_frame,
              bodyPtrPrecompileBuiltinsCasesTheory.body_exprs_ptr_head] >>
  `local_ptrs_reserved cenv s3` by metis_tac[local_ptrs_reserved_next_var] >>
  `fn_has_code s3 sm fn /\ fn_has_code sm sb fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `stmt_state_rel ctx fn cenv cx ee'' t''` by fs[loweringPostsTheory.expr_post_def] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at s3 x` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at s3 x` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `gas_admissible (bind (eval_expr cx aq) (read_result cx)) expr_res_ok ee''` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  irule precompile_operand_bind_ptr >> simp[] >>
  qexistsl [`cenv`,`d`,`env`,`q`,`s3`,`sm`,`ty`] >>
  simp[] >> rpt strip_tac);

fun recovery_frame () = (
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `stmt_state_rel ctx fn cenv cx ee''' t'''` by fs[loweringPostsTheory.expr_post_def] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sm x` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sm x` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `!x. MEM (Var x) [h;v;r;q] ==> not_fresh_at sm x` by
    (simp[] >> metis_tac[exprOperandVarTheory.compile_lower_value_var,
                        stmtFragPtrTheory.not_fresh_at_mono]) >>
  `!i. MEM i (emitted_insts sm sb) ==> MEM i (fn_insts fn)` by
    metis_tac[exprSimHashTheory.hash_emitted_inst_mem] >>
  drule_all bodyPtrPrecompileBuiltinsPlacementTheory.precompile_tail_placement >>
  strip_tac);

fun recovery_safe () = (
  `safe_operand s1 h` by
    (irule exprWordOperandTheory.lower_value_word_safe_operand >>
     goal_assum (drule_at Any) >> simp[is_word_type_def] >>
     metis_tac[exprSimSourceTheory.expr_body_pre_var_types_well_formed,
               expr_body_pre_def]) >>
  `safe_operand s2 v` by
    (irule exprWordOperandTheory.lower_value_word_safe_operand >>
     goal_assum (drule_at Any) >> simp[is_word_type_def] >>
     metis_tac[exprSimSourceTheory.expr_body_pre_var_types_well_formed,
               expr_body_pre_def]) >>
  `safe_operand s3 r` by
    (irule exprWordOperandTheory.lower_value_word_safe_operand >>
     goal_assum (drule_at Any) >> simp[is_word_type_def] >>
     metis_tac[exprSimSourceTheory.expr_body_pre_var_types_well_formed,
               expr_body_pre_def]) >>
  `safe_operand sm q` by
    (irule exprWordOperandTheory.lower_value_word_safe_operand >>
     goal_assum (drule_at Any) >> simp[is_word_type_def] >>
     metis_tac[exprSimSourceTheory.expr_body_pre_var_types_well_formed,
               expr_body_pre_def]) >>
  `EVERY (\op. !l. op <> Label l) [h;v;r;q]` by
    fs[exprSafeOperandTheory.safe_operand_def]);

fun recovery_word () = (
  `wb_frame cenv ee s1 t t'` by metis_tac[exprSimWordArgsTheory.expr_post_frame] >>
  `wb_frame cenv ee' s2 t' t''` by metis_tac[exprSimWordArgsTheory.expr_post_frame] >>
  `wb_frame cenv ee'' s3 t'' t'''` by metis_tac[exprSimWordArgsTheory.expr_post_frame] >>
  `eval_operand h t = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) v')` by
    (qpat_x_assum `expr_post _ _ _ _ ah _ _ _ _ _ _ _ _` mp_tac >>
     simp[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def,
          vyperValueTheory.evaluate_type_def, is_word_type_def]) >>
  `eval_operand h t' = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) v') /\
   op_taint tn' h = {}` by
    (irule (clean_word_operand_frame |> INST_TYPE [``:'a`` |-> ``:num # num``]) >>
     fs[bodyPtrDefsTheory.ptr_val_ok_def, exprSafeOperandTheory.safe_operand_def] >>
     qpat_assum `ghost_kept _ ee s1 _ _ t _ tn'` (irule_at Any) >> simp[]) >>
  `!x. h = Var x ==> not_fresh_at s2 x` by
    (fs[exprSafeOperandTheory.safe_operand_def] >>
     metis_tac[stmtFragPtrTheory.not_fresh_at_mono]) >>
  `eval_operand h t'' = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) v') /\
   op_taint tn'' h = {}` by
    (irule (clean_word_operand_frame |> INST_TYPE [``:'a`` |-> ``:num # num``]) >>
     fs[exprSafeOperandTheory.safe_operand_def] >>
     qpat_assum `ghost_kept _ ee' s2 _ _ t' _ tn''` (irule_at Any) >> simp[]) >>
  `!x. h = Var x ==> not_fresh_at s3 x` by
    metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `eval_operand h t''' = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) v') /\
   op_taint tn''' h = {}` by
    (irule (clean_word_operand_frame |> INST_TYPE [``:'a`` |-> ``:num # num``]) >>
     fs[exprSafeOperandTheory.safe_operand_def] >>
     qpat_assum `ghost_kept _ ee'' s3 _ _ t'' _ tn'''` (irule_at Any) >> simp[]));

fun recovery_other_words () = (
  `eval_operand v t' = SOME (typed_val_to_w256
     (THE (evaluate_type (get_tenv cx) (expr_type av))) v'')` by
    (qpat_x_assum `expr_post _ _ _ _ av _ _ _ _ _ _ _ _` mp_tac >>
     simp[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def,
          vyperValueTheory.evaluate_type_def, is_word_type_def]) >>
  `eval_operand r t'' = SOME (typed_val_to_w256
     (THE (evaluate_type (get_tenv cx) (expr_type ar))) v''')` by
    (qpat_x_assum `expr_post _ _ _ _ ar _ _ _ _ _ _ _ _` mp_tac >>
     simp[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def,
          vyperValueTheory.evaluate_type_def, is_word_type_def]) >>
  `eval_operand q t''' = SOME (typed_val_to_w256
     (THE (evaluate_type (get_tenv cx) (expr_type aq))) v'''')` by
    (qpat_x_assum `expr_post _ _ _ _ aq _ _ _ _ _ _ _ _` mp_tac >>
     simp[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def,
          vyperValueTheory.evaluate_type_def, is_word_type_def]) >>
  `eval_operand v t'' = SOME (typed_val_to_w256
     (THE (evaluate_type (get_tenv cx) (expr_type av))) v'') /\ op_taint tn'' v = {}` by
    (irule (clean_word_operand_frame |> INST_TYPE [``:'a`` |-> ``:num # num``]) >>
     fs[bodyPtrDefsTheory.ptr_val_ok_def, exprSafeOperandTheory.safe_operand_def] >>
     qpat_assum `ghost_kept _ ee' s2 _ _ t' _ tn''` (irule_at Any) >> simp[]) >>
  `!x. v = Var x ==> not_fresh_at s3 x` by
    (fs[exprSafeOperandTheory.safe_operand_def] >>
     metis_tac[stmtFragPtrTheory.not_fresh_at_mono]) >>
  `eval_operand v t''' = SOME (typed_val_to_w256
     (THE (evaluate_type (get_tenv cx) (expr_type av))) v'') /\ op_taint tn''' v = {}` by
    (irule (clean_word_operand_frame |> INST_TYPE [``:'a`` |-> ``:num # num``]) >>
     fs[exprSafeOperandTheory.safe_operand_def] >>
     qpat_assum `ghost_kept _ ee'' s3 _ _ t'' _ tn'''` (irule_at Any) >> simp[]) >>
  `eval_operand r t''' = SOME (typed_val_to_w256
     (THE (evaluate_type (get_tenv cx) (expr_type ar))) v''') /\ op_taint tn''' r = {}` by
    (irule (clean_word_operand_frame |> INST_TYPE [``:'a`` |-> ``:num # num``]) >>
     fs[bodyPtrDefsTheory.ptr_val_ok_def, exprSafeOperandTheory.safe_operand_def] >>
     qpat_assum `ghost_kept _ ee'' s3 _ _ t'' _ tn'''` (irule_at Any) >> simp[]));

fun recovery_typed_tail () = (
  `value_has_type (BaseTV (BytesT (Fixed 32))) v' /\
   value_has_type (THE (evaluate_type (get_tenv cx) (expr_type av))) v'' /\
   value_has_type (THE (evaluate_type (get_tenv cx) (expr_type ar))) v''' /\
   value_has_type (THE (evaluate_type (get_tenv cx) (expr_type aq))) v''''` by
    gvs[vyperTypeExprResultTheory.expr_result_typed_def,
        vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
        vyperTypeExprSoundnessTheory.value_runtime_typed_def,
        vyperTypeInvariantsTheory.value_result_typed_def,
        vyperValueTheory.evaluate_type_def] >>
  `EVERY (\op. op_taint tn''' op = {} /\ (!l. op <> Label l) /\
     (!x. op = Var x ==> not_fresh_at sm x)) [h;v;r;q]` by
    (fs[bodyPtrDefsTheory.ptr_val_ok_def] >> simp[] >> metis_tac[]) >>
  `allocas_from 0 t'''` by simp[ptrDisciplineTheory.allocas_from_def] >>
  `stor_taint_ok cx tn''' t'''` by fs[bodyPtrDefsTheory.ghost_inv_def] >>
  Cases_on `ec_source_tail cx (BaseT AddressT) ECRecover
     [expr_type ah;expr_type av;expr_type ar;expr_type aq]
     [v';v'';v''';v''''] ee'''` >>
  rename1 `ec_source_tail _ _ _ _ _ ee''' = (tail_res,fin)`);

fun recovery_tail_path () = (
  qpat_x_assum `ec_source_tail _ _ _ _ _ ee''' = _` mp_tac >>
  simp[] >> disch_then (fn th => assume_tac th >>
    mp_then Any mp_tac recovery_source_tail_ptr_path th) >>
  disch_then (fn th =>
    qpat_assum `compile_ecrecover _ _ _ _ _ = _`
      (mp_then Any (fn th =>
        qpat_assum `stmt_state_rel _ _ _ _ ee''' t'''`
          (mp_then Any (fn th =>
            qpat_assum `ghost_inv _ _ _ ee''' G''' tn''' t'''`
              (mp_then Any mp_tac th)) th)) th)) >>
  simp[vyperValueTheory.evaluate_type_def] >>
  disch_then (qspecl_then [`[ah;av;ar;aq]`,`PG`,`cx_dead cx`] mp_tac) >>
  (impl_tac >- gs[vyperValueTheory.evaluate_type_def,
                    bodyPtrDefsTheory.stor_taint_ok_def]) >> strip_tac);

fun recovery_tail_outcome () = (
  `ee''' with gas_obs := [] = ee'''` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `fin with gas_obs := [] = fin` by
    (drule ec_source_tail_gas_obs >> disch_then (qspec_then `[]` mp_tac) >>
     simp[] >> gvs[]) >>
  irule ec_source_tail_pointer_outcome >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[] >>
  simp[vyperASTTheory.expr_type_def, as_ptr_val_def]);

fun recovery_entry_rebase () = (
  `wb_frame cenv es sa s0 t` by metis_tac[expr_post_frame] >>
  `wb_frame cenv ee'' s3 t'' t'''` by metis_tac[expr_post_frame] >>
  `sa.cs_next_var <= s2.cs_next_var /\ sa.cs_next_id <= s2.cs_next_id /\
   sa.cs_next_var <= s3.cs_next_var /\ sa.cs_next_id <= s3.cs_next_id /\
   sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by decide_tac >>
  `MAP FDOM es.scopes = MAP FDOM ee'.scopes /\
   MAP FDOM es.scopes = MAP FDOM ee''.scopes /\
   MAP FDOM es.scopes = MAP FDOM ee'''.scopes` by metis_tac[] >>
  `wb_frame cenv es sa s0 t'` by
    (irule wb_frame_trans >>
     qpat_assum `wb_frame _ ee s1 t t'` (irule_at Any) >> simp[] >> metis_tac[]) >>
  `wb_frame cenv es sa s0 t''` by
    (irule wb_frame_trans >>
     qpat_assum `wb_frame _ ee' s2 t' t''` (irule_at Any) >> simp[] >> metis_tac[]) >>
  `wb_frame cenv es sa s0 t'''` by
    (irule wb_frame_trans >>
     qpat_assum `wb_frame _ ee'' s3 t'' t'''` (irule_at Any) >> simp[] >> metis_tac[]));

fun recovery_ghost_rebase () = (
  `ghost_kept cenv es sa G0 tn0 s0 G' tn'` by
    (irule wordArgsPtrTheory.ghost_kept_wb_trans >>
     qpat_assum `ghost_kept _ ee s1 _ _ _ G' tn'` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  `ghost_kept cenv es sa G0 tn0 s0 G'' tn''` by
    (irule wordArgsPtrTheory.ghost_kept_wb_trans >>
     qpat_assum `ghost_kept _ ee' s2 _ _ _ G'' tn''` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  `ghost_kept cenv es sa G0 tn0 s0 G''' tn'''` by
    (irule wordArgsPtrTheory.ghost_kept_wb_trans >>
     qpat_assum `ghost_kept _ ee'' s3 _ _ _ G''' tn'''` (irule_at Any) >>
     simp[] >> metis_tac[]));

fun recovery_final_rebase () = (
  reverse conj_tac >-
    (irule wordArgsPtrTheory.ghost_kept_wb_trans >>
     qpat_assum `ghost_kept _ ee''' sm _ _ _ _ _` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  irule exprSimCalldataSliceTheory.vv_post_prefix_frame >>
  qpat_assum `vv_post _ _ _ _ _ ee''' sm _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> metis_tac[]);
in

Theorem recovery_expr_vv_sim_ptr:
  (builtin_args_length_ok ECRecover (LENGTH args) ==> body_exprs_ptr_ok cx args) /\
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann ECRecover args) es ==>
  expr_vv_sim_ptr d ctx PG fn cenv cx ty (Builtin ann ECRecover args) es
Proof
  recovery_start () >> recovery_hash () >> recovery_v () >> recovery_r () >>
  recovery_frame () >> recovery_safe () >> recovery_word () >>
  recovery_other_words () >> recovery_typed_tail () >> recovery_tail_path () >>
  recovery_tail_outcome () >> recovery_entry_rebase () >>
  recovery_ghost_rebase () >> recovery_final_rebase ()
QED

end
