(* Memory simulation composition for EC arithmetic. *)
Theory bodyMemEcArithSimulation
Ancestors
  bodyMemEcArithCompose bodyMemEcArithPaths exprSimCalldataSlice
  bodyExprForceMemory gasOutcome gasSummary exprSimECArith
  exprSimMemDefs fragExec compileEnv exprSimDefs exprLoweringProps
  bodyMemTbEmptyMemory exprSimWordArgs exprSimProps loweringPosts

Theorem ec_tail_mem_outcome[local]:
  (bt = ECAdd \/ bt = ECMul) /\
  ec_source_tail cx ann bt tys vs es = (res,ee) /\
  gas_marked_path T ctx func s n r /\
  ((?t. r = OK t /\ Q res (ee with gas_obs := []) t) \/
   (exit_result r /\ R res (ee with gas_obs := []) r)) ==>
  gas_outcome T tops (ctx,func) (ec_source_tail cx ann bt tys vs) (es,s) Q R
Proof
  strip_tac >> rewrite_tac[gas_outcome_def] >>
  qexists_tac `REPLICATE n F` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`res`,`ee`,`r`] >> simp[] >>
  irule gas_marked_exec_no_source_read >> simp[] >>
  metis_tac[ec_source_tail_gas_obs]
QED

Theorem ec_two_operand_post[local]:
  lower_value compile_expr cenv (expr_type a) a sa = (p,s1) /\
  lower_value compile_expr cenv (expr_type b) b s1 = (q,sm) /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  expr_post ctx func cenv cx a es sa s1 s0 es1 v1 p t /\
  expr_post ctx func cenv cx b es1 s1 sm t es2 v2 q u /\
  MAP FDOM es.scopes = MAP FDOM es2.scopes /\
  MAP FDOM es1.scopes = MAP FDOM es2.scopes /\
  vv_post ctx func cenv cx e es2 sm sb u ee tv vv t' ==>
  vv_post ctx func cenv cx e es sa sb s0 ee tv vv t'
Proof
  strip_tac >>
  `sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
   s1.cs_next_var <= sm.cs_next_var /\ s1.cs_next_id <= sm.cs_next_id` by
    metis_tac[cj 2 compile_expr_grows] >>
  `wb_frame cenv es sa s0 u` by
    (irule wb_frame_trans >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[expr_post_frame]) >>
  irule vv_post_prefix_frame >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem ec_pointer_tail_mem_outcome[local]:
  (bt = ECAdd \/ bt = ECMul) /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  ec_source_tail cx ann bt tys vs es2 = (INL tv,ee) /\
  gas_marked_path T ctx func u n (OK t') /\
  vv_post ctx func cenv cx e es sa sb s0 ee tv
    (FST (as_ptr_val (expr_type e) LocMemory (res,sb))) t' /\
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv
    (FST (as_ptr_val (expr_type e) LocMemory (res,sb))) t' /\
  t'.vs_current_bb = sb.cs_current_bb /\
  t'.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t' /\ s0.vs_alloca_next <= u.vs_alloca_next /\
  u.vs_alloca_next <= t'.vs_alloca_next ==>
  gas_outcome T tops (ctx,func) (ec_source_tail cx ann bt tys vs) (es2,u)
    (\r ee t. ?tv. r = INL tv /\
      vv_post ctx func cenv cx e es sa sb s0 ee tv
        (FST (as_ptr_val (expr_type e) LocMemory (res,sb))) t /\
      vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv
        (FST (as_ptr_val (expr_type e) LocMemory (res,sb))) t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
    (\r ee rr. expr_exit r rr)
Proof
  strip_tac >>
  `?rv. tv = Value rv` by
    (qpat_x_assum `ec_source_tail _ _ _ _ _ _ = _` mp_tac >>
     simp[ec_source_tail_cases, AllCaseEqs()] >> metis_tac[]) >> gvs[] >>
  irule ec_tail_mem_outcome >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  simp[value_store_bound_gas_obs] >>
  simp[exprLoweringTheory.as_ptr_val_def] >>
  irule memory_value_post_gas_obs >> simp[contextTheory.mk_ptr_def] >>
  gvs[exprLoweringTheory.as_ptr_val_def] >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_post_def, contextTheory.mk_ptr_def] >> strip_tac >>
  first_assum ACCEPT_TAC
QED

Theorem ecmul_vv_sim_mem:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann ECMul [a;b]) es /\
  body_exprs_mem_ok cx [a;b] ==>
  expr_vv_sim_mem ctx func cenv cx ty (Builtin ann ECMul [a;b]) es
Proof
  strip_tac >> drule (cj 2 ec_pre_types) >> strip_tac >> gvs[] >>
  rewrite_tac[expr_vv_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  drule (cj 1 compile_ec_operands) >> strip_tac >>
  `cs_extends sm sb` by
    (drule (cj 2 ec_points_code_shape) >>
     simp[same_blocks_def, cs_extends_def, rich_listTheory.IS_PREFIX_APPEND] >>
     metis_tac[listTheory.APPEND]) >>
  simp[ec_eval_bind] >>
  ho_match_mp_tac (Q.INST [`ann` |-> `ArrayT (BaseT (UintT 256)) (Fixed 2)`,
    `bt` |-> `ECMul`, `q` |-> `scalar`] ec_mem_operands_then) >> simp[] >>
  conj_tac >- metis_tac[exprSimHashTheory.expr_exit_INR_cast] >>
  rpt gen_tac >> strip_tac >>
  `value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v1 /\
   value_has_type (BaseTV (UintT 256)) v2` by
    gvs[vyperTypeExprResultTheory.expr_result_typed_def,
        vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
        vyperTypeInvariantsTheory.value_result_typed_def,
        vyperValueTheory.evaluate_type_def] >>
  `expr_val_rel cx (BaseT (UintT 256)) v2 scalar u` by
    metis_tac[loweringPostsTheory.expr_post_def] >>
  `?sw. eval_operand scalar u = SOME sw` by
    metis_tac[cj 1 ec_memory_semantics] >>
  `w2n w + 64 < dimword (:256)` by
    metis_tac[ec_point_pointer_bound] >>
  `!i. MEM i (emitted_insts sm sb) ==> MEM i (fn_insts func)` by
    metis_tac[exprSimHashTheory.hash_emitted_inst_mem] >>
  Cases_on `ec_source_tail cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECMul
    [ArrayT (BaseT (UintT 256)) (Fixed 2);BaseT (UintT 256)] [v1;v2] es2` >>
  rename1 `ec_source_tail _ _ _ _ _ _ = (rr,ee)` >>
  drule_at (Pat `compile_ecmul_point _ _ _ = _`)
    (Q.INST [`e` |-> `Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECMul [a;b]`]
      ecmul_points_path_mem) >>
  simp[exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def] >>
  disch_then drule_all >>
  disch_then (qspecl_then [`b`,`a`] strip_assume_tac)
  >- suspend "success"
  >> (irule ec_tail_mem_outcome >> simp[] >> metis_tac[])
QED

Resume ecmul_vv_sim_mem[success]:
  `vv_post ctx func cenv cx
     (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECMul [a;b])
     es sa sb s0 ee a'
     (FST (as_ptr_val (ArrayT (BaseT (UintT 256)) (Fixed 2)) LocMemory (res,sb))) t'` by
    (irule ec_two_operand_post >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  irule (SRULE[vyperASTTheory.expr_type_def, exprLoweringTheory.lowered_value_type_def]
    (Q.INST [`e` |-> `Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECMul [a;b]`]
      ec_pointer_tail_mem_outcome)) >> simp[] >> metis_tac[]
QED
Finalise ecmul_vv_sim_mem


Theorem ecadd_vv_sim_mem:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann ECAdd [a;b]) es /\
  body_exprs_mem_ok cx [a;b] ==>
  expr_vv_sim_mem ctx func cenv cx ty (Builtin ann ECAdd [a;b]) es
Proof
  strip_tac >> drule (cj 1 ec_pre_types) >> strip_tac >> gvs[] >>
  rewrite_tac[expr_vv_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  drule (cj 2 compile_ec_operands) >> strip_tac >>
  `cs_extends sm sb` by
    (drule (cj 1 ec_points_code_shape) >>
     simp[same_blocks_def, cs_extends_def, rich_listTheory.IS_PREFIX_APPEND] >>
     metis_tac[listTheory.APPEND]) >>
  simp[ec_eval_bind] >>
  ho_match_mp_tac (Q.INST [`ann` |-> `ArrayT (BaseT (UintT 256)) (Fixed 2)`,
    `bt` |-> `ECAdd`] ec_mem_operands_then) >> simp[] >>
  conj_tac >- metis_tac[exprSimHashTheory.expr_exit_INR_cast] >>
  rpt gen_tac >> strip_tac >> suspend "typed"
QED

Resume ecadd_vv_sim_mem[typed]:
  `value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v1 /\
   value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v2` by
    gvs[vyperTypeExprResultTheory.expr_result_typed_def,
        vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
        vyperTypeInvariantsTheory.value_result_typed_def,
        vyperValueTheory.evaluate_type_def] >>
  `expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v2 q u /\
   expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) s1 sm es2 v2 q u` by
    metis_tac[loweringPostsTheory.expr_post_def] >>
  `sa.cs_next_id <= s1.cs_next_id` by metis_tac[cj 2 compile_expr_grows] >>
  `expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) sa sm es2 v2 q u` by
    metis_tac[exprSimPropsTheory.expr_val_at_start_mono] >>
  `?w2. eval_operand q u = SOME w2` by
    (qpat_assum `expr_val_rel _ _ v1 p u`
      (mp_then (Pat `expr_val_rel _ _ _ _ _`) mp_tac (cj 2 ec_memory_semantics)) >>
     simp[] >> disch_then drule_all >> metis_tac[]) >>
  `w2n w2 + 64 <= u.vs_alloca_next` by
    (irule bodyMemEcArithOperandsTheory.ec_point_read_capacity >>
     qexistsl_tac [`cx`,`q`,`u`,`v2`] >> simp[]) >>
  `w2n w + 64 < dimword (:256) /\ w2n w2 + 64 < dimword (:256)` by
    metis_tac[ec_point_pointer_bound] >>
  `!i. MEM i (emitted_insts sm sb) ==> MEM i (fn_insts func)` by
    metis_tac[exprSimHashTheory.hash_emitted_inst_mem] >>
  Cases_on `ec_source_tail cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECAdd
    [ArrayT (BaseT (UintT 256)) (Fixed 2);ArrayT (BaseT (UintT 256)) (Fixed 2)]
    [v1;v2] es2` >>
  rename1 `ec_source_tail _ _ _ _ _ _ = (rr,ee)` >>
  drule_at (Pat `compile_ecadd_points _ _ _ = _`)
    (Q.INST [`e` |-> `Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECAdd [a;b]`]
      ecadd_points_path_mem) >>
  simp[exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def] >>
  disch_then drule_all >>
  disch_then (qspecl_then [`b`,`a`] strip_assume_tac)
  >- suspend "success"
  >> (irule ec_tail_mem_outcome >> simp[] >> metis_tac[])
QED

Resume ecadd_vv_sim_mem[success]:
  `vv_post ctx func cenv cx
     (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECAdd [a;b])
     es sa sb s0 ee a'
     (FST (as_ptr_val (ArrayT (BaseT (UintT 256)) (Fixed 2)) LocMemory (res,sb))) t'` by
    (irule ec_two_operand_post >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  irule (SRULE[vyperASTTheory.expr_type_def, exprLoweringTheory.lowered_value_type_def]
    (Q.INST [`e` |-> `Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECAdd [a;b]`]
      ec_pointer_tail_mem_outcome)) >> simp[] >> metis_tac[]
QED
Finalise ecadd_vv_sim_mem


Theorem ec_arith_sim_mem:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann bt [a;b]) es /\
  body_exprs_mem_ok cx [a;b] /\ (bt = ECAdd \/ bt = ECMul) ==>
  expr_sim_mem ctx func cenv cx ty (Builtin ann bt [a;b]) es /\
  expr_vv_sim_mem ctx func cenv cx ty (Builtin ann bt [a;b]) es
Proof
  strip_tac >>
  `expr_vv_sim_mem ctx func cenv cx ty (Builtin ann bt [a;b]) es` by
    metis_tac[ecadd_vv_sim_mem, ecmul_vv_sim_mem] >> simp[] >>
  gvs[] >>
  (irule body_expr_sim_mem_of_vv_sim_mem >> simp[] >> conj_tac
   >- (rpt strip_tac >> imp_res_tac compile_ec_operands >>
       gvs[exprLoweringTheory.as_ptr_val_def]) >>
   qexists_tac `env` >> simp[])
QED
