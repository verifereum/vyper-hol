(* Lift physical internal-call conversion continuations to memory simulations. *)
Theory bodyMemTbConvertCallLift
Ancestors
  bodyMemTbConvertCallSummary bodyMemTbConvertDestLift
  exprSimHyps exprSimHypsDefs exprSimUnwrap exprSimDefs exprSimMemDefs
  vyperTypeExprSoundness vyperState vyperInterpreter exprSimSource vyperTypeSystem vyperTypeInvariants
  bodyMemTbConvertDynamicLift exprSimConvertFromBytes exprLoweringProps
  exprSimConvert exprLowering exprOperandVar loweringSlice freshWrites compileEnv
  rich_list fragExec stmtSimForced gasSummary gasOutcome gasSummaryCompose
  fragGasMode fragGasPath valueCopyBytes loweringPosts exprSimConvertBytes

Theorem convert_call_vv_layout[local]:
  expr_body_pre cenv cx env (Call ann (IntCall fid) args drv) es /\
  eval_expr cx (Call ann (IntCall fid) args drv) (es with gas_obs := gs) = (INL tv,ee) /\
  vv_post ctx func cenv cx (Call ann (IntCall fid) args drv) es sa sm s0 ee tv vv s ==>
  ?ltv.
    evaluate_type (get_tenv cx)
      (lowered_value_type cenv (Call ann (IntCall fid) args drv)) = SOME ltv /\
    type_memory_bytes cenv (lowered_value_type cenv (Call ann (IntCall fid) args drv)) =
      type_memory_size ltv
Proof
  strip_tac >>
  Cases_on `read_result cx tv ee` >> rename1 `read_result cx tv ee = (rr,ef)` >>
  `ef = ee` by metis_tac[read_result_state] >> gvs[] >>
  Cases_on `rr`
  >- (rename1 `read_result cx tv ee = (INL v,ee)` >>
      `expr_body_pre cenv cx env (Call ann (IntCall fid) args drv)
        (es with gas_obs := gs)` by metis_tac[expr_body_pre_gas_obs] >>
      `bind (eval_expr cx (Call ann (IntCall fid) args drv)) (read_result cx)
        (es with gas_obs := gs) = (INL v,ee)` by simp[bind_def] >>
      drule_all bodyMemTbConvertCallSourceTheory.convert_call_read_lowered_typed >>
      simp[value_runtime_typed_def] >> strip_tac >>
      `env.type_defs = get_tenv cx` by
        gvs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
            env_context_consistent_def] >>
      metis_tac[expr_sim_inv_memory_size, expr_body_pre_def]) >>
  metis_tac[vv_post_failed_read]
QED

Theorem call_dynamic_convert_sim_mem[local]:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert dst [e]) es /\
  e = Call a (IntCall fid) args drv /\
  is_bytestring_type (expr_type e) /\ ~is_bytestring_type dst /\
  expr_vv_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_sim_mem ctx func cenv cx ty (TypeBuiltin ann Convert dst [e]) es
Proof
  strip_tac >> drule dynamic_convert_typing_boundary >> strip_tac >>
  drule_all dynamic_scalar_type >> strip_tac >>
  drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  simp[expr_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  drule_all dynamic_convert_mem_layout >> strip_tac >>
  irule expr_sim_mem_word_outcome >>
  conj_tac >- simp[vyperASTTheory.expr_type_def] >>
  Cases_on `compile_expr cenv (expr_type (Call a (IntCall fid) args drv))
    (Call a (IntCall fid) args drv) sa` >>
  rename1 `compile_expr _ _ _ sa = (vv,sm)` >>
  `unwrap_value cenv vv sm = (x,s1)` by
    (qpat_x_assum `lower_value _ _ _ (Call _ _ _ _) _ = _` mp_tac >>
     simp[lower_value_def, comp_bind_def]) >>
  drule (cj 1 compile_expr_grows) >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >>
  `fn_has_code sa sm func /\ fn_has_code sm s1 func` by
    (irule fn_has_code_split >> simp[]) >>
  `gas_admissible (eval_expr cx (Call a (IntCall fid) args drv)) expr_vv_res_ok es` by
    metis_tac[expr_body_pre_vv_gas_admissible] >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_vv_sim_mem_def] >>
  disch_then (qspecl_then [`sa`, `sm`, `vv`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rewrite_tac[bodyMemTbConvertComposeTheory.eval_expr_convert_action, bind_assoc] >>
  irule forced_vv_then_outcome >>
  conj_tac >- (rpt strip_tac >> BETA_TAC >>
    metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  qexists_tac `\tv ee u.
    vv_post ctx func cenv cx (Call a (IntCall fid) args drv) es sa sm s0 ee tv vv u /\
    vv_store_bound cx (expr_type (Call a (IntCall fid) args drv))
      (lowered_value_type cenv (Call a (IntCall fid) args drv)) ee tv vv u /\
    u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next` >>
  reverse conj_tac >- simp[] >>
  rpt gen_tac >> BETA_TAC >> strip_tac >> suspend "continuation"
QED

Resume call_dynamic_convert_sim_mem[continuation]:
  drule_all convert_call_vv_layout >> strip_tac >>
  drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
    call_dynamic_vv_convert_summary >>
  disch_then (drule_at (Pat `well_formed_type _ _`)) >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
  disch_then (qspecl_then [`sb`, `op`, `gs`] mp_tac) >>
  simp[gas_summary_at_def, gas_marked_exec_def] >> metis_tac[]
QED

Finalise call_dynamic_convert_sim_mem

Theorem call_dynamic_convert_mem:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert dst [e]) es /\
  e = Call a (IntCall fid) args drv /\
  is_bytestring_type (expr_type e) /\ ~is_bytestring_type dst /\
  expr_vv_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_sim_mem ctx func cenv cx ty (TypeBuiltin ann Convert dst [e]) es /\
  expr_vv_sim_mem ctx func cenv cx ty (TypeBuiltin ann Convert dst [e]) es
Proof
  strip_tac >>
  `expr_sim_mem ctx func cenv cx ty (TypeBuiltin ann Convert dst [e]) es` by
    metis_tac[call_dynamic_convert_sim_mem] >> simp[] >>
  drule dynamic_convert_typing_boundary >> strip_tac >>
  drule_all dynamic_scalar_type >> strip_tac >>
  irule exprSimMemoryStackTheory.body_expr_vv_sim_mem_stack_word >>
  simp[vyperASTTheory.expr_type_def] >>
  metis_tac[compile_convert_stack, eval_expr_type_builtin_value, pairTheory.PAIR_EQ]
QED

Theorem call_bytestring_convert_outcome[local]:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert ann [e]) es /\
  e = Call a (IntCall fid) args drv /\ is_bytestring_type ann /\
  expr_vv_sim_mem ctx func cenv cx (expr_type e) e es /\
  lower_value compile_expr cenv ty (TypeBuiltin ann Convert ann [e]) sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  gas_admissible (bind (eval_expr cx (TypeBuiltin ann Convert ann [e])) (read_result cx))
    expr_res_ok es /\ stmt_state_rel ctx func cenv cx es s0 /\
  alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (eval_expr cx (TypeBuiltin ann Convert ann [e])) (read_result cx)) (es,s0)
    (\res fin ss. ?v. res = INL v /\
      expr_post ctx func cenv cx (TypeBuiltin ann Convert ann [e]) es sa sb s0
        fin v op ss /\ ss.vs_current_bb = sb.cs_current_bb /\
      ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func ss /\ s0.vs_alloca_next <= ss.vs_alloca_next /\
      (?w. eval_operand op ss = SOME w /\
        w2n w + type_memory_bytes cenv ann <= ss.vs_alloca_next))
    (\res fin out. expr_exit res out)
Proof
  strip_tac >> drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  `is_bytestring_type (expr_type (Call a (IntCall fid) args drv))` by
    metis_tac[valid_conversion_to_bytestring] >>
  `is_bytestring_type (lowered_value_type cenv (Call a (IntCall fid) args drv))` by
    metis_tac[bodyMemTbConvertCallSourceTheory.convert_call_lowered_bytestring,
              vyperASTTheory.expr_type_def] >>
  drule_all bytestring_convert_mem_layout >> strip_tac >>
  Cases_on `compile_expr cenv (expr_type (Call a (IntCall fid) args drv))
    (Call a (IntCall fid) args drv) sa` >>
  rename1 `compile_expr _ _ _ sa = (vv,sm)` >>
  `unwrap_value cenv vv sm = (x,s1)` by
    (qpat_x_assum `lower_value _ _ _ (Call _ _ _ _) _ = _` mp_tac >>
     simp[lower_value_def, comp_bind_def]) >>
  drule (cj 1 compile_expr_grows) >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >>
  `fn_has_code sa sm func /\ fn_has_code sm s1 func` by
    (irule fn_has_code_split >> simp[]) >>
  `gas_admissible (eval_expr cx (Call a (IntCall fid) args drv)) expr_vv_res_ok es` by
    metis_tac[expr_body_pre_vv_gas_admissible] >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_vv_sim_mem_def] >>
  disch_then (qspecl_then [`sa`, `sm`, `vv`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rewrite_tac[bodyMemTbConvertComposeTheory.eval_expr_convert_action, bind_assoc] >>
  irule forced_vv_then_outcome >>
  conj_tac >- (rpt strip_tac >> BETA_TAC >>
    metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  qexists_tac `\tv ee u.
    vv_post ctx func cenv cx (Call a (IntCall fid) args drv) es sa sm s0 ee tv vv u /\
    vv_store_bound cx (expr_type (Call a (IntCall fid) args drv))
      (lowered_value_type cenv (Call a (IntCall fid) args drv)) ee tv vv u /\
    u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next` >>
  reverse conj_tac >- simp[] >>
  rpt gen_tac >> BETA_TAC >> strip_tac >> suspend "continuation"
QED

Resume call_bytestring_convert_outcome[continuation]:
  drule_all convert_call_vv_layout >> strip_tac >>
  `type_memory_bytes cenv ann < dimword (:256)` by
    (`~is_word_type ann` by gvs[bytestring_type_cases, is_word_type_def] >>
     `alloc_limits_expr cenv (TypeBuiltin ann Convert ann [Call a (IntCall fid) args drv])` by
       gvs[expr_body_pre_def] >>
     gvs[allocLimitsTheory.alloc_limits_expr_def,
         allocLimitsTheory.type_alloc_ok_def, vyperASTTheory.expr_type_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  `!v. read_result cx tv ee = (INL v,ee) ==>
       expr_res_ok (convert_result cx (expr_type (Call a (IntCall fid) args drv)) ann v)` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `gas_admissible (bind (eval_expr cx (TypeBuiltin _ _ _ _)) _) _ es`
       (mp_tac o REWRITE_RULE [gasContextTheory.gas_admissible_def]) >>
     disch_then (qspec_then `gs` mp_tac) >>
     rewrite_tac[bodyMemTbConvertComposeTheory.eval_expr_convert_action] >>
     simp[bind_def] >> disch_then irule >> simp[]) >>
  drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
    call_bytestring_vv_convert_summary >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ (TypeBuiltin _ _ _ _) _`)) >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
  disch_then (qspecl_then [`sb`, `op`, `gs`] mp_tac) >>
  simp[gas_summary_at_def, gas_marked_exec_def] >> metis_tac[]
QED

Finalise call_bytestring_convert_outcome

Theorem call_bytestring_convert_sim_mem[local]:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert dst [e]) es /\
  e = Call a (IntCall fid) args drv /\ is_bytestring_type dst /\
  expr_vv_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_sim_mem ctx func cenv cx ty (TypeBuiltin ann Convert dst [e]) es
Proof
  strip_tac >> drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  rw[expr_sim_mem_def] >>
  drule_at (Pat `lower_value _ _ _ _ _ = _`) call_bytestring_convert_outcome >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ (TypeBuiltin _ _ _ _) _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  simp[] >> strip_tac >>
  irule gas_outcome_post_mono >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >> simp[vyperASTTheory.expr_type_def] >>
  metis_tac[bytestring_convert_capacity_posts]
QED

Theorem call_bytestring_convert_vv_sim_mem[local]:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert dst [e]) es /\
  e = Call a (IntCall fid) args drv /\ is_bytestring_type dst /\
  expr_vv_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_vv_sim_mem ctx func cenv cx ty (TypeBuiltin ann Convert dst [e]) es
Proof
  strip_tac >> drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  rw[expr_vv_sim_mem_def] >>
  `?t op. vv = StackValue t op` by metis_tac[compile_convert_stack, pairTheory.PAIR_EQ] >> gvs[] >>
  `lower_value compile_expr cenv ty (TypeBuiltin ann Convert ann [Call a (IntCall fid) args drv]) sa = (op,sb)` by
    simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
  `gas_admissible (bind (eval_expr cx (TypeBuiltin ann Convert ann [Call a (IntCall fid) args drv])) (read_result cx))
      expr_res_ok es` by
    (irule exprSimStackTheory.eval_expr_force_admissible >>
     simp[] >> metis_tac[eval_expr_type_builtin_value]) >>
  simp[vyperASTTheory.expr_type_def, lowered_value_type_def] >>
  irule bytestring_convert_stack_outcome >>
  conj_tac >- metis_tac[] >>
  irule call_bytestring_convert_outcome >> simp[] >> metis_tac[]
QED

Theorem call_bytestring_convert_mem:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert dst [e]) es /\
  e = Call a (IntCall fid) args drv /\ is_bytestring_type dst /\
  expr_vv_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_sim_mem ctx func cenv cx ty (TypeBuiltin ann Convert dst [e]) es /\
  expr_vv_sim_mem ctx func cenv cx ty (TypeBuiltin ann Convert dst [e]) es
Proof
  metis_tac[call_bytestring_convert_sim_mem, call_bytestring_convert_vv_sim_mem]
QED
