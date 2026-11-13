(* Reachability and counted sequencing for widened internal returns. *)
Theory internalReturnCompositionMem
Ancestors
  bodyMemoryDefs internalReturnValueEndpointMem stmtSimReturnWiden
  incompatibleReturnLayout stmtReasonVvMemory runFromGasPathMem
  typedMemoryCopy vyperTypeSystem vyperTypeInvariants exprSimHypsDefs compileEnv
  stmtLowering exprLoweringProps fragExecMem gasSummary gasOutcome
  venomExecSemantics venomState stmtSimDefs fragGasMode vyperInterpreter vyperState
  loweringPosts stmtSimReturn stmtSimProps fragExec externalEntryShape

Theorem internal_return_widened_reachable:
  expr_sim_inv ce cx env es /\
  IS_SOME (type_stmt env ty (Return eo)) /\
  ce.ce_returns_count = returns_stack_count sft ty /\
  (IS_SOME rb <=> ce.ce_returns_count = 0 /\ ty <> NoneT) /\
  ~(!e. eo = SOME e ==> lowered_value_type ce e = expr_type e /\
       (expr_type e = ty \/ is_word_type ty \/ is_bytestring_type ty)) ==>
  ?e bw cap. eo = SOME e /\ rb = SOME (bw,cap) /\
    ce.ce_returns_count = 0 /\ ~is_word_type ty /\
    well_typed_expr env e /\ type_widens_to (get_tenv cx) (expr_type e) ty
Proof
  strip_tac >> Cases_on `eo` >- gvs[] >> rename1 `SOME e` >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `well_typed_expr env e /\ type_widens_to (get_tenv cx) (expr_type e) ty /\
   ty <> NoneT` by
    (qpat_x_assum `IS_SOME (type_stmt _ _ _)` mp_tac >>
     simp[type_stmt_def, AllCaseEqs()]) >>
  `~is_word_type ty` by
    (strip_tac >> `expr_type e = ty` by metis_tac[typed_copy_word_widening] >>
     `~is_bytestring_type (expr_type e)` by
       metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
     Cases_on `lowered_value_type ce e = expr_type e` >- gvs[] >>
     `~(lowered_value_type ce e = expr_type e \/
        is_bytestring_type (expr_type e) /\
        is_bytestring_type (lowered_value_type ce e) /\
        arg_type_fits (lowered_value_type ce e) (expr_type e))` by simp[] >>
     drule_all incompatible_return_layout_intcall >> strip_tac >>
     gvs[vyperASTTheory.expr_type_def]) >>
  `ce.ce_returns_count = 0` by
    (spose_not_then assume_tac >>
     `expr_type e = ty` by metis_tac[stack_return_widens_eq, arithmeticTheory.NOT_ZERO_LT_ZERO] >>
     `~is_bytestring_type (expr_type e)` by
       (strip_tac >> Cases_on `ty` >>
        gvs[is_bytestring_type_def, returns_stack_count_def]) >>
     Cases_on `lowered_value_type ce e = expr_type e` >- gvs[] >>
     `~(lowered_value_type ce e = expr_type e \/
        is_bytestring_type (expr_type e) /\
        is_bytestring_type (lowered_value_type ce e) /\
        arg_type_fits (lowered_value_type ce e) (expr_type e))` by simp[] >>
     drule_all incompatible_return_layout_intcall >> strip_tac >>
     `ann = ty` by gvs[vyperASTTheory.expr_type_def] >>
     `lowered_value_type ce e = ty` by
       metis_tac[stack_return_widens_eq, arithmeticTheory.NOT_ZERO_LT_ZERO] >> gvs[]) >>
  Cases_on `rb` >> gvs[] >> PairCases_on `x` >> simp[]
QED

Theorem internal_return_suffix_outcome_mem[local]:
  frag_exec_mem ctx sm sb (\s. s = t) (\s. F) (RetQ v (ee with scopes := [])) /\
  (!v es gs r. RetQ v (es with gas_obs := gs) r = RetQ v es r) /\
  fn_has_code sm sb func /\ ~t.vs_halted /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  gas_outcome T tops (ctx,func) (raise (ReturnException v)) (ee,t)
    Q (\res est r. !tail. stmt_exit RetQ (est with gas_obs := tail) res r)
Proof
  strip_tac >>
  `?fuel r. run_from fuel ctx func t = r /\ exit_result r /\
    RetQ v (ee with scopes := []) r /\ mem_safe_run fuel ctx func t` by
    (qpat_x_assum `frag_exec_mem _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [frag_exec_mem_def]) >>
     disch_then (qspecl_then [`func`, `t`] mp_tac) >> simp[]) >>
  drule_all run_from_gas_path_mem >> strip_tac >>
  simp[gas_outcome_def] >> qexists_tac `REPLICATE n F` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR (ReturnException v)`, `ee`, `r`] >>
  simp[gas_marked_exec_def, raise_def, gas_marked_path_def,
       stmt_exit_def] >> disj2_tac >> gen_tac >> disj2_tac >>
  qpat_x_assum `!v es gs r. _` (qspecl_then [`v`, `ee with scopes := []`, `tail`, `r`] mp_tac) >>
  simp[]
QED

Theorem internal_return_memory_compose_mem:
  ce.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\ ce.ce_returns_count = 0 /\
  expr_sim_mem ctx func ce cx ty e es /\
  (!v es gs r. RetQ v (es with gas_obs := gs) r = RetQ v es r) /\
  (!sa op sm sb bp bsz s0 ee v t gs.
    lower_value compile_expr ce ty e sa = (op,sm) /\
    ce.ce_return_buf = SOME (PtrVar (Var bp) bsz) /\
    compile_internal_return_from_env ce ty (lowered_value_type ce e)
      op (Var rpc) sm = ((),sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved ce sa /\ ret_pc_ok ce sa s0 /\
    return_buf_frame (SOME (bw,cap)) ce sa s0 /\
    ret_buf_frontier (SOME (bw,cap)) ce t /\
    stmt_state_rel ctx func ce cx es s0 /\
    bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
    expr_post ctx func ce cx e es sa sm s0 ee v op t /\
    expr_store_bound cx (expr_type e) v op t /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    (!sty stv. post_value_type ce e = sty /\
      evaluate_type (get_tenv cx) sty = SOME stv /\
      value_has_type stv v /\ ~is_bytestring_type sty ==>
      expr_store_bound cx sty v op t /\
      (~is_word_type sty ==> ?sw. eval_operand op t = SOME sw /\
        (type_memory_size stv = 0 \/
         w2n sw + type_memory_size stv <= t.vs_alloca_next) /\
        w2n sw + type_memory_size stv < dimword (:256))) ==>
    frag_exec_mem ctx sm sb (\s. s = t) (\s. F)
      (RetQ v (ee with scopes := []))) ==>
  stmt_frag_mem (SOME (bw,cap)) ctx func cx lctx RetQ ce
    (stmt_env ce lctx ty (Return (SOME e)))
    (eval_stmt cx (Return (SOME e))) es
Proof
  strip_tac >> simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  `?bp bsz. ce.ce_return_buf = SOME (PtrVar (Var bp) bsz)` by
    fs[return_buf_frame_def] >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[loweringPostsTheory.stmt_env_def, declare_stmt_local_def,
       compile_stmt_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `lower_value compile_expr ce ty e sa` >>
  rename1 `lower_value compile_expr ce ty e sa = (op,sm)` >>
  simp[] >>
  Cases_on `compile_internal_return_from_env ce ty (lowered_value_type ce e) op (Var rpc) sm` >>
  simp[] >> strip_tac >> gvs[] >>
  rename1 `compile_internal_return_from_env _ _ _ _ _ sm = ((),sb)` >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var` by
    metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends sm sb` by
    (qspec_then `ce` (qspec_then `ty` mp_tac) (cj 2 stmt_return_helpers_labels) >>
     disch_then (qspecl_then [`lowered_value_type ce e`, `op`, `Var rpc`, `sm`] mp_tac) >>
     simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[return_forced_admissible] >>
  drule_at (Pat `lower_value _ _ _ _ _ = _`) internal_return_nonbytes_value_endpoint_mem >>
  disch_then drule_all >> strip_tac >>
  `eval_stmt cx (Return (SOME e)) =
    bind (bind (eval_expr cx e) (read_result cx)) (\v. raise (ReturnException v))` by
    metis_tac[FUN_EQ_THM, eval_return_forced] >>
  asm_rewrite_tac[] >>
  irule gas_outcome_bind_value >> first_assum (irule_at (Pos last)) >>
  conj_tac >- suspend "suffix" >>
  rpt gen_tac >> strip_tac >> Cases_on `res` >- fs[exprSimDefsTheory.expr_exit_def] >>
  simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type]
QED

Resume internal_return_memory_compose_mem[suffix]:
  rpt gen_tac >> BETA_TAC >> strip_tac >> gvs[] >>
  `?gs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
     (INL v,mid with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> metis_tac[]) >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def, gas_marked_path_def] >>
     strip_tac >> drule fragGasPathMemTheory.gas_path_mem_exec >>
     simp[fragExecTheory.exit_result_def]) >>
  `!lo. alloca_prefix lo s0 ==> alloca_prefix lo t` by
    (rpt strip_tac >> drule_all gas_marked_exec_alloca_prefix >> simp[]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x t = SOME w` by fs[expr_post_def] >>
  `ret_buf_frontier (SOME (bw,cap)) ce t` by
    (irule ret_buf_frontier_post >>
     qexistsl_tac [`ce`, `s0`, `sa`] >> fs[]) >>
  irule internal_return_suffix_outcome_mem >> simp[] >>
  qexistsl_tac [`sb`, `sm`] >> simp[] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Finalise internal_return_memory_compose_mem
