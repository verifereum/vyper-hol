Theory bodyMemBopRestWordSim
Ancestors
  bodyMemBopRestWordCompose bodyMemBopRestWordTailMem bodyMemoryPreds
  exprSimBopRestWordCompose exprSimBopRestWordFacts exprSimBopRestWordLayout
  exprSimBopRestWordBasics exprSimSource exprSimHyps exprSimUnwrapProps
  exprOperandVar allocLimits exprSimMemDefs exprSimBopRestWordTail
Libs
  pairLib

Theorem compile_rest_word_membership_sim_mem:
  !tops ctx func cenv cx env ty ann bop e1 e2 bd es.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
    (bop = In \/ bop = NotIn) /\
    is_word_type (expr_type e1) /\
    expr_type e2 = ArrayT (expr_type e1) bd /\
    (!a t n elems. e2 <> Builtin a (MakeArray t n) elems) /\
    body_exprs_mem_ok cx [e1;e2] ==>
    expr_sim_mem ctx func cenv cx ty (Builtin ann (Bop bop) [e1;e2]) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `ann = BaseT BoolT` by
    (qpat_x_assum `expr_body_pre _ _ _ (Builtin _ _ _) _` mp_tac >>
     qpat_x_assum `bop = In \/ bop = NotIn` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[exprSimHypsDefsTheory.expr_body_pre_def,
          vyperTypeSystemTheory.well_typed_expr_def,
          vyperTypeSystemTheory.well_typed_builtin_app_def] >>
     Cases_on `bop` >> simp[vyperTypeSystemTheory.well_typed_binop_def] >> metis_tac[]) >>
  drule_all rest_word_nonliteral_dispatch >> disch_tac >>
  simp[expr_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  irule expr_sim_mem_word_outcome >>
  conj_tac >- simp[vyperASTTheory.expr_type_def, compileEnvTheory.is_word_type_def] >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[Once exprLoweringTheory.lower_value_def, compileEnvTheory.comp_bind_def,
    exprBopLoweringTheory.compile_expr_bop] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 exprLoweringTheory.compile_expr_raw_def)),
    Q.INST [`et` |-> `expr_type e1`, `bd` |-> `bd`] rest_word_nonliteral_dispatch,
    exprBopLoweringTheory.lower_value_child_call] >>
  rpt (pairarg_tac >> gnvs[]) >>
  simp[exprBopLoweringTheory.as_stack_val_pair, exprLoweringTheory.unwrap_value_def,
    compileEnvTheory.comp_return_def] >> strip_tac >>
  qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `as_stack_val _ tailcomp` >>
  PairCases_on `tailcomp` >>
  simp[exprBopLoweringTheory.as_stack_val_pair] >> strip_tac >>
  gnvs[exprLoweringTheory.unwrap_value_def, compileEnvTheory.comp_return_def,
    compileEnvTheory.comp_bind_def, ETA_AX] >>
  qpat_x_assum `!ty st ret_ty e1' cenv' ce. _` kall_tac >>
  rule_assum_tac (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  `cs_extends st2 sb` by suspend "tail_extends" >>
  suspend "operand_boundaries"
QED

Resume compile_rest_word_membership_sim_mem[tail_extends]:
  qpat_x_assum `compile_var_array_membership _ _ _ _ _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  Cases_on `bd` >>
  simp[exprLoweringTheory.compile_var_array_membership_def,
    compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[compileEnvTheory.comp_return_def] >>
  qpat_assum `compile_array_membership_loop _ _ _ _ _ _ _ _ = _`
    (strip_assume_tac o REWRITE_RULE [rest_word_loop_factor_eq]) >>
  rename1 `rest_word_loop_prefix _ _ _ _ _ loopst = (h,cl)` >>
  drule rest_word_loop_prefix_shape >>
  rewrite_tac[rest_word_loop_prefix_shape_def] >> strip_tac >>
  drule rest_word_ptr_load_shape >> strip_tac >>
  drule rest_word_loop_suffix_shape >>
  rewrite_tac[rest_word_loop_suffix_shape_def] >> strip_tac >>
  `cs_extends loopst sb` by
    (simp[compileEnvTheory.cs_extends_def] >> qexists `TAKE 6 sb.cs_blocks` >> simp[]) >>
  qpat_assum `compile_ptr_load _ _ _ (vv_operand arr_vv) st2 = _`
    (mp_tac o MATCH_MP rest_word_ptr_load_shape) >> strip_tac >>
  drule_all rest_word_capacity_check_shape >> strip_tac >>
  `cs_extends st2 loopst` by
    simp[compileEnvTheory.cs_extends_def,
      rich_listTheory.IS_PREFIX_APPEND, listTheory.APPEND_ASSOC] >>
  metis_tac[compileEnvTheory.cs_extends_trans]
QED
Resume compile_rest_word_membership_sim_mem[operand_boundaries]:
  `expr_body_pre cenv cx env e1 es` by
    (irule expr_body_pre_builtin_arg >>
     conj_tac >- fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
     qexistsl [`BaseT BoolT`, `[e1; e2]`, `Bop bop`, `es`] >> simp[]) >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  qpat_assum `compile_expr _ _ e2 _ = _`
    (mp_tac o MATCH_MP (CONJUNCT1 exprLoweringPropsTheory.compile_expr_grows)) >> strip_tac >>
  `cs_extends sa st2` by metis_tac[compileEnvTheory.cs_extends_trans] >>
  `cs_extends st1 sb` by metis_tac[compileEnvTheory.cs_extends_trans] >>
  `fn_has_code sa st1 func /\ fn_has_code st1 st2 func /\ fn_has_code st2 sb func` by
    metis_tac[fragExecTheory.fn_has_code_mid, compileEnvTheory.cs_extends_refl] >>
  `local_ptrs_reserved cenv st1` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `body_expr_mem_ok cx e1` by fs[body_exprs_mem_ok_def] >>
  `expr_sim_mem ctx func cenv cx (expr_type e1) e1 es` by
    metis_tac[body_expr_mem_ok_def] >>
  irule rest_word_mixed_outcome_mem >>
  qpat_assum `lower_value _ _ _ e1 _ = _` (irule_at Any) >>
  qexistsl [`arr_vv`, `st2`] >>
  simp[] >> rpt gen_tac >> strip_tac >>
  `bind (eval_expr cx e1) (read_result cx)
     (es with gas_obs := gas_explicit left s0.vs_gas_readings) =
       (INL v1, mid with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gasSummaryTheory.gas_marked_exec_def]) >>
     disch_then (mp_tac o CONJUNCT1) >>
     disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env e1
      (es with gas_obs := gas_explicit left s0.vs_gas_readings)` by simp[] >>
  `expr_sim_inv cenv cx env (mid with gas_obs := [])` by
    metis_tac[expr_body_pre_eval] >>
  `expr_body_pre cenv cx env e2 (mid with gas_obs := [])` by
    (irule expr_body_pre_builtin_arg >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`BaseT BoolT`, `[e1; e2]`, `Bop bop`, `es`] >> simp[]) >>
  `body_expr_mem_ok cx e2` by
    (qpat_x_assum `body_exprs_mem_ok _ _` mp_tac >>
     simp[body_exprs_mem_ok_def] >> strip_tac >>
     first_x_assum irule >>
     drule (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >> strip_tac >> metis_tac[]) >>
  conj_tac >- metis_tac[body_expr_mem_ok_def] >>
  conj_tac
  >- (irule expr_body_pre_vv_gas_admissible >>
      qexistsl [`cenv`, `env`] >> gvs[]) >>
  conj_tac
  >- (drule (REWRITE_RULE [ETA_AX] exprBopSimPropsTheory.bop_value_scopes_dom) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  suspend "typed_tail"
QED

Resume compile_rest_word_membership_sim_mem[typed_tail]:
  `eval_expr cx e2
     (mid with gas_obs := gas_explicit right t.vs_gas_readings) =
       (INL tv, fin with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ (eval_expr cx e2) _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gasSummaryTheory.gas_marked_exec_def]) >>
     disch_then (mp_tac o CONJUNCT1) >>
     disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env e2
     (mid with gas_obs := gas_explicit right t.vs_gas_readings)` by gvs[] >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  `vv_holds cenv cx (expr_type e2) tv arr_vv (fin with gas_obs := []) u` by
    fs[loweringPostsTheory.vv_post_def] >>
  drule rest_word_vv_read_suffix >>
  simp[] >> disch_then (qx_choose_then `v2` assume_tac) >>
  `value_has_type tvt v2` by metis_tac[] >>
  `?et. tvt = ArrayTV et bd /\
        evaluate_type (get_tenv cx) (expr_type e1) = SOME et` by
    (qpat_x_assum `evaluate_type _ (expr_type e2) = _` mp_tac >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >> metis_tac[]) >>
  gnvs[] >>
  `?av. v2 = ArrayV av` by
    (Cases_on `v2` >> fs[vyperTypingTheory.value_has_type_def]) >>
  gnvs[] >>
  `vv_post ctx func cenv cx e2 (mid with gas_obs := []) st1 st2 t
      (fin with gas_obs := []) (Value (ArrayV av)) arr_vv u` by
    (qpat_assum `!tail. read_result _ _ _ = _`
       (qspec_then `[]` assume_tac) >>
     drule vv_post_read_result >> simp[] >> metis_tac[]) >>
  `expr_body_pre cenv cx env e1
      (es with gas_obs := gas_explicit left s0.vs_gas_readings)` by simp[] >>
  `value_has_type et v1` by
    (drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_value) >>
     strip_tac >> gvs[]) >>
  `eval_operand needle t = SOME (typed_val_to_w256 et v1)` by
    (qpat_x_assum `expr_post _ _ _ _ e1 _ _ _ _ _ _ _ _` mp_tac >>
     simp[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def] >>
     metis_tac[]) >>
  `eval_operand needle u = SOME (typed_val_to_w256 et v1)` by
    (Cases_on `needle` >>
     fs[venomStateTheory.eval_operand_def, loweringPostsTheory.vv_post_def] >>
     metis_tac[]) >>
  `!z. needle = Var z \/ vv_operand arr_vv = Var z ==> not_fresh_at st2 z` by
    (rpt strip_tac
     >- metis_tac[freshWritesTheory.not_fresh_at_mono]
     >> drule (cj 1 exprOperandVarTheory.compiler_compile_var) >> simp[]) >>
  `(?w. eval_operand (vv_operand arr_vv) u = SOME w) /\
   (case vv_location arr_vv of NONE => LocMemory | SOME l => l) <> LocCalldata` by
    (qpat_x_assum `vv_holds _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `arr_vv` >>
     simp[loweringPostsTheory.vv_holds_def, contextTheory.vv_operand_def,
          contextTheory.vv_location_def, loweringPostsTheory.expr_val_rel_def]
     >- metis_tac[] >>
     rename1 `p.ptr_location` >>
     Cases_on `p.ptr_location` >> simp[] >> metis_tac[]) >>
  `type_alloc_ok cenv (ArrayT (expr_type e1) bd)` by
    (`alloc_limits_expr cenv e2` by fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
     drule alloc_limits_expr_type_alloc_ok >> simp[]) >>
  `(case bd of Fixed n => n | Dynamic n => n) < dimword (:256)` by
    metis_tac[rest_word_array_alloc_bound] >>
  `~u.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ right _ _ _`
       (strip_assume_tac o REWRITE_RULE [gasSummaryTheory.gas_marked_exec_def]) >>
     metis_tac[fragGasModeTheory.gas_marked_path_exec,
       fragGasPathTheory.gas_path_normal]) >>
  `alloca_inv u` by fs[loweringPostsTheory.vv_post_def,
    exprLoweringPropsTheory.stmt_state_rel_def, compileEnvTheory.state_rel_def] >>
  suspend "safe_tail"
QED

Resume compile_rest_word_membership_sim_mem[safe_tail]:
  `?q. gas_marked_path T ctx func u 0 (OK q) /\
       alloca_history func q /\ u.vs_alloca_next <= q.vs_alloca_next /\
       q.vs_current_bb = sb.cs_current_bb /\
       q.vs_inst_idx = LENGTH sb.cs_current_insts /\
       vv_post ctx func cenv cx e2 (mid with gas_obs := []) st1 st2 t
         (fin with gas_obs := []) (Value (ArrayV av)) arr_vv q /\
       eval_operand op q = SOME (bool_to_word
         (if bop = In then evaluate_in_array (ArrayTV et bd) v1 av
          else ~evaluate_in_array (ArrayTV et bd) v1 av))` by
    (Cases_on `bd` >> gnvs[]
     >- (drule (Q.INST [`loc` |-> `(case vv_location vv of SOME l => l | NONE => LocMemory)`]
           rest_word_fixed_tail_mem) >>
         simp[] >> disch_then drule >> simp[] >> disch_then drule >>
         simp[] >> disch_then drule >> simp[] >> metis_tac[]) >>
     drule (Q.INST [`loc` |-> `(case vv_location vv of SOME l => l | NONE => LocMemory)`]
       rest_word_dynamic_tail_mem) >>
     simp[] >> disch_then drule >> simp[] >> disch_then drule >>
     simp[] >> disch_then drule >> simp[] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `eval_operand op q = SOME (bool_to_word answer)` >>
  `!ee. bop_result cx (BaseT BoolT) bop [expr_type e1; ArrayT (expr_type e1) bd]
          v1 (ArrayV av) ee = INL (BoolV answer)` by
    (simp[exprBopSimDefsTheory.bop_result_def,
          vyperContextTheory.evaluate_builtin_def] >>
     Cases_on `bop = In` >>
     fs[Abbr `answer`, vyperValueOperationTheory.evaluate_binop_def,
        vyperValueOperationTheory.binop_negate_def]) >>
  qexistsl [`[]`, `fin`, `q`, `BoolV answer`] >>
  simp[gasSummaryTheory.gas_marked_exec_def] >>
  conj_tac
  >- (qpat_assum `!tail. read_result _ _ _ = _` (qspec_then `[]` assume_tac) >>
      drule vv_post_read_result >> simp[] >> metis_tac[]) >>
  simp[loweringPostsTheory.expr_val_rel_def, loweringPostsTheory.expr_val_at_def,
       compileEnvTheory.is_word_type_def, vyperValueTheory.evaluate_type_def,
       valueEncodingTheory.typed_val_to_w256_def, valueEncodingTheory.val_to_w256_def,
       venomExecSemanticsTheory.bool_to_word_def] >>
  Cases_on `answer` >> fs[venomExecSemanticsTheory.bool_to_word_def]
QED
Finalise compile_rest_word_membership_sim_mem
