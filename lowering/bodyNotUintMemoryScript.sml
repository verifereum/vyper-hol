(* Memory-safe unary lowering. *)
Theory bodyNotUintMemory
Ancestors
  bodyNotMemoryProps
  exprSimSource exprSimHypsDefs exprSimProps exprSimUnopProps
  exprSimMemoryStack exprSimMemoryValues exprSimMemDefs loweringPosts
  gasNormalPrefix gasSummary gasSummaryCompose gasContext gasCount fragGasMode
  fragGasPathMem fragGasSeqMem gasExemptCert
  bodyMemoryDefs emitHelperProps fragExecMem instMemFrontier allocaHistoryFragment
  exprLoweringProps emitHelper venomInst venomState words list rich_list
  compileEnv fragExec exprSimDefs valueEncoding vyperValue vyperAST venomExecSemantics
  loweringSlice exprLowering vyperState vyperExprNoControl
  builtinSimple freshWrites varsExt vyperTyping vyperValueOperation integer_word

Theorem body_not_uint256_tail_mem[local]:
  emit_op NOT [x] sm = (op,sb) /\ local_ptrs_reserved cenv sm /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  value_has_type (BaseTV (UintT 256)) v1 /\ expr_type e = BaseT (UintT 256) /\
  sa.cs_next_var <= sm.cs_next_var /\
  expr_post ctx func cenv cx e es sa sm s0 es' v1 x entry /\
  alloca_history func entry /\ s0.vs_alloca_next <= entry.vs_alloca_next /\
  res = unop_result cx (BaseT (UintT 256)) Not [expr_type e] v1 es' ==>
  frag_exec_mem ctx sm sb (\s. s = entry)
    (\s. ?v. res = INL v /\
         expr_post ctx func cenv cx (Builtin (BaseT (UintT 256)) Not [e]) es
           sa sb s0 es' v op s /\
         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s)
    (expr_exit res)
Proof
  strip_tac >> Cases_on `v1` >> gvs[value_has_type_def] >>
  rename1 `expr_post _ _ _ _ _ _ _ _ _ _ (IntV i) _ _` >>
  `stmt_state_rel ctx func cenv cx es' entry /\
   eval_operand x entry = SOME (integer_word$i2w i : bytes32)` by
    gvs[expr_post_def, expr_val_rel_def, vyperValueTheory.evaluate_type_def,
        typed_val_to_w256_def, val_to_w256_def, is_word_type_def] >>
  drule_all body_not_frag_mem_at >>
  disch_then (qspecl_then
    [`integer_word$i2w i : bytes32`, `es'`, `entry`, `cx`, `ctx`,
     `expr_exit (unop_result cx (BaseT (UintT 256)) Not [expr_type e] (IntV i) es')`] mp_tac) >>
  disch_then (mp_tac o MATCH_MP frag_exec_mem_weaken) >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  gvs[unop_result_def, vyperContextTheory.evaluate_builtin_def,
       vyperASTTheory.type_to_int_bound_def, expr_exit_def] >>
  irule expr_post_unop >> simp[is_word_type_def] >>
  conj_tac
  >- (gvs[expr_val_rel_def, vyperValueTheory.evaluate_type_def,
          typed_val_to_w256_def, val_to_w256_def, is_word_type_def] >>
      `~(i < 0)` by intLib.ARITH_TAC >>
      simp[integer_wordTheory.i2w_pos, integer_wordTheory.i2w_def]) >>
  qexistsl_tac [`sm`, `entry`, `IntV i`, `x`] >> simp[]
QED

Theorem compile_not_uint256_sim_mem:
  is_uint256_type (expr_type e) /\ expr_body_pre cenv cx env e es /\
  expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_sim_mem ctx func cenv cx ty (Builtin (expr_type e) Not [e]) es
Proof
  strip_tac >>
  `expr_type e = BaseT (UintT 256)` by
    (Cases_on `expr_type e` >> gvs[] >> rename1 `BaseT bt` >> Cases_on `bt` >> gvs[]) >>
  simp[expr_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  drule lower_value_not >> strip_tac >>
  gvs[compile_invert_def] >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
   (!z. x = Var z ==> not_fresh_at s1 z)` by
    (drule expr_body_pre_lower_value_word_shape >>
     disch_then drule >> simp[is_word_type_def]) >>
  `cs_extends s1 sb` by metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `builtin_args_length_ok Not 1 /\ Not <> Len` by
    simp[vyperContextTheory.builtin_args_length_ok_def] >>
  drule_all eval_expr_unop_cases >> strip_tac
  >- (qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
      disch_then (qspecl_then [`sa`, `s1`, `x`, `INR exc`, `es'`, `s0`] mp_tac) >>
      (impl_tac >- gvs[]) >>
      disch_then (mp_tac o MATCH_MP frag_exec_mem_weaken) >>
      disch_then (qspecl_then
        [`\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\ alloca_history func s`,
         `\s. F`, `expr_exit res`] mp_tac) >>
      (impl_tac >- gvs[]) >> strip_tac >>
      irule frag_exec_mem_exit_prefix >> qexists_tac `s1` >> simp[]) >>
  `value_has_type (BaseTV (UintT 256)) v1` by
    (drule expr_body_pre_word_value >>
     simp[is_word_type_def, vyperValueTheory.evaluate_type_def]) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `x`, `INL v1`, `es'`, `s0`] mp_tac) >>
  (impl_tac >- simp[expr_res_ok_def]) >>
  disch_then (mp_tac o MATCH_MP frag_exec_mem_pre_exit_c) >>
  disch_then (qspecl_then
    [`\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\ alloca_history func s`,
     `expr_exit res`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (fn th => irule (MATCH_MP frag_exec_mem_then th)) >>
  simp[] >> rpt strip_tac >> gvs[] >>
  irule body_not_uint256_tail_mem >> simp[] >> qexistsl_tac [`v1`, `x`] >> simp[]
QED

Theorem compile_not_uint256_vv_sim_mem:
  is_uint256_type (expr_type e) /\ expr_body_pre cenv cx env e es /\
  expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_vv_sim_mem ctx func cenv cx ty (Builtin (expr_type e) Not [e]) es
Proof
  strip_tac >> irule body_expr_vv_sim_mem_stack >>
  conj_tac >- simp[compile_not_abs_stack] >>
  conj_tac >- metis_tac[eval_expr_builtin_value] >>
  irule compile_not_uint256_sim_mem >> simp[] >> qexists_tac `env` >> simp[]
QED

