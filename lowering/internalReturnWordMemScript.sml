(* Scalar internal returns use a memory-free RET after expression evaluation. *)
Theory internalReturnWordMem
Ancestors
  internalReturnComposeMem internalReturnPathMem internalReturnVoidMem
  stmtSimReturn stmtSimReturnWiden ctorReturnFrame bodySim
  stmtLowering stmtLoweringMono exprLoweringProps emitHelperProps
  compileEnv loweringPosts exprSimMemDefs fragExec venomExecSemantics venomState

Theorem internal_return_word_code[local]:
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  cenv.ce_returns_count = 1 /\ cenv.ce_return_buf = NONE /\ is_word_type ty /\
  stmt_env cenv lctx ty (Return (SOME e)) sa = (cenv'',sb) /\
  lower_value compile_expr cenv ty e sa = (op,s1) ==>
  emit_inst RET [op; Var rpc] [] s1 = ((),sb)
Proof
  strip_tac >> qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, compile_internal_return_from_env_def,
       compile_internal_return_def, word_type_elem_types] >>
  Cases_on `emit_inst RET [op; Var rpc] [] s1` >> simp[oneTheory.one]
QED

Theorem internal_return_word_suffix[local]:
  same_frame cenv cenv' /\
  cenv'.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  emit_inst RET [op; Var rpc] [] s1 = ((),sb) /\
  fn_has_code s1 sb func /\ ret_pc_ok cenv' sa s0 /\
  expr_type e = ty /\ is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME ret_tv /\
  expr_post ctx func cenv' cx e es sa s1 s0 ee v op t /\
  ~t.vs_halted /\ t.vs_current_bb = s1.cs_current_bb /\
  t.vs_inst_idx = LENGTH s1.cs_current_insts ==>
  ?n r. gas_path_mem ctx func t n r /\ exit_result r /\
    !tail. intret_q func cenv cx ret_tv v
      ((ee with gas_obs := tail) with scopes := []) r
Proof
  strip_tac >>
  `post_value_type cenv' e = ty` by metis_tac[post_value_type_word] >>
  `eval_operand op t = SOME (typed_val_to_w256 ret_tv v)` by
    (fs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  `?pc. lookup_var rpc t = SOME pc` by
    (fs[ret_pc_ok_def, expr_post_def] >> metis_tac[]) >>
  `gas_path_mem ctx func t 0
    (IntRet <|iret_values := [typed_val_to_w256 ret_tv v]; iret_adopt_fmp := NONE|> t)` by
    (irule emit_internal_ret_path_mem >> simp[] >>
     qexistsl_tac [`[op]`,`pc`,`rpc`,`s1`,`sb`] >> simp[eval_operands_def]) >>
  qexistsl_tac [`0`, `IntRet <|iret_values := [typed_val_to_w256 ret_tv v];
    iret_adopt_fmp := NONE|> t`] >> simp[exit_result_def] >>
  `state_rel func cenv cx (ee with scopes := []) t` by
    (irule constructor_exit_state_rel >> fs[expr_post_def, stmt_state_rel_def] >>
     metis_tac[]) >>
  simp[intret_q_def, result_rel_def] >> gen_tac >> conj_tac
  >- (
      `ee with <|scopes := []; gas_obs := tail|> =
        (ee with scopes := []) with gas_obs := tail` by simp[] >>
      pop_assum SUBST1_TAC >> simp[state_rel_gas_obs]) >>
  irule intret_vals_match_word >> metis_tac[]
QED

Theorem internal_return_word_mem:
  same_frame cenv cenv' /\
  cenv'.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  cenv'.ce_returns_count = 1 /\ expr_type e = ty /\ is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME ret_tv /\
  expr_sim_mem ctx func cenv' cx ty e es ==>
  stmt_frag_mem NONE ctx func cx lctx (intret_q func cenv cx ret_tv) cenv'
    (stmt_env cenv' lctx ty (Return (SOME e)))
    (eval_stmt cx (Return (SOME e))) es
Proof
  strip_tac >> Cases_on `cenv'.ce_return_buf = NONE`
  >- (irule internal_return_value_counted_mem >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all internal_return_word_code >>
      metis_tac[cs_extends_emit_inst]) >>
  rpt strip_tac >>
  `emit_inst RET [op; Var rpc] [] s1 = ((),sb)` by
    (irule internal_return_word_code >> metis_tac[]) >>
  `cs_extends sa s1` by
    metis_tac[ci_mono_compile_expr_sa, ci_mono_def, pairTheory.SND] >>
  `cs_extends s1 sb` by metis_tac[cs_extends_emit_inst] >>
  `fn_has_code s1 sb func` by metis_tac[fn_has_code_split] >>
  irule internal_return_word_suffix >> metis_tac[]) >>
  simp[stmtSimDefsTheory.stmt_frag_mem_def, return_buf_frame_def]
QED
