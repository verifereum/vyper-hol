(* Admissibility boundary for account-member memory simulation. *)
Theory bodyMemBiAccCompose
Ancestors
  bodyMemoryPreds exprSimSource exprSimAccounts exprSimHypsDefs allocLimits
  vyperTyping vyperTypeSystem vyperAST bodyMemBiAccFrag bodyUnopFragMemory
  exprSimUnop exprSimUnopProps exprSimMemDefs exprSimMemoryStack
  exprSimDefs exprLoweringProps exprLowering exprSimHyps
  vyperContext builtinSimple emitHelperProps compileEnv vyperValue vyperTypeInvariants exprUnopSimDefs
Libs
  pairLib

Theorem body_acc_mem_admissible:
  expr_body_pre cenv cx env (Builtin ty (Acc item) es) s ==>
  item <> Code /\
  ?e. es = [e] /\ ty = account_item_type item /\
      expr_type e = BaseT AddressT
Proof
  strip_tac >>
  `item <> Code` by
    (strip_tac >>
     gvs[expr_body_pre_def, alloc_limits_expr_def]) >>
  simp[] >>
  gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  Cases_on `es` >> gvs[] >> rename1 `h::t` >> Cases_on `t` >> gvs[]
QED

Theorem compile_acc_sim_mem:
  !ctx func cenv cx env ty item e es.
    item <> Code /\ expr_type e = BaseT AddressT /\
    expr_body_pre cenv cx env e es /\
    expr_sim_mem ctx func cenv cx (BaseT AddressT) e es ==>
    expr_sim_mem ctx func cenv cx ty
      (Builtin (account_item_type item) (Acc item) [e]) es
Proof
  rpt gen_tac >> strip_tac >> irule compile_unop_sim_mem >>
  simp[account_item_type_word, is_word_type_def, builtin_args_length_ok_def] >>
  qexistsl_tac [`\x. case item of
                 Balance => emit_op BALANCE [x]
               | Codesize => emit_op EXTCODESIZE [x]
               | Codehash => emit_op EXTCODEHASH [x]
               | IsContract => comp_bind (emit_op EXTCODESIZE [x])
                                  (\c. emit_op GT [c; Lit 0w])
               | Address => comp_return x
               | Code => comp_return x`, `BaseT AddressT`] >>
  conj_tac
  >- (rpt strip_tac >> drule_all lower_value_acc >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule expr_body_pre_lower_value_word_shape >> disch_then drule >>
      simp[is_word_type_def]) >>
  reverse conj_tac
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `item` >> gvs[comp_return_def, cs_extends_refl, comp_bind_def] >>
      rpt gen_tac >> strip_tac >>
      rpt (pairarg_tac >> gvs[]) >>
      imp_res_tac emit_op_extends_next_var >>
      metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
  rpt strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs1)` by simp[] >>
  drule expr_body_pre_word_value >> simp[is_word_type_def] >>
  strip_tac >>
  gvs[vyperValueTheory.evaluate_type_def] >>
  Cases_on `v1` >> gvs[value_has_type_def] >>
  irule compile_acc_frag_mem >> simp[] >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs1)` by simp[] >>
  drule_all expr_body_pre_eval >> simp[expr_sim_inv_def]
QED

Theorem compile_acc_vv_sim_mem:
  !ctx func cenv cx env ty item e es.
    item <> Code /\ expr_type e = BaseT AddressT /\
    expr_body_pre cenv cx env e es /\
    expr_sim_mem ctx func cenv cx (BaseT AddressT) e es ==>
    expr_vv_sim_mem ctx func cenv cx ty
      (Builtin (account_item_type item) (Acc item) [e]) es
Proof
  rpt gen_tac >> strip_tac >>
  irule body_expr_vv_sim_mem_stack_word >>
  simp[vyperASTTheory.expr_type_def, account_item_type_word,
       compile_acc_stack] >>
  conj_tac >- metis_tac[eval_expr_builtin_value] >>
  metis_tac[compile_acc_sim_mem]
QED
