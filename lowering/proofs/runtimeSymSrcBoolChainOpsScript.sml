Theory runtimeSymSrcBoolChainOps
Ancestors
  runtimeSymSrcContextCopy runtimeSymSrcEmission runtimeSymSrcBlockEmission
  exprLowering compileEnv loweringShapeDefs vyperAST venomInst list

Theorem runtime_sym_compile_bool_chain_ops:
  runtime_sym_label exit_lbl /\
  (!e s v s'. MEM e es /\ EVERY runtime_sym_inst (state_insts s) /\
     lower_value cfn ce (BaseT BoolT) e s = (v,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v) /\
  EVERY runtime_sym_inst (state_insts st) /\
  compile_bool_chain_ops cfn ce d result exit_lbl es st = (u,st') ==>
  EVERY runtime_sym_inst (state_insts st')
Proof
  Cases_on `u` >> qid_spec_tac `st'` >> qid_spec_tac `st` >> Induct_on `es`
  >- simp[compile_bool_chain_ops_def, comp_return_def] >>
  qx_gen_tac `head` >> rpt gen_tac >> strip_tac >>
  `!s v s'. EVERY runtime_sym_inst (state_insts s) /\
      lower_value cfn ce (BaseT BoolT) head s = (v,s') ==>
      EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v`
    by (rpt gen_tac >> strip_tac >>
        qpat_assum `!e s v s'. MEM e (head::es) /\ _ ==> _`
          (qspecl_then [`head`,`s`,`v`,`s'`] mp_tac) >> simp[]) >>
  qpat_x_assum `compile_bool_chain_ops _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `es`
  >- (simp[compile_bool_chain_ops_def, comp_bind_def, comp_ignore_bind_def] >>
      rpt (pairarg_tac >> simp[]) >> strip_tac >>
      qpat_assum `!s v s'. _ /\ lower_value _ _ _ _ _ = _ ==> _`
        (drule_all_then strip_assume_tac) >>
      drule_all_then assume_tac runtime_sym_assign >>
      drule_all_then ACCEPT_TAC runtime_sym_jump) >>
  rename1 `compile_bool_chain_ops _ _ _ _ _ (head::next::rest) _ = _` >>
  simp[Once compile_bool_chain_ops_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >>
  rename1 `lower_value _ _ _ _ _ = (c,s1)` >>
  Cases_on `fresh_label (if d then "and_next" else "or_true") s1` >>
  rename1 `fresh_label _ s1 = (l1,s2)` >>
  Cases_on `fresh_label (if d then "and_false" else "or_next") s2` >>
  Cases_on `d` >> rule_assum_tac (REWRITE_RULE [COND_CLAUSES]) >>
  simp[NoAsms, comp_bind_def, comp_return_def] >>
  qpat_assum `fresh_label _ s1 = _` (fn th => simp[NoAsms, th]) >>
  qpat_assum `fresh_label _ s2 = _` (fn th => simp[NoAsms, th]) >>
  rpt (pairarg_tac >> pop_assum (fn th => assume_tac th >> simp[NoAsms, th])) >>
  strip_tac >>
  qpat_assum `!s v s'. _ /\ lower_value _ _ _ _ _ = _ ==> _`
    (drule_all_then strip_assume_tac) >>
  imp_res_tac runtime_sym_fresh_label >>
  rename1 `fresh_label _ s2 = (_,s3)` >>
  `EVERY runtime_sym_inst (state_insts s3)` by asm_rewrite_tac[] >>
  drule_all_then assume_tac runtime_sym_jnz >>
  imp_res_tac runtime_sym_new_block_result >>
  rename1 `emit_inst ASSIGN [Lit _] _ s5 = (_,s6)` >>
  `EVERY runtime_sym_inst (state_insts s6)` by
    (irule runtime_sym_assign >>
     goal_assum (drule_at (Pat `emit_inst ASSIGN _ _ _ = _`)) >>
     rewrite_tac[stackPlanTypesTheory.is_label_operand_def] >> asm_rewrite_tac[]) >>
  drule_all_then assume_tac runtime_sym_jump >>
  qpat_assum `!st st'. _ ==> EVERY runtime_sym_inst (state_insts st')` irule >>
  (reverse conj_tac
   >- (asm_rewrite_tac[] >>
       rename1 `compile_bool_chain_ops _ _ _ _ _ _ tail_st = ((),st')` >>
       qexists `tail_st` >> asm_rewrite_tac[]) >>
   rpt gen_tac >> strip_tac >>
   `MEM e (head::next::rest)` by
     (pure_once_rewrite_tac[MEM] >> asm_rewrite_tac[]) >>
   qpat_assum `!e s v s'. MEM e (head::_) /\ _ ==> _`
     (drule_all_then ACCEPT_TAC))
QED
