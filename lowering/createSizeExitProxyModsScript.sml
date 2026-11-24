Theory createSizeExitProxyMods
Ancestors
  createSizeExitProxy createExprSizeExitDefsMods exprSimFullBundleProps
  s1PrefixDefs venomInst venomState relation list words pair arithmetic createSizeDispatch
  exprLowering stmtLoweringMono vfmConstants exprLoweringProps rich_list exprSimSend
  integer_word createExprSizeExitDefs

Theorem create_size_exit_proxy_mods:
  !mods exps cx ann has_salt rof ks args dflt.
    create_expr_size_exit_mods mods exps cx
      (Call ann (CreateTarget CreateMinimalProxy has_salt rof ks) args dflt)
Proof
  rewrite_tac[create_expr_size_exit_mods_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `expr_vv_sim_full_pre_mods _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[expr_vv_sim_full_pre_mods_def]) >>
  qpat_x_assum `compile_expr _ _ (Call _ _ _ _) _ = _` mp_tac >>
  rewrite_tac[exprSimSendTheory.compile_expr_call, compile_call_def] >>
  Cases_on `compile_create_call compile_expr cenv CreateMinimalProxy has_salt rof args sa` >>
  pure_rewrite_tac[as_stack_val_def, pairTheory.PAIR_EQ] >>
  disch_then (SUBST_ALL_TAC o CONJUNCT2) >>
  `!ce ty e st. ci_mono st (SND (compile_expr ce ty e st))` by
    simp[ci_mono_compile_expr_sa] >>
  `MEM inst.inst_opcode [CREATE; CREATE2]` by
    (simp[] >> metis_tac[]) >>
  drule_then strip_assume_tac expr_sim_full_code_fields >>
  drule_all create_size_dispatch_identification >> strip_tac >>
  qmatch_asmsub_rename_tac `create_size_dispatch_tail _ _ _ _ _ _ _ dispatch_salt _ _` >>
  `~(2 * max_code_size < w2n (54w:256 word))` by
    (rewrite_tac[max_code_size_def, w2n_n2w, dimword_def,
                 venomLayoutTheory.dimindex_256] >> EVAL_TAC) >>
  Cases_on `dispatch_salt` >> gvs[mk_inst_def, eval_operand_def]
QED
