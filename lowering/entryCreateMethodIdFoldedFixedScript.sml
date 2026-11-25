(* Fixed literal MethodId has an empty compile interval in both modes. *)
Theory entryCreateMethodIdFoldedFixed
Ancestors
  bodyFullBuiltinEnvMethodIdLiteral entryCreateCompositeFocus entryCreateBuiltinStack
  entryCreateFocusSpec exprSimFullBundleProps s1PrefixDefs
  gasExplicitSites vyperInterpreter vyperState vyperAST
  exprSimHash exprLowering exprLoweringProps compileEnv loweringPosts

Triviality fixed_site_pre:
  expr_sim_full_pre config ce cx ty e es (st0,sa,sb,sha,shb,op,s,G,tn) <=>
  expr_sim_full_hypotheses config ce cx ty e es (st0,sa,sb,sha,shb,op,s,G,tn)
Proof
  PairCases_on `config` >>
  simp[expr_sim_full_pre_def,expr_sim_full_hypotheses_def,expr_sim_full_code_def,CONJ_ASSOC]
QED

Triviality method_id_folded_fixed_value:
  method_id_literal (Literal la l) = SOME bs /\
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty
    (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]) es
    (st0,sa,sb,sha,shb,op,s,G,tn) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
    (cx_tops cx) cx st0 sa sb
    (bind (eval_expr cx (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]))
      (read_result cx)) (es,s,G,tn)
    (expr_sim_full_post (DF,lo,d,ctx,func) ce cx
      (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]) (es,sa,sb,s,op,G,tn))
    (create_operand_exit_post ctx cx) /\
  create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
    (bind (eval_expr cx (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]))
      (read_result cx)) (es,s)
Proof
  simp_tac bool_ss [fixed_site_pre] >> strip_tac >>
  drule_all method_id_literal_fixed_nil >> strip_tac >> gvs[] >>
  fs[expr_sim_full_hypotheses_def] >>
  `create_operand_at sa s` by simp[create_operand_at_def] >>
  reverse conj_tac
  >- (simp[create_operand_cut_def] >> metis_tac[create_operand_empty_scope]) >>
  irule scoped_operand_pure >> simp[] >>
  qexistsl_tac [`es`, `INL (BytesV (TAKE 4 (Keccak_256_w64 bs)))`] >> simp[]
QED

Theorem method_id_folded_fixed_sites:
  method_id_literal (Literal la l) = SOME bs ==>
  (!st0 sa sb sha shb op s G tn.
     expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty
       (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]) es
       (st0,sa,sb,sha,shb,op,s,G,tn) ==>
     scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
       (cx_tops cx) cx st0 sa sb
       (bind (eval_expr cx (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]))
         (read_result cx)) (es,s,G,tn)
       (expr_sim_full_post (DF,lo,d,ctx,func) ce cx
         (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]) (es,sa,sb,s,op,G,tn))
       (create_operand_exit_post ctx cx) /\
     create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
       (bind (eval_expr cx (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]))
         (read_result cx)) (es,s)) /\
  (!st0 sa sb sha shb vv s G tn.
     expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty
       (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]) es
       (st0,sa,sb,sha,shb,vv,s,G,tn) ==>
     scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
       (cx_tops cx) cx st0 sa sb
       (eval_expr cx (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l])) (es,s,G,tn)
       (\H res ee G' tn' t.
          create_operand_vv_post (DF,lo,d,ctx,func) ce cx
            (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l])
            (es,sa,sb,s,vv,G,tn) H res ee G' tn' t /\
          t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts)
       (create_operand_exit_post ctx cx) /\
     create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
       (eval_expr cx (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l])) (es,s))
Proof
  strip_tac >> conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_all method_id_folded_fixed_value >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `?operand. vv = StackValue (BaseT (BytesT (Fixed 4))) operand` by
    (drule compile_expr_method_id_literal >>
     disch_then (qspecl_then [`ce`, `ty`, `BaseT (BytesT (Fixed 4))`, `sa`] assume_tac) >>
     gvs[expr_vv_sim_full_pre_def, compile_literal_vv_def, comp_return_def]) >>
  gvs[] >> irule create_builtin_stack_vv_at >>
  simp[post_value_type_def, expr_type_def, is_word_type_def] >>
  rpt conj_tac
  >- metis_tac[eval_expr_builtin_value] >>
  qexistsl_tac [`sha`,`shb`,`shfunc`,`ty`] >> simp[] >>
  strip_tac >> drule_all method_id_folded_fixed_value >> simp[]
QED
