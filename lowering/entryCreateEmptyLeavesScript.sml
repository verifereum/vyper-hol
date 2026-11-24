(* Empty expression fragments stop at their entry cursor. The scoped
   simulation and the legacy full simulation use the same nil witness. *)
Theory entryCreateEmptyLeaves
Ancestors
  entryCreateFocusSpec entryCreateCompositeFocus bodyFullEmptyLeafData
  bodyFullExprCore bodyFullLiteralWord bodyFullNameVV bodyFullNameNonword
  exprSimFullBundleProps s1PrefixDefs exprSimHypsDefs
  gasExplicitSites vyperInterpreter vyperState vyperAST

Theorem value_pre_bundle[local]:
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
    ce cx ty e es (st0,sa,sb,sha,shb,op,s0,G0,tn0) <=>
  expr_sim_full_hypotheses (DF,lo,d,ctx,shctx,PG,func,shfunc)
    ce cx ty e es (st0,sa,sb,sha,shb,op,s0,G0,tn0)
Proof
  simp[expr_sim_full_pre_def, expr_sim_full_hypotheses_def, expr_sim_full_code_def,
       CONJ_ASSOC]
QED

Theorem vv_pre_bundle[local]:
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
    ce cx ty e es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) <=>
  expr_vv_sim_full_hypotheses (DF,lo,d,ctx,shctx,PG,func,shfunc)
    ce cx ty e es (st0,sa,sb,sha,shb,vv,s0,G0,tn0)
Proof
  simp[expr_vv_sim_full_pre_def, expr_vv_sim_full_hypotheses_def, expr_sim_full_code_def,
       CONJ_ASSOC]
QED

Theorem empty_leaf_cut[local]:
  create_operand_at sa s ==> create_operand_cut sa sa E C f tops cx st0 source (es,s)
Proof
  rw[create_operand_cut_def] >> metis_tac[create_operand_empty_scope]
QED

Theorem empty_leaf_outcome[local]:
  create_operand_at sa s /\ ~s.vs_halted /\
  (?res. (!tail. source (es with gas_obs := tail) = (res,es with gas_obs := tail)) /\
         (!H. valid_horizon cx st0 H es.storage_trace ==>
              Q H res (es with gas_obs := []) G tn s)) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 sa sa source (es,s,G,tn) Q R
Proof
  strip_tac >> irule scoped_operand_pure >>
  simp[] >> qexistsl_tac [`es`,`res`] >> simp[]
QED

Theorem empty_leaf_value[local]:
  (!st0 sa sb sha shb op s0 G0 tn0.
    expr_sim_full_hypotheses (DF,lo,d,ctx,shctx,PG,func,shfunc)
      ce cx ty e es (st0,sa,sb,sha,shb,op,s0,G0,tn0) ==>
    sb = sa /\ ?res.
      (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := tail) =
              (res,es with gas_obs := tail)) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
         expr_sim_full_post (DF,lo,d,ctx,func) ce cx e (es,sa,sb,s0,op,G0,tn0)
           H res (es with gas_obs := []) G0 tn0 s0)) ==>
  expr_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty e es /\
  !st0 sa sb sha shb op s0 G0 tn0.
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
      ce cx ty e es (st0,sa,sb,sha,shb,op,s0,G0,tn0) ==>
    create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
      (bind (eval_expr cx e) (read_result cx)) (es,s0)
Proof
  strip_tac >> simp[expr_sim_scoped_def, value_pre_bundle] >>
  conj_tac >> rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
  gvs[expr_sim_full_hypotheses_def] >>
  FIRST [irule empty_leaf_cut, irule empty_leaf_outcome] >>
  simp[create_operand_at_def] >> metis_tac[]
QED

Theorem empty_leaf_vv[local]:
  (!st0 sa sb sha shb vv s0 G0 tn0.
    expr_vv_sim_full_hypotheses (DF,lo,d,ctx,shctx,PG,func,shfunc)
      ce cx ty e es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) ==>
    sb = sa /\ ?res.
      (!tail. eval_expr cx e (es with gas_obs := tail) = (res,es with gas_obs := tail)) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
         expr_vv_sim_full_post (DF,lo,d,ctx,func) ce cx e (es,sa,sb,s0,vv,G0,tn0)
           H res (es with gas_obs := []) G0 tn0 s0)) ==>
  expr_vv_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty e es /\
  !st0 sa sb sha shb vv s0 G0 tn0.
    expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
      ce cx ty e es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) ==>
    create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
      (eval_expr cx e) (es,s0)
Proof
  strip_tac >> simp[expr_vv_sim_scoped_def, vv_pre_bundle] >>
  conj_tac >> rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
  gvs[expr_vv_sim_full_hypotheses_def] >>
  FIRST [irule empty_leaf_cut, irule empty_leaf_outcome] >>
  simp[create_operand_at_def] >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_vv_sim_full_post _ _ _ _ _ _ _ _ _ _ _`
    (drule_then (strip_assume_tac o SIMP_RULE (srw_ss())
       [expr_vv_sim_full_post_def, expr_sim_full_endpoint_def])) >>
  simp[create_operand_vv_post_def] >> gvs[]
QED

(* Every conclusion concerns the compile interval at the supplied cursor,
   not an arbitrary visit to the same block. *)
Theorem create_empty_leaf_cases:
  (!ann nsid mid.
    expr_body_pre ce cx env (FlagMember ann nsid mid) es ==>
    expr_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty (FlagMember ann nsid mid) es /\
    !st0 sa sb sha shb op s0 G0 tn0.
      expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
        ce cx ty (FlagMember ann nsid mid) es (st0,sa,sb,sha,shb,op,s0,G0,tn0) ==>
      create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
        (bind (eval_expr cx (FlagMember ann nsid mid)) (read_result cx)) (es,s0)) /\
  (!ann nsid mid.
    expr_body_pre ce cx env (FlagMember ann nsid mid) es ==>
    expr_vv_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty (FlagMember ann nsid mid) es /\
    !st0 sa sb sha shb vv s0 G0 tn0.
      expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
        ce cx ty (FlagMember ann nsid mid) es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) ==>
      create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
        (eval_expr cx (FlagMember ann nsid mid)) (es,s0)) /\
  (!ann l.
    expr_body_pre ce cx env (Literal ann l) es /\ is_word_type ann ==>
    expr_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty (Literal ann l) es /\
    !st0 sa sb sha shb op s0 G0 tn0.
      expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
        ce cx ty (Literal ann l) es (st0,sa,sb,sha,shb,op,s0,G0,tn0) ==>
      create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
        (bind (eval_expr cx (Literal ann l)) (read_result cx)) (es,s0)) /\
  (!ann l.
    expr_body_pre ce cx env (Literal ann l) es /\ is_word_type ann ==>
    expr_vv_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty (Literal ann l) es /\
    !st0 sa sb sha shb vv s0 G0 tn0.
      expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
        ce cx ty (Literal ann l) es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) ==>
      create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
        (eval_expr cx (Literal ann l)) (es,s0)) /\
  (!ann id.
    expr_body_pre ce cx env (Name ann id) es /\ ~is_word_type ann ==>
    expr_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty (Name ann id) es /\
    !st0 sa sb sha shb op s0 G0 tn0.
      expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
        ce cx ty (Name ann id) es (st0,sa,sb,sha,shb,op,s0,G0,tn0) ==>
      create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
        (bind (eval_expr cx (Name ann id)) (read_result cx)) (es,s0)) /\
  (!ann id.
    expr_body_pre ce cx env (Name ann id) es ==>
    expr_vv_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty (Name ann id) es /\
    !st0 sa sb sha shb vv s0 G0 tn0.
      expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
        ce cx ty (Name ann id) es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) ==>
      create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
        (eval_expr cx (Name ann id)) (es,s0))
Proof
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  FIRST [irule empty_leaf_value, irule empty_leaf_vv] >> rpt gen_tac >> strip_tac
  >- (drule_all flag_member_value_nil >> metis_tac[])
  >- (drule_all flag_member_vv_nil >> simp[])
  >- (drule_all literal_word_value_nil >> metis_tac[])
  >- (drule_all literal_word_vv_nil >> metis_tac[])
  >- (drule_all name_nonword_nil >> metis_tac[]) >>
  drule_all name_vv_nil >> metis_tac[]
QED
