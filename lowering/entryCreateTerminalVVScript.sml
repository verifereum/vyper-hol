(* A terminal stack expression needs no reconstruction of a normal VV post. *)
Theory entryCreateTerminalVV
Ancestors
  entryCreateFocusSpec entryCreateCompletedCut entryCreateBodyCut
  s1PrefixDefs exprSimFullBundleProps exprSimDefs exprSimStack stmtSimProps
  vyperSystemControl gasExemptCert gasStorage vyperStorageFootprint
  exprLowering compileEnv context vyperInterpreter vyperState

Theorem terminal_calls_no_success:
  (target = RawRevert \/ target = SelfDestructTarget) ==>
  !st. ?exc ee. eval_expr cx (Call ann target args dflt) st = (INR exc,ee)
Proof
  strip_tac >> gen_tac >>
  Cases_on `eval_expr cx (Call ann target args dflt) st` >>
  rename1 `eval_expr _ _ _ = (res,_)` >> Cases_on `res` >> gvs[] >>
  metis_tac[raw_revert_no_success, selfdestruct_no_success]
QED

Theorem terminal_source_views[local]:
  (!st. ?exc ee. eval_expr cx e st = (INR exc,ee)) ==>
  (!st. ?exc ee. bind (eval_expr cx e) (read_result cx) st = (INR exc,ee)) /\
  (!st exc ee. bind (eval_expr cx e) (read_result cx) st = (INR exc,ee) <=>
               eval_expr cx e st = (INR exc,ee)) /\
  (!st. SND (eval_expr cx e st) = SND (bind (eval_expr cx e) (read_result cx) st)) /\
  (!st. ignore_bind (eval_expr cx e) (return ()) st =
        ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()) st)
Proof
  disch_tac >> rpt conj_tac >> rpt gen_tac >>
  first_x_assum (qspec_then `st` strip_assume_tac) >> simp[ignore_bind_def,bind_def]
QED

Theorem terminal_scoped_outcome_vv[local]:
  (!st. ?exc ee. eval_expr cx e st = (INR exc,ee)) /\
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 sa sb
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    (expr_sim_full_post (DF,lo,d,C,f) ce cx e (es,sa,sb,s,op,G,tn))
    (create_operand_exit_post C cx) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 sa sb
    (eval_expr cx e) (es,s,G,tn) Q (create_operand_exit_post C cx)
Proof
  strip_tac >> drule terminal_source_views >> strip_tac >>
  qpat_x_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [scoped_operand_outcome_def]) >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `marks`
  >- (disj1_tac >> simp[gas_bad_storage_at_def] >>
      conj_tac >- fs[gas_bad_storage_at_def] >>
      rename1 `gas_origin_ptr_focus _ _ _ (_,_,_,_,stop)` >>
      qexistsl_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`stop`] >> simp[])
  >- (disj2_tac >> disj1_tac >>
      `?exc. res = INR exc` by
        (qpat_assum `!tail. bind _ _ _ = (res,_)` (qspec_then `[]` assume_tac) >>
         qpat_assum `!st. ?exc ee. bind _ _ st = _`
           (qspec_then `es with gas_obs := gas_explicit marks s.vs_gas_readings`
             strip_assume_tac) >> fs[] >> qexists_tac `exc` >> simp[]) >> gvs[] >>
      qexistsl_tac [`INR exc`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
      rpt strip_tac >> first_x_assum drule >>
      simp[expr_sim_full_post_def,create_operand_exit_post_def,
           halt_exit_def,expr_exit_INR_type]) >>
  disj2_tac >> disj2_tac >>
  rename1 `gas_origin_ptr_focus _ _ _ (_,_,_,_,stop)` >>
  qexistsl_tac [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`stop`] >> simp[] >>
  conj_tac
  >- (irule gas_exempt_cert_source_cong >>
      qexists_tac `ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ())` >> simp[]) >>
  qexists_tac `H` >> simp[]
QED

Theorem terminal_operand_cut_vv[local]:
  (!st. ?exc ee. eval_expr cx e st = (INR exc,ee)) /\
  create_operand_cut sa sb E C f tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s) ==>
  create_operand_cut sa sb E C f tops cx st0 (eval_expr cx e) (es,s)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  drule terminal_source_views >> strip_tac >>
  simp[create_operand_cut_def,create_body_cut_def] >> rpt strip_tac >>
  qpat_x_assum `!st. ?exc ee. eval_expr _ _ st = _`
    (qspec_then `es with gas_obs := gas_explicit (create_cut_marks E before) s.vs_gas_readings ++ tail`
      strip_assume_tac) >> gvs[] >>
  qpat_x_assum `!p d k before hit after.
      create_interior_visit _ _ _ _ _ (p,d,k) _ (before,hit,after) ==> _` drule >>
  disch_then drule >>
  disch_then (qspecl_then [`H`,`tail`,`INR exc`,`ee`] mp_tac) >>
  simp[create_cut_failure_def]
QED

(* At this particular VV site, using an already proved value simulation or
   a value cut keeps the end cursor, the marks, and the machine witnesses. *)
Theorem terminal_no_success_vv_site:
  (!st. ?exc ee. eval_expr cx e st = (INR exc,ee)) /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
    ce cx ty e es (st0,sa,sb,sha,shb,StackValue ann op,s,G,tn) ==>
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
    ce cx ty e es (st0,sa,sb,sha,shb,op,s,G,tn) /\
  (expr_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty e es ==>
   scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
     (cx_tops cx) cx st0 sa sb (eval_expr cx e) (es,s,G,tn)
     (\H res ee G' tn' t.
       create_operand_vv_post (DF,lo,d,ctx,func) ce cx e
         (es,sa,sb,s,StackValue ann op,G,tn) H res ee G' tn' t /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts)
     (create_operand_exit_post ctx cx)) /\
  (create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
     (bind (eval_expr cx e) (read_result cx)) (es,s) ==>
   create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
     (eval_expr cx e) (es,s))
Proof
  strip_tac >> conj_asm1_tac
  >- (fs[expr_vv_sim_full_pre_def] >>
      `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
        (irule eval_expr_force_admissible >> simp[] >>
         rpt strip_tac >> rename1 `eval_expr cx e st = (INL _,_)` >>
         qpat_assum `!st. ?exc ee. eval_expr _ _ st = _`
           (qspec_then `st` strip_assume_tac) >> gvs[]) >>
      simp[expr_sim_full_pre_def,lower_value_def,comp_bind_def,unwrap_value_def,comp_return_def] >>
      first_assum ACCEPT_TAC) >>
  conj_tac
  >- (simp[expr_sim_scoped_def] >> strip_tac >> first_x_assum drule >>
      strip_tac >> drule_all terminal_scoped_outcome_vv >> simp[]) >>
  strip_tac >> irule terminal_operand_cut_vv >> simp[]
QED

(* The selected value outcome suffices; no simulation at other sites is needed. *)
Theorem terminal_no_success_vv_pointwise_site:
  (!st. ?exc ee. eval_expr cx e st = (INR exc,ee)) /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
    ce cx ty e es (st0,sa,sb,sha,shb,StackValue ann op,s,G,tn) ==>
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
    ce cx ty e es (st0,sa,sb,sha,shb,op,s,G,tn) /\
  (scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
     (cx_tops cx) cx st0 sa sb (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
     (expr_sim_full_post (DF,lo,d,ctx,func) ce cx e (es,sa,sb,s,op,G,tn))
     (create_operand_exit_post ctx cx) ==>
   scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
     (cx_tops cx) cx st0 sa sb (eval_expr cx e) (es,s,G,tn)
     (\H res ee G' tn' t.
       create_operand_vv_post (DF,lo,d,ctx,func) ce cx e
         (es,sa,sb,s,StackValue ann op,G,tn) H res ee G' tn' t /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts)
     (create_operand_exit_post ctx cx)) /\
  (create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
     (bind (eval_expr cx e) (read_result cx)) (es,s) ==>
   create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
     (eval_expr cx e) (es,s))
Proof
  strip_tac >> drule_all terminal_no_success_vv_site >> strip_tac >> simp[] >>
  strip_tac >> drule_all terminal_scoped_outcome_vv >> simp[]
QED
