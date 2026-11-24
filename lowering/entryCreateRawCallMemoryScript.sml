(* Scoped memory RawCall handoff: use the answer-parametric adapter at the
   selected expression occurrence.  The prefix and request suppliers are
   intentionally parameters; their concrete installations are supplied by
   the neighboring RawCall components. *)
Theory entryCreateRawCallMemory
Ancestors
  bodyFullRawCall bodyFullRawCallAdapter bodySimFull entryCreateFocusSpec entryCreateRawCallMemoryNative
  entryCreateRawCallGeneratedPrefix entryCreateRawCallPrepRun
  entryCreateRawCallWords entryCreateRawCallRequest
  entryCreateRawCallPrepCode
  gasOutcomeFullCompose exprSimFullBundleProps s1PrefixDefs
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState
  venomState list relation arithmetic

Theorem raw_call_memory_answer_post[local]:
  (\H res ee G tn t.
    create_operand_vv_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sb,s0,vv,G0,tn0)
      H res ee G tn t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts) =
  raw_call_vv_answer_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sb,s0,vv,G0,tn0)
Proof
  simp[FUN_EQ_THM, create_operand_vv_post_def, raw_call_vv_answer_post_def,
       PULL_EXISTS, AC CONJ_ASSOC CONJ_COMM]
QED

Theorem raw_call_memory_answer_exit[local]:
  create_operand_exit_post ctx cx = raw_call_vv_answer_exit ctx cx
Proof
  simp[FUN_EQ_THM, create_operand_exit_post_def, raw_call_vv_answer_exit_def]
QED

Theorem raw_call_memory_selected_site:
  body_exprs_full_ok cx args /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) args dflt) es /\
  (!st0 sa sb shadow_sa shadow_sb vv s0 G0 tn0.
    let A = \i source x Q R.
      scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (cx_tops cx) cx st0 i sb source x Q R
    in
    raw_call_vv_answer_rules A ctx /\
    raw_call_vv_prefix_rule A
      (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      (tops,cenv,env,cx,ty,ann,flags,es)
      (st0,sa,sb,shadow_sa,shadow_sb,vv,s0,G0,tn0) /\
    raw_call_vv_request_rule A (DF,lo,d,ctx,func)
      (cenv,env,cx,flags,st0) (es,sa,sb,s0,G0,tn0)) ==>
  expr_vv_sim_scoped
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
    (Call ann (RawCallTarget flags) args dflt) es
Proof
  strip_tac >>
  simp_tac bool_ss [expr_vv_sim_scoped_def, raw_call_memory_answer_post,
                    raw_call_memory_answer_exit] >>
  rpt gen_tac >> disch_tac >>
  gvs[LET_THM, FORALL_AND_THM] >>
  irule (BETA_RULE (Q.ISPEC
    `\i (source:evaluation_state -> (eval_result + vyperState$exception) # evaluation_state)
        x Q R. scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 i sb source x Q R` (Q.GEN `A` raw_call_expr_vv_by))) >>
  first_assum (irule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
  qexistsl_tac [`ty`,`tops`,`shb`,`sha`,`shadow_func`] >>
  simp[] >>
  qpat_x_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac [raw_call_vv_pre_def, expr_vv_sim_full_pre_def] >>
  disch_then ACCEPT_TAC
QED
