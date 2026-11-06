(* Outcome composition for the consuming local assignment action. *)
Theory stmtSimAssignCompose
Ancestors
  stmtSimAssignPath stmtSimAssignSource stmtSimDeclCompose gasSummary gasSummaryCompose
  gasOutcome gasExemptCert stmtSimDefs exprSimDefs loweringPosts stmtSimProps
  vyperInterpreter vyperState venomState compileEnv valueEncoding
  list finite_map stmtLowering emitHelperProps exprLoweringProps
Libs monadsyntax

Theorem assign_local_marked_exec:
  gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
    (stmt_res_ok lctx) es /\
  gas_marked_exec memory (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx))
      (write_place cx (MemoryPlace id []))) (es,s0) marks res ee r ==>
  gas_marked_exec memory (ctx,func)
    (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
    (es,s0) marks res ee r
Proof
  strip_tac >> drule assign_local_admissible_run >>
  strip_tac >> gvs[gas_marked_exec_def]
QED

Theorem assign_local_rhs_outcome:
  (!memory tops ctx' func' cx' e' es' s0 marks err ee leaf fin.
     gas_exempt_cert memory tops (ctx',func')
       (ignore_bind (bind (eval_expr cx' e') (read_result cx')) (return ()))
       (es',s0) marks (err,ee) (leaf,fin) ==>
     gas_exempt_cert memory tops (ctx',func')
       (ignore_bind (eval_expr cx' e') (return ()))
       (es',s0) marks (err,ee) (leaf,fin)) /\
  gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
    (stmt_res_ok lctx) es /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
  (!gs v es1 entry. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gs) = (INL v,es1) /\
     lookup_scopes id es1.scopes = SOME entry ==> store_lays_out etv entry.type v) /\
  emit_void MSTORE [Var p;op] sb = ((),sf) /\ fn_has_code sb sf func /\
  ~block_is_terminated sf /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s0)
    (\res ee t. ?v. res = INL v /\
      expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) (es,s0)
    (stmt_post ctx func cx lctx cenv cenv sa sf s0)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  strip_tac >> rewrite_tac[gas_outcome_def] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_outcome_def]) >> strip_tac
  >- (qexists `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [gas_summary_at_def]) >> strip_tac
      >- (gvs[] >> drule_all assign_local_normal_continuation >> strip_tac >>
          simp[gas_summary_at_def] >>
          qexistsl [`INL ()`, `ff`, `OK u`] >> simp[stmt_post_end_gas_obs] >>
          irule assign_local_marked_exec >>
          (conj_tac >- (qexists `lctx` >> simp[])) >>
          irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
            |> REWRITE_RULE [APPEND_NIL]) >>
          qexistsl [`es_end with gas_obs := []`, `t`, `v`] >> simp[] >>
          irule gas_marked_exec_end_gas_obs >> simp[]) >>
      Cases_on `res` >- gvs[expr_exit_def] >>
      simp[gas_summary_at_def] >>
      qexistsl [`INR y`, `es_end`, `r`] >> simp[] >> conj_tac
      >- (irule assign_local_marked_exec >>
          (conj_tac >- (qexists `lctx` >> simp[])) >>
          irule gas_marked_exec_bind_exception >> simp[]) >>
      disj2_tac >> gen_tac >> simp[stmt_exit_def] >>
      metis_tac[expr_exit_INR_type]) >>
  qexists `marks` >> disj2_tac >>
  qexistsl [`err`, `ee`, `leaf`, `finish'`] >>
  irule assign_local_exempt >> simp[]
QED
