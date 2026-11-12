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

(* Rewrite a gas_bad_storage_at goal on the assignment statement to one on
   its bind form, using the admissible run equation at every gas_obs. *)
val assign_bad_storage_tac =
  drule assign_local_admissible_run >>
  disch_then (fn th =>
    PURE_REWRITE_TAC [gasStorageTheory.gas_bad_storage_at_def, th]) >>
  PURE_REWRITE_TAC [GSYM gasStorageTheory.gas_bad_storage_at_def];

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
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0) /\
  local_ptrs_reserved cenv sa /\
  gas_outcome F (cx_tops cx) (ctx,func) cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s0)
    (\H res ee t. ?v. res = INL v /\
      expr_post H ctx func cenv cx e es sa sb s0 ee v op t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\H res ee r. expr_exit res r) ==>
  gas_outcome F (cx_tops cx) (ctx,func) cx st0
    (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) (es,s0)
    (\H. stmt_post H ctx func cx lctx cenv cenv sa sf es s0)
    (\H res ee r. !tail. stmt_exit (RetQ H) (ee with gas_obs := tail) res r)
Proof
  strip_tac >> rewrite_tac[gas_outcome_def] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_outcome_def]) >> strip_tac
  >- (qexists `marks` >> disj1_tac >> assign_bad_storage_tac >>
      irule gasStorageTheory.gas_bad_storage_at_bind_left >>
      simp[vyperStorageTraceTheory.storage_trace_frame_write_place])
  >- (qexists `marks` >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [gas_summary_at_def]) >> BETA_TAC >> strip_tac
      >- (reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
          >- (disj1_tac >> assign_bad_storage_tac >>
              irule gasStorageTheory.gas_bad_storage_at_bind_left >>
              simp[vyperStorageTraceTheory.storage_trace_frame_write_place] >>
              metis_tac[gasStorageTheory.gas_bad_storage_at_counted_prefix]) >>
          `?H0. valid_horizon cx st0 H0 es_end.storage_trace` by
            metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
          gvs[] >>
          `?v. res = INL v` by metis_tac[] >> gvs[] >>
          `!H. valid_horizon cx st0 H es_end.storage_trace ==>
               expr_post H ctx func cenv cx e es sa sb s0
                 (es_end with gas_obs := []) v op t` by metis_tac[] >>
          `t.vs_current_bb = sb.cs_current_bb /\
           t.vs_inst_idx = LENGTH sb.cs_current_insts` by metis_tac[] >>
          qspecl_then [`ctx`, `func`, `cenv`, `cx`, `st0`, `lctx`, `id`, `e`, `es`,
            `etv`, `sa`, `sb`, `sf`, `s0`, `marks`, `v`, `es_end`, `t`, `op`, `p`, `sz`]
            mp_tac assign_local_normal_continuation >>
          impl_tac >- (simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
                       qexists `H0` >> first_assum ACCEPT_TAC) >>
          strip_tac >>
          disj2_tac >> disj1_tac >>
          simp[gas_summary_at_def] >>
          qexistsl [`INL ()`, `ff`, `OK u`] >> simp[stmt_post_end_gas_obs] >>
          irule assign_local_marked_exec >>
          (conj_tac >- (qexists `lctx` >> simp[])) >>
          irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
            |> REWRITE_RULE [APPEND_NIL]) >>
          qexistsl [`es_end with gas_obs := []`, `t`, `v`] >> simp[] >>
          irule gas_marked_exec_end_gas_obs >> simp[]) >>
      reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
      >- (disj1_tac >> assign_bad_storage_tac >>
              irule gasStorageTheory.gas_bad_storage_at_bind_left >>
          simp[vyperStorageTraceTheory.storage_trace_frame_write_place] >>
          metis_tac[gasStorageTheory.gas_bad_storage_at_counted_prefix]) >>
      `?H0. valid_horizon cx st0 H0 es_end.storage_trace` by
        metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
      `expr_exit res r` by (gs[] >> metis_tac[]) >>
      Cases_on `res` >- gvs[expr_exit_def] >>
      disj2_tac >> disj1_tac >>
      simp[gas_summary_at_def] >>
      qexistsl [`INR y`, `es_end`, `r`] >> simp[] >> conj_tac
      >- (irule assign_local_marked_exec >>
          (conj_tac >- (qexists `lctx` >> simp[])) >>
          irule gas_marked_exec_bind_exception >> simp[]) >>
      rpt strip_tac >> simp[stmt_exit_def] >>
      metis_tac[expr_exit_INR_type]) >>
  qexists `marks` >> disj2_tac >> disj2_tac >>
  qexistsl [`err`, `ee`, `leaf`, `finish'`] >>
  irule assign_local_exempt >> simp[]
QED
