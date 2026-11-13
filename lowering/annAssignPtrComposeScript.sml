(* Source action composition retains the actual counted pointer endpoints. *)
Theory annAssignPtrCompose
Ancestors
 bodyPtrDefs stmtSimDeclCompose stmtSimDeclSource gasSummaryComposePtrAll gasSummaryComposePtr
 fragGasPathPtr gasExemptCert vyperInterpreter vyperState venomState
 exprSimDefs gasSummaryCompose gasSummary gasOutcome list stmtSimProps
Libs monadsyntax

Theorem annassign_marked_end_gas_obs_ptr:
 gas_marked_exec_ptr D (ctx,func) PG source (es,s,G,tn) marks res ee Gf tnf r ==>
 gas_marked_exec_ptr D (ctx,func) PG source (es,s,G,tn) marks res
   (ee with gas_obs := gs) Gf tnf r
Proof
 simp[gas_marked_exec_ptr_def]
QED

Theorem annassign_rhs_outcome_ptr:
 !D ctx func PG cx st0 id typ tyv e es salloc Ga tna RhsPost StmtPost RetQ.
 evaluate_type (get_tenv cx) typ = SOME tyv /\
 gas_outcome_ptr D (cx_tops cx) (ctx,func) PG cx st0
   (bind (eval_expr cx e) (read_result cx)) (es,salloc,Ga,tna) RhsPost
   (\H res ee gt r. expr_exit res r) /\
 (!H res ee G tn t. RhsPost H res ee G tn t ==> ?v. res = INL v) /\
 (!marks v ee G tn t.
   gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx)) (es,salloc)
     marks (INL (v)) ee (OK t) /\
   (?H. valid_horizon cx st0 H ee.storage_trace) /\
   (!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_marked_exec_ptr (D H) (ctx,func) PG
       (bind (eval_expr cx e) (read_result cx)) (es,salloc,Ga,tna) marks (INL (v)) ee G tn (OK t) /\
     RhsPost H (INL (v)) (ee with gas_obs := []) G tn t) ==>
   ?ff u Gf tnf.
     gas_marked_exec F (ctx,func) (new_variable id tyv v)
       (ee with gas_obs := [],t) [] (INL ()) ff (OK u) /\
     !H. valid_horizon cx st0 H ff.storage_trace ==>
       gas_marked_exec_ptr (D H) (ctx,func) PG (new_variable id tyv v)
         (ee with gas_obs := [],t,G,tn) [] (INL ()) ff Gf tnf (OK u) /\
       StmtPost H (INL ()) (ff with gas_obs := []) Gf tnf u) ==>
 gas_outcome_ptr D (cx_tops cx) (ctx,func) PG cx st0
   (eval_stmt cx (AnnAssign id typ e)) (es,salloc,Ga,tna) StmtPost
   (\H res ee gt r. !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r)
Proof
 rpt gen_tac >> strip_tac >>
 drule eval_annassign_action >> disch_then (qspecl_then [`id`, `e`] SUBST1_TAC) >>
 mp_tac (Q.INST
   [`tops` |-> `cx_tops cx`, `source` |-> `bind (eval_expr cx e) (read_result cx)`, `next` |-> `new_variable id tyv`,
    `s0` |-> `salloc`, `G0` |-> `Ga`, `tn0` |-> `tna`,
    `P` |-> `RhsPost`, `Q` |-> `StmtPost`, `E` |-> `\H res ee gt r. expr_exit res r`,
    `R` |-> `\H res ee gt r. !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r`]
   (INST_TYPE [alpha |-> ``:value``, beta |-> ``:unit``] gas_outcome_ptr_bind_all)) >>
 impl_tac
 >- (rpt conj_tac
     >- first_assum ACCEPT_TAC
     >- metis_tac[sumTheory.ISL]
     >- (rpt strip_tac >> Cases_on `res` >> gvs[expr_exit_def] >>
         simp[stmt_exit_ptr_def] >> metis_tac[expr_exit_INR_type])
     >- simp[vyperStorageTraceTheory.storage_trace_frame_new_variable,
              vyperStorageTraceTheory.storage_trace_frame_read_result,
              vyperStorageTraceTheory.storage_trace_frame_bind_all]
     >- (rpt gen_tac >> strip_tac >>
         qpat_x_assum `!marks v ee G tn t. _`
           (qspecl_then [`left`, `v`, `mid`, `G`, `tn`, `t`] mp_tac) >>
         impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
           conj_tac >- metis_tac[] >>
           rpt strip_tac >> first_x_assum drule >> strip_tac >>
           gvs[gas_marked_exec_ptr_def, gas_marked_exec_def,
               fragGasModeTheory.gas_marked_path_def]) >>
         strip_tac >> rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >>
         disj2_tac >> disj1_tac >> rewrite_tac[gas_summary_ptr_at_marked] >>
         qexistsl_tac [`INL ()`, `ff`, `Gf`, `tnf`, `OK u`] >>
         fs[gas_marked_exec_def])
     >- (rpt strip_tac >> simp[ignore_bind_def, bind_assoc] >>
         irule gas_exempt_cert_error_value >> simp[GSYM ignore_bind_def]) >>
     rpt strip_tac >> simp[ignore_bind_def, bind_assoc] >>
     irule gas_exempt_cert_bind_value >> goal_assum (drule_at Any) >>
     simp[GSYM ignore_bind_def]) >>
 simp[]
QED

(* Only old-variable frames are rebased; memory ghosts remain at the endpoint. *)
Theorem annassign_outcome_entry_prefix_ptr:
 (!H. valid_horizon cx st0 H es.storage_trace ==>
   gas_path_ptr (D H) 0 ctx func PG G0 tn0 s0 n Ga tna (OK salloc)) /\
 (!x. not_fresh_at sa0 x ==> not_fresh_at sa x /\
    FLOOKUP Ga x = FLOOKUP G0 x /\
    op_taint tna (Var x) = op_taint tn0 (Var x)) /\
 (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
    lookup_var x salloc = SOME w) /\
 gas_outcome_ptr D tops (ctx,func) PG cx st0 source (es,salloc,Ga,tna)
   (\H res ee G tn t. ?cenv''.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel H ctx func cenv'' cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      ghost_inv H d cenv'' cx ee G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x salloc = SOME w ==>
         lookup_var x t = SOME w) /\
      (!x. not_fresh_at sa x ==>
         FLOOKUP G x = FLOOKUP Ga x /\
         op_taint tn (Var x) = op_taint tna (Var x))) R ==>
 gas_outcome_ptr D tops (ctx,func) PG cx st0 source (es,s0,G0,tn0)
   (\H res ee G tn t. ?cenv''.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel H ctx func cenv'' cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      ghost_inv H d cenv'' cx ee G tn t /\
      (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
         lookup_var x t = SOME w) /\
      (!x. not_fresh_at sa0 x ==>
         FLOOKUP G x = FLOOKUP G0 x /\
         op_taint tn (Var x) = op_taint tn0 (Var x))) R
Proof
 strip_tac >> drule_all gas_outcome_ptr_prefix >> strip_tac >>
 irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
 simp[] >> rpt gen_tac >> strip_tac >>
 qexists `cenv''` >> simp[]
QED

Theorem annassign_raw_rhs_outcome_ptr:
 !D ctx func PG cx st0 id typ tyv e es salloc Ga tna RhsPost StmtPost RetQ.
 evaluate_type (get_tenv cx) typ = SOME tyv /\
 (!gs tv ee. eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) ==>
    ?v. tv = Value v) /\
 gas_outcome_ptr D (cx_tops cx) (ctx,func) PG cx st0
   (eval_expr cx e) (es,salloc,Ga,tna) RhsPost
   (\H res ee gt r. expr_exit res r) /\
 (!H res ee G tn t. RhsPost H res ee G tn t ==> ?v. res = INL v) /\
 (!marks v ee G tn t.
   gas_marked_exec F (ctx,func) (eval_expr cx e) (es,salloc)
     marks (INL (Value v)) ee (OK t) /\
   (?H. valid_horizon cx st0 H ee.storage_trace) /\
   (!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_marked_exec_ptr (D H) (ctx,func) PG
       (eval_expr cx e) (es,salloc,Ga,tna) marks (INL (Value v)) ee G tn (OK t) /\
     RhsPost H (INL (Value v)) (ee with gas_obs := []) G tn t) ==>
   ?ff u Gf tnf.
     gas_marked_exec F (ctx,func) (new_variable id tyv v)
       (ee with gas_obs := [],t) [] (INL ()) ff (OK u) /\
     !H. valid_horizon cx st0 H ff.storage_trace ==>
       gas_marked_exec_ptr (D H) (ctx,func) PG (new_variable id tyv v)
         (ee with gas_obs := [],t,G,tn) [] (INL ()) ff Gf tnf (OK u) /\
       StmtPost H (INL ()) (ff with gas_obs := []) Gf tnf u) ==>
 gas_outcome_ptr D (cx_tops cx) (ctx,func) PG cx st0
   (eval_stmt cx (AnnAssign id typ e)) (es,salloc,Ga,tna) StmtPost
   (\H res ee gt r. !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r)
Proof
 rpt gen_tac >> strip_tac >>
 drule eval_annassign_action >> disch_then (qspecl_then [`id`, `e`] SUBST1_TAC) >>
 once_rewrite_tac[bind_assoc] >>
 mp_tac (Q.INST
   [`tops` |-> `cx_tops cx`, `source` |-> `eval_expr cx e`, `next` |-> `\raw. bind (read_result cx raw) (new_variable id tyv)`,
    `s0` |-> `salloc`, `G0` |-> `Ga`, `tn0` |-> `tna`,
    `P` |-> `RhsPost`, `Q` |-> `StmtPost`, `E` |-> `\H res ee gt r. expr_exit res r`,
    `R` |-> `\H res ee gt r. !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r`]
   (INST_TYPE [alpha |-> ``:eval_result``, beta |-> ``:unit``] gas_outcome_ptr_bind_all)) >>
 impl_tac
 >- (rpt conj_tac
     >- first_assum ACCEPT_TAC
     >- metis_tac[sumTheory.ISL]
     >- (rpt strip_tac >> Cases_on `res` >> gvs[expr_exit_def] >>
         simp[stmt_exit_ptr_def] >> metis_tac[expr_exit_INR_type])
     >- simp[vyperStorageTraceTheory.storage_trace_frame_new_variable,
              vyperStorageTraceTheory.storage_trace_frame_read_result,
              vyperStorageTraceTheory.storage_trace_frame_bind_all]
     >- (rpt gen_tac >> strip_tac >>
         `?w. v = Value w` by
           (fs[gas_marked_exec_def] >>
            first_x_assum (qspec_then `[]` assume_tac) >> metis_tac[]) >> gvs[] >>
         simp[read_result_def, bind_return] >>
         qpat_x_assum `!marks v ee G tn t. _`
           (qspecl_then [`left`, `w`, `mid`, `G`, `tn`, `t`] mp_tac) >>
         impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
           conj_tac >- metis_tac[] >>
           rpt strip_tac >> first_x_assum drule >> strip_tac >>
           gvs[gas_marked_exec_ptr_def, gas_marked_exec_def,
               fragGasModeTheory.gas_marked_path_def]) >>
         strip_tac >> rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >>
         disj2_tac >> disj1_tac >> rewrite_tac[gas_summary_ptr_at_marked] >>
         qexistsl_tac [`INL ()`, `ff`, `Gf`, `tnf`, `OK u`] >>
         fs[gas_marked_exec_def])
     >- (rpt strip_tac >> simp[ignore_bind_def, bind_assoc] >>
         irule gas_exempt_cert_error_result >> simp[GSYM ignore_bind_def]) >>
     rpt strip_tac >> simp[ignore_bind_def, bind_assoc] >>
     irule gas_exempt_cert_bind_result >> goal_assum (drule_at Any) >>
     simp[GSYM ignore_bind_def]) >>
 simp[]
QED
