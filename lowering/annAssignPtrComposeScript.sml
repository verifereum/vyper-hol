(* Source action composition retains the actual counted pointer endpoints. *)
Theory annAssignPtrCompose
Ancestors
 bodyPtrDefs stmtSimDeclCompose stmtSimDeclSource gasSummaryComposePtr
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
 !D ctx func PG cx id typ tyv e es salloc Ga tna Q P RetQ.
 evaluate_type (get_tenv cx) typ = SOME tyv /\
 gas_outcome_ptr D (cx_tops cx) (ctx,func) PG
   (bind (eval_expr cx e) (read_result cx)) (es,salloc,Ga,tna) Q
   (\res ee gt r. expr_exit res r) /\
 (!res ee G tn t. Q res ee G tn t ==> ?v. res = INL v) /\
 (!marks v ee G tn t.
   gas_marked_exec_ptr D (ctx,func) PG
     (bind (eval_expr cx e) (read_result cx)) (es,salloc,Ga,tna)
     marks (INL v) ee G tn (OK t) /\
   Q (INL v) (ee with gas_obs := []) G tn t ==>
   ?ff u Gf tnf.
     gas_marked_exec_ptr D (ctx,func) PG (new_variable id tyv v)
       (ee with gas_obs := [],t,G,tn) [] (INL ()) ff Gf tnf (OK u) /\
     P (INL ()) (ff with gas_obs := []) Gf tnf u) ==>
 gas_outcome_ptr D (cx_tops cx) (ctx,func) PG
   (eval_stmt cx (AnnAssign id typ e)) (es,salloc,Ga,tna) P
   (\res ee gt r. !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r)
Proof
 rpt gen_tac >> strip_tac >> rewrite_tac[gas_outcome_ptr_def] >>
 qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _`
   (mp_tac o REWRITE_RULE [gas_outcome_ptr_def]) >> strip_tac
 >- (qexists `marks` >> disj1_tac >>
     drule eval_annassign_action >>
     disch_then (qspecl_then [`id`,`e`] SUBST1_TAC) >>
     qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_summary_ptr_at_marked]) >> strip_tac
     >- suspend "normal"
     >> suspend "exception") >>
 suspend "exempt"
QED

Resume annassign_rhs_outcome_ptr[normal]:
 gvs[] >>
 `?v. res = INL v` by metis_tac[] >> gvs[] >>
 qpat_x_assum `!marks v ee G tn t. _` (drule_then mp_tac) >>
 (impl_tac >- simp[]) >> strip_tac >>
 rewrite_tac[gas_summary_ptr_at_marked] >>
 qexistsl [`INL ()`,`ff`,`Gf`,`tnf`,`OK u`] >> simp[] >>
 irule (Q.INST [`right` |-> `[]`] gas_marked_exec_ptr_bind_normal
   |> REWRITE_RULE [APPEND_NIL]) >>
 goal_assum (drule_at Any) >> simp[]
QED

Resume annassign_rhs_outcome_ptr[exception]:
 Cases_on `res` >- gvs[expr_exit_def] >>
 rewrite_tac[gas_summary_ptr_at_marked] >>
 qexistsl [`INR y`,`es_end`,`G`,`tn`,`r`] >> simp[] >> conj_tac
 >- (irule gas_marked_exec_ptr_bind_exception >> simp[]) >>
 fs[stmt_exit_ptr_def] >> disj2_tac >> gen_tac >> disj1_tac >>
 metis_tac[expr_exit_INR_type]
QED

Resume annassign_rhs_outcome_ptr[exempt]:
 qexists `marks` >> disj2_tac >>
 qexistsl [`err`,`ee`,`leaf`,`finish'`] >>
 drule eval_annassign_action >>
 disch_then (qspecl_then [`id`,`e`] SUBST1_TAC) >>
 rewrite_tac[ignore_bind_def] >> once_rewrite_tac[bind_assoc] >>
 irule gas_exempt_cert_error_value >> simp[ignore_bind_def]
QED

Finalise annassign_rhs_outcome_ptr

(* Only old-variable frames are rebased; memory ghosts remain at the endpoint. *)
Theorem annassign_outcome_entry_prefix_ptr:
 gas_path_ptr D 0 ctx func PG G0 tn0 s0 n Ga tna (OK salloc) /\
 (!x. not_fresh_at sa0 x ==> not_fresh_at sa x /\
    FLOOKUP Ga x = FLOOKUP G0 x /\
    op_taint tna (Var x) = op_taint tn0 (Var x)) /\
 (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
    lookup_var x salloc = SOME w) /\
 gas_outcome_ptr D tops (ctx,func) PG source (es,salloc,Ga,tna)
   (\res ee G tn t. ?cenv''.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel ctx func cenv'' cx ee t /\
      ghost_inv d cenv'' cx ee G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x salloc = SOME w ==>
         lookup_var x t = SOME w) /\
      (!x. not_fresh_at sa x ==>
         FLOOKUP G x = FLOOKUP Ga x /\
         op_taint tn (Var x) = op_taint tna (Var x))) R ==>
 gas_outcome_ptr D tops (ctx,func) PG source (es,s0,G0,tn0)
   (\res ee G tn t. ?cenv''.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel ctx func cenv'' cx ee t /\
      ghost_inv d cenv'' cx ee G tn t /\
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
 !D ctx func PG cx id typ tyv e es salloc Ga tna Q P RetQ.
 evaluate_type (get_tenv cx) typ = SOME tyv /\
 (!gs tv ee. eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) ==>
    ?v. tv = Value v) /\
 gas_outcome_ptr D (cx_tops cx) (ctx,func) PG
   (eval_expr cx e) (es,salloc,Ga,tna) Q
   (\res ee gt r. expr_exit res r) /\
 (!res ee G tn t. Q res ee G tn t ==> ?tv. res = INL tv) /\
 (!marks v ee G tn t.
   gas_marked_exec_ptr D (ctx,func) PG (eval_expr cx e)
     (es,salloc,Ga,tna) marks (INL (Value v)) ee G tn (OK t) /\
   Q (INL (Value v)) (ee with gas_obs := []) G tn t ==>
   ?ff u Gf tnf.
     gas_marked_exec_ptr D (ctx,func) PG (new_variable id tyv v)
       (ee with gas_obs := [],t,G,tn) [] (INL ()) ff Gf tnf (OK u) /\
     P (INL ()) (ff with gas_obs := []) Gf tnf u) ==>
 gas_outcome_ptr D (cx_tops cx) (ctx,func) PG
   (eval_stmt cx (AnnAssign id typ e)) (es,salloc,Ga,tna) P
   (\res ee gt r. !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r)
Proof
 rpt gen_tac >> strip_tac >> rewrite_tac[gas_outcome_ptr_def] >>
 drule eval_annassign_action >>
 disch_then (qspecl_then [`id`,`e`] SUBST1_TAC) >>
 once_rewrite_tac[bind_assoc] >>
 qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _`
   (mp_tac o REWRITE_RULE [gas_outcome_ptr_def]) >> strip_tac
 >- (qexists `marks` >> disj1_tac >>
     qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_summary_ptr_at_marked]) >> strip_tac
     >- suspend "raw_normal" >> suspend "raw_exception") >>
 qexists `marks` >> disj2_tac >>
 qexistsl [`err`,`ee`,`leaf`,`finish'`] >>
 rewrite_tac[ignore_bind_def] >> once_rewrite_tac[bind_assoc] >>
 irule gas_exempt_cert_error_result >> simp[ignore_bind_def]
QED

Resume annassign_raw_rhs_outcome_ptr[raw_normal]:
 gvs[] >>
 `?tv. res = INL tv` by metis_tac[] >> gvs[] >>
 `?v. tv = Value v` by
   (qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [gas_marked_exec_ptr_def]) >> strip_tac >>
    first_x_assum (qspec_then `[]` assume_tac) >> metis_tac[]) >>
 gvs[] >>
 qpat_x_assum `!marks v ee G tn t. _` (drule_then mp_tac) >>
 (impl_tac >- simp[]) >> strip_tac >>
 rewrite_tac[gas_summary_ptr_at_marked] >>
 qexistsl [`INL ()`,`ff`,`Gf`,`tnf`,`OK u`] >> simp[] >>
 irule (Q.INST [`right` |-> `[]`] gas_marked_exec_ptr_bind_normal
   |> REWRITE_RULE [APPEND_NIL]) >>
 goal_assum (drule_at Any) >>
 simp[read_result_def, bind_return]
QED

Resume annassign_raw_rhs_outcome_ptr[raw_exception]:
 Cases_on `res` >- gvs[expr_exit_def] >>
 rewrite_tac[gas_summary_ptr_at_marked] >>
 qexistsl [`INR y`,`es_end`,`G`,`tn`,`r`] >> simp[] >> conj_tac
 >- (irule gas_marked_exec_ptr_bind_exception >> simp[]) >>
 fs[stmt_exit_ptr_def] >> disj2_tac >> gen_tac >> disj1_tac >>
 metis_tac[expr_exit_INR_type]
QED

Finalise annassign_raw_rhs_outcome_ptr
