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
