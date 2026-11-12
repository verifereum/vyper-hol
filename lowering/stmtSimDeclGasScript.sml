(* Counted sequencing boundaries for declarations. *)
Theory stmtSimDeclGas
Ancestors
  stmtSimDeclSource gasExemptCert gasExemptOrigin gasNormalPrefix gasSummary
  gasSummaryCompose fragGasMode loweringPosts exprLoweringProps vyperState
Libs
  monadsyntax





Theorem gas_marked_return_prefix[local]:
  gas_marked_path F ctx func s0 0 (OK s1) ==>
  gas_marked_exec F (ctx,func) (return ()) (es,s0) [] (INL ()) es (OK s1)
Proof
  simp[gas_marked_exec_def, return_def]
QED

Theorem gas_exempt_cert_zero_prefix:
  gas_marked_path F ctx func s0 0 (OK s1) /\
  gas_exempt_cert F tops (ctx,func) source (es,s1) marks (err,ee) (leaf,finish_state) ==>
  gas_exempt_cert F tops (ctx,func) source (es,s0) marks (err,ee) (leaf,finish_state)
Proof
  strip_tac >> drule gas_marked_return_prefix >>
  disch_then (qspec_then `es` assume_tac) >>
  drule gas_exempt_cert_start_gas_obs >>
  disch_then (qspec_then `[]` assume_tac) >> fs[] >>
  drule gas_exempt_cert_bind_unit >>
  disch_then (qspecl_then [`tops`, `\u. source`] mp_tac) >>
  simp[bind_return] >> disch_then irule >> simp[]
QED

Theorem gas_marked_exec_zero_prefix:
  gas_marked_path F ctx func s0 0 (OK s1) /\
  gas_marked_exec F (ctx,func) source (es,s1) marks res ee r ==>
  gas_marked_exec F (ctx,func) source (es,s0) marks res ee r
Proof
  strip_tac >>
  `s1.vs_gas_readings = s0.vs_gas_readings` by
    (drule gas_marked_path_ok_suffix >> simp[]) >>
  fs[gas_marked_exec_def] >>
  metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES]
QED

Theorem annassign_exempt_cert:
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  gas_exempt_cert F tops (ctx,func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (es,s) marks (err,ee) (leaf,finish_state) ==>
  gas_exempt_cert F tops (ctx,func) (eval_stmt cx (AnnAssign id typ e))
    (es,s) marks (err,ee) (leaf,finish_state)
Proof
  strip_tac >> drule eval_annassign_action >>
  disch_then (qspecl_then [`id`, `e`] SUBST1_TAC) >>
  irule gas_exempt_cert_error_value >> simp[]
QED
