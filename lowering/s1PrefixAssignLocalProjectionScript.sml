(* The local write preserves the RHS request witness. *)
Theory s1PrefixAssignLocalProjection
Ancestors
  s1PrefixDefs stmtSimAssignSource tuplePlaceStep vyperState

Theorem body_assign_local_prefix_of_rhs:
  gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
    (stmt_res_ok lctx) es /\
  gas_prefix_full (DF,lo,explicit,ctx,func,PG)
      cx st0 (bind (eval_expr cx e) (read_result cx))
      (es,s,G,tn) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG)
      cx st0 (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
      (es,s,G,tn)
Proof
  strip_tac >> drule assign_local_admissible_run >> strip_tac >>
  qpat_x_assum `gas_prefix_full _ _ _ _ _`
    (qx_choose_then `marks` (CONJUNCTS_THEN ASSUME_TAC) o
     REWRITE_RULE[gas_prefix_full_def]) >>
  rewrite_tac[gas_prefix_full_def] >> qexists_tac `marks` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!tail res ee obs_pre rq outcome sfx H. _ ==> request_site _ _ _ _ _ _ _`
    (qspec_then `tail` irule) >>
  qabbrev_tac `gs = gas_explicit marks s.vs_gas_readings ++ tail` >>
  Cases_on `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs)` >>
  rename1 `_ = (rhs,mid)` >>
  `ee.storage_trace = mid.storage_trace` by
    (qpat_x_assum `bind _ (write_place _ _) _ = _` mp_tac >>
     Cases_on `rhs` >> simp[Once bind_def] >>
     metis_tac[write_place_storage_trace]) >>
  simp[] >> qexistsl [`mid`, `rhs`, `sfx`, `tail`] >>
  fs[Abbr `gs`]
QED
