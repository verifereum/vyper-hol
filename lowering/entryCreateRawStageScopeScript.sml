(* Normal return from the RawCreate bytecode child. The VV witness, not a
   second evaluation, supplies the source value and all-horizon replay. *)
Theory entryCreateRawStageScope
Ancestors
  entryCreateFocusSpec entryCreateScopedBind bodyFullCreateHeld
  exprSimAggregateSource exprSimMemorySource gasStorage vyperStorageFootprint
  vyperInterpreter vyperState

Theorem raw_create_scoped_bytecode_read[local]:
  storage_trace_domain cx st0 ee.storage_trace /\
  (!tail. eval_expr cx code (es with gas_obs := gs ++ tail) =
    (res,ee with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    create_operand_vv_post (DF,lo,d,ctx,func) ce cx code
      (es,sa,a,s,vv,G,tn) H res ee G1 tn1 t) ==>
  ?raw v. res = INL raw /\ read_result cx raw ee = (INL v,ee) /\
    (!tail. bind (eval_expr cx code) (read_result cx)
      (es with gas_obs := gs ++ tail) = (INL v,ee with gas_obs := tail))
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
    (drule_then (strip_assume_tac o REWRITE_RULE [create_operand_vv_post_def])) >>
  drule vv_post_materialises >> strip_tac >>
  qexistsl_tac [`tv`,`v`] >> simp[Once bind_def] >>
  metis_tac[read_result_gas_obs]
QED
