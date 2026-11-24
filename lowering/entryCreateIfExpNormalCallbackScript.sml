(* Normalize only the source component of the completed test callback. *)
Theory entryCreateIfExpNormalCallback
Ancestors
  entryCreateFocusSpec exprSimFullBundleProps fragGasOriginPtr gasSummary
  gasContext vyperStorageFootprint venomState vyperState

Theorem ifexp_selected_callback_normalize:
  let source = vyperState$bind (eval_expr cx c) (read_result cx);
      arm = (\sel. vyperState$bind (eval_expr cx (if sel then a else b))
                   (conditional_result cx));
      P = expr_sim_full_post (DF,lo,d,ctx,f) ce cx c (es,sa,sc,s0,cop,G0,tn0)
  in
  (!marks sel n G1 tn1 z.
    (!tail. source (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL (BoolV sel),n with gas_obs := tail)) /\
    storage_trace_domain cx st0 n.storage_trace /\ n.gas_obs = [] /\
    create_operand_at sc z /\
    create_operand_full_scope sa sc E ctx f s0 marks (OK z) /\
    (!H. valid_horizon cx st0 H n.storage_trace ==>
      P H (INL (BoolV sel)) n G1 tn1 z /\
      gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (s0,G0,tn0) marks (OK z,G1,tn1)) /\
    gas_marked_exec T (ctx,f) source (es,s0) marks (INL (BoolV sel)) n (OK z) /\
    gas_admissible (arm sel) expr_vv_res_ok n ==>
    scoped_operand_outcome (DF,lo,E,ctx,f,PG) (cx_tops cx) cx st0 sc sb
      (arm sel) (n,z,G1,tn1) Q R) ==>
  !marks sel mid G1 tn1 z.
    (!tail. source (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL (BoolV sel),mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    create_operand_at sc z /\
    create_operand_full_scope sa sc E ctx f s0 marks (OK z) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      P H (INL (BoolV sel)) (mid with gas_obs := []) G1 tn1 z /\
      gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (s0,G0,tn0) marks (OK z,G1,tn1)) /\
    gas_marked_exec T (ctx,f) source (es,s0) marks (INL (BoolV sel)) mid (OK z) /\
    gas_admissible (arm sel) expr_vv_res_ok mid ==>
    scoped_operand_outcome (DF,lo,E,ctx,f,PG) (cx_tops cx) cx st0 sc sb
      (arm sel) (mid with gas_obs := [],z,G1,tn1) Q R
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!marks sel n G1 tn1 z. _ ==> scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`
    irule >>
  simp[] >> qexists `marks` >> simp[] >>
  simp[gas_marked_exec_def] >> fs[gas_marked_exec_def]
QED
