(* Prepare the selected arm at the completed condition's actual midpoint. *)
Theory entryCreateIfExpMidpoint
Ancestors
  entryCreateFocusSpec entryCreateCompletedCut exprSimIfExp
  exprSimFullBundleProps vyperStorageFootprint fragGasOriginPtr fragGasOrigin
  gasSummary venomState vyperState

Theorem ifexp_condition_selected_callback:
  gas_admissible (eval_expr cx (IfExp t c a b)) expr_vv_res_ok es /\
  (!marks sel mid G1 tn1 z.
    (!tail. vyperState$bind (eval_expr cx c) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL (BoolV sel),mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    create_operand_at sc z /\
    create_operand_full_scope sa sc E ctx func s0 marks (OK z) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      expr_sim_full_post (DF,lo,d,ctx,func) ce cx c (es,sa,sc,s0,op,G0,tn0)
        H (INL (BoolV sel) : value + exception) (mid with gas_obs := []) G1 tn1 z /\
      gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (s0,G0,tn0) marks (OK z,G1,tn1)) /\
    gas_marked_exec T (ctx,func) (vyperState$bind (eval_expr cx c) (read_result cx))
      (es,s0) marks (INL (BoolV sel)) mid (OK z) /\
    gas_admissible (vyperState$bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
      expr_vv_res_ok (mid with gas_obs := []) ==>
    scoped_operand_outcome (DF,lo,E,ctx,func,PG) (cx_tops cx) cx st0 sc sb
      (vyperState$bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
      (mid with gas_obs := [],z,G1,tn1) Q R) ==>
  !marks res mid G1 tn1 z.
    (!tail. vyperState$bind (eval_expr cx c) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (res,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    create_operand_at sc z /\
    create_operand_full_scope sa sc E ctx func s0 marks (OK z) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      (expr_sim_full_post (DF,lo,d,ctx,func) ce cx c (es,sa,sc,s0,op,G0,tn0)
        H res mid G1 tn1 z /\ mid.gas_obs = []) /\
      gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (s0,G0,tn0) marks (OK z,G1,tn1)) ==>
    ?v. res = INL v /\
      scoped_operand_outcome (DF,lo,E,ctx,func,PG) (cx_tops cx) cx st0 sc sb
        (if v = BoolV T then vyperState$bind (eval_expr cx a) (conditional_result cx)
         else if v = BoolV F then vyperState$bind (eval_expr cx b) (conditional_result cx)
         else raise (Error (TypeError "not BoolV"))) (mid,z,G1,tn1) Q R
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> (_ /\ _) /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `?v. res = INL v` by fs[expr_sim_full_post_def] >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  qpat_assum `!tail. vyperState$bind _ _ _ = _`
    (qspec_then `[]` (assume_tac o REWRITE_RULE [listTheory.APPEND_NIL])) >>
  gvs[] >> drule_all ifexp_root_condition_bool >> strip_tac >> gvs[] >>
  drule_all ifexp_root_branch_admissible >> strip_tac >>
  `gas_marked_exec T (ctx,func) (vyperState$bind (eval_expr cx c) (read_result cx))
      (es,s0) marks (INL (BoolV sel)) mid (OK z)` by
    (simp[gas_marked_exec_def] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ gas_origin_ptr_path _ _ _ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     drule gas_origin_ptr_path_projections >> metis_tac[gas_origin_path_erase]) >>
  `scoped_operand_outcome (DF,lo,E,ctx,func,PG) (cx_tops cx) cx st0 sc sb
      (vyperState$bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
      (mid with gas_obs := [],z,G1,tn1) Q R` by
    (qpat_assum `!marks sel mid G1 tn1 z. _ ==> scoped_operand_outcome _ _ _ _ _ _ _ _ _ _` irule >>
     fs[] >> qexists_tac `marks` >> fs[] >> metis_tac[]) >>
  Cases_on `sel` >> gs[]
QED
