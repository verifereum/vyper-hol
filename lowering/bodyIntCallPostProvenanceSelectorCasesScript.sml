(* Noncapturing selector dispatch; Attribute uses the imported general boundary. *)
Theory bodyIntCallPostProvenanceSelectorCases
Ancestors
  bodyIntCallPostProvenanceAttributeSelector
  bodyIntCallPostProvenanceArraySelector bodyIntCallPostProvenanceOtherSelectors

Theorem intcall_noncapturing_subscript_outcome:
  (!env ty es sa sb vv s0.
    expr_body_pre ce cx env obj es /\ ~expr_has_effect obj /\
    compile_expr ce ty obj sa = (vv,sb) /\ fn_has_code sa sb func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
    gas_admissible (eval_expr cx obj) expr_vv_res_ok es /\
    stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx obj) (es,s0)
      (\res ee t. ?tv. res = INL tv /\
        vv_post ctx func ce cx obj es sa sb s0 ee tv vv t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        intcall_vv_provenance ce cx (expr_type obj) sa sb ee tv vv t)
      (\res ee r. expr_exit res r)) /\
  expr_sim_case F ctx func ce cx idx /\ expr_vv_case F ctx func ce cx idx /\
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (Subscript ann obj idx) es /\
  ~expr_has_effect (Subscript ann obj idx) /\
  ~subscript_reads_base cx obj idx /\ ~copies_subscript_base ce obj idx /\
  compile_expr ce ty (Subscript ann obj idx) sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  gas_admissible (eval_expr cx (Subscript ann obj idx)) expr_vv_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx (Subscript ann obj idx)) (es,s0)
    (\res ee t. ?tv. res = INL tv /\
      vv_post ctx func ce cx (Subscript ann obj idx) es sa sb s0 ee tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      intcall_vv_provenance ce cx ann sa sb ee tv vv t)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> Cases_on `?et bd. expr_type obj = ArrayT et bd`
  >- (pop_assum strip_assume_tac >>
      irule intcall_noncapturing_array_subscript_outcome >> simp[] >> metis_tac[]) >>
  irule intcall_noncapturing_other_subscript_outcome >> simp[] >> metis_tac[]
QED
