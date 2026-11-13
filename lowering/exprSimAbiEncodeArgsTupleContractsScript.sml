Theory exprSimAbiEncodeArgsTupleContracts
Ancestors
  exprSimAbiEncodeArgsTupleProbe exprSimDefs exprSimHypsDefs
  loweringPosts exprLowering compileEnv finite_map

Theorem tuple_post_value_type:
  ce.ce_func_return_type (nsid_to_string (NONE,"f")) = tuple_narrow ==>
  post_value_type ce tuple_call = tuple_narrow
Proof
  simp[tuple_call_def, tuple_wide_def, post_value_type_def,
       lowered_value_type_def, is_word_type_def, is_bytestring_type_def]
QED

Theorem tuple_expr_post_value:
  ce.ce_func_return_type (nsid_to_string (NONE,"f")) = tuple_narrow /\
  expr_post ctx func ce cx tuple_call es sa sb s0 ee v op t ==>
  expr_val_rel cx tuple_narrow v op t
Proof
  strip_tac >> drule tuple_post_value_type >> strip_tac >>
  gvs[expr_post_def]
QED

Theorem tuple_joint_contracts:
  exprs_case F ctx func ce cx [tuple_call] <=>
  (!env ty es. expr_body_pre ce cx env tuple_call es ==>
    !sa sb op s0.
      lower_value compile_expr ce ty tuple_call sa = (op,sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved ce sa /\
      gas_admissible (bind (eval_expr cx tuple_call) (read_result cx)) expr_res_ok es /\
      stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome F (cx_tops cx) (ctx,func)
        (bind (eval_expr cx tuple_call) (read_result cx)) (es,s0)
        (\res ee t. ?v. res = INL v /\
          expr_post ctx func ce cx tuple_call es sa sb s0 ee v op t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts)
        (\res ee r. expr_exit res r)) /\
  (!env ty es. expr_body_pre ce cx env tuple_call es ==>
    !sa sb vv s0.
      compile_expr ce ty tuple_call sa = (vv,sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved ce sa /\
      gas_admissible (eval_expr cx tuple_call) expr_vv_res_ok es /\
      stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx tuple_call) (es,s0)
        (\res ee t. ?tv. res = INL tv /\
          vv_post ctx func ce cx tuple_call es sa sb s0 ee tv vv t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts)
        (\res ee r. expr_exit res r))
Proof
  simp[tuple_singleton_cases, expr_sim_def, expr_vv_sim_def]
QED

Theorem tuple_vv_post_interface:
  ce.ce_func_return_type (nsid_to_string (NONE,"f")) = tuple_narrow ==>
  (vv_post ctx func ce cx tuple_call es sa sb s0 ee tv vv t <=>
    stmt_state_rel ctx func ce cx ee t /\
    vv_holds ce cx tuple_narrow tv vv ee t /\
    vv_at ce cx tuple_narrow sa sb ee tv vv t /\
    vv_own ce cx tuple_narrow sa sb ee tv vv t /\
    (~expr_has_effect tuple_call ==> vv_storage_live cx vv ee t) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    (!aid off sz.
       FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
       (!n b sz'. local_region ce es.scopes s0 n b sz' ==>
                  off + sz <= b \/ b + sz' <= off) ==>
       mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
    locals_kept ce es ee s0 t)
Proof
  strip_tac >> drule tuple_post_value_type >> strip_tac >>
  simp[vv_post_def, tuple_call_def, vyperASTTheory.expr_type_def,
       tuple_narrow_def, tuple_wide_def]
QED

Theorem tuple_stack_success_interface:
  ce.ce_func_return_type (nsid_to_string (NONE,"f")) = tuple_narrow /\
  vv_post ctx func ce cx tuple_call es sa sb s0 ee tv (StackValue rt op) t ==>
  ?v. read_result cx tv ee = (INL v,ee) /\
      expr_val_rel cx tuple_narrow v op t /\
      expr_val_at ce cx tuple_narrow sa sb ee v op t /\
      expr_val_own ce cx tuple_narrow sa sb ee v op t
Proof
  strip_tac >> drule tuple_vv_post_interface >> strip_tac >>
  gvs[vv_holds_def, vv_at_def, vv_own_def] >> metis_tac[]
QED
