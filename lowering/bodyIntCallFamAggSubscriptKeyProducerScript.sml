(* Apply the key's joint producer at a successful mapping-base endpoint. *)
Theory bodyIntCallFamAggSubscriptKeyProducer
Ancestors
  bodyIntCallFamAggSubscriptForcedOutcome bodyIntCallFamAggSubscriptKeyOutcome
  bodyIntCallJointContract exprSimSubscriptMap exprOperandVar gasSummary
  loweringPosts compileEnv

Theorem intcall_mapping_key_producer:
  intcall_forced_producer fp idx /\
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  intcall_expr_res fp ce env es sa s0 /\
  (expr_body_pre ce fp.jc_cx env (Subscript ann obj idx) es \/
   expr_map_pre ce fp.jc_cx env (Subscript ann obj idx) es) /\
  place_type ce obj = MapPT kt vt /\
  supportedExprs$supported_expr fp.jc_tops idx /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr idx) /\
  gas_admissible (eval_expr fp.jc_cx (Subscript ann obj idx)) A es /\
  (!ex. A (INR ex) ==> expr_map_res_ok (INR ex)) /\
  gas_marked_exec F (fp.jc_ctx,fp.jc_func) (eval_expr fp.jc_cx obj)
    (es,s0) marks (INL (HashMapRef tr slot kt vt)) mid (OK t) /\
  intcall_expr_cont fp ce env es sa s0 (mid with gas_obs := []) sm t /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
  lower_value compile_expr ce (expr_type idx) idx sm = (key,sn) /\
  (if is_bytestring_type kt then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  compile_mapping_subscript base_op hashed sp = (op,sb) /\
  fn_has_code sm sn fp.jc_func /\ fn_has_code sn sp fp.jc_func /\
  fn_has_code sp sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  (!x. base_op = Var x ==> not_fresh_at sm x) /\
  (!lbl. base_op <> Label lbl) /\ eval_operand base_op t = SOME slot ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (bind (bind (eval_expr fp.jc_cx idx) (read_result fp.jc_cx))
      (\kv. select_result fp.jc_cx (expr_type obj)
        (HashMapRef tr slot kt vt) (ValueSubscript kv)))
    (mid with gas_obs := [],t)
    (\res en out. ?kv selected.
      res = INL selected /\
      select_result fp.jc_cx (expr_type obj) (HashMapRef tr slot kt vt)
        (ValueSubscript kv) en = (INL selected,en) /\
      eval_operand op out = SOME (hashmap_slot slot (encode_hashmap_key kt kv)) /\
      (!x. op = Var x ==> not_fresh_at sb x) /\
      intcall_expr_cont fp ce env es sa s0 en sb out)
    (\res en r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre ce fp.jc_cx env idx (mid with gas_obs := [])` by
    (drule_all mapping_subscript_marked_index_pre >> simp[]) >>
  `gas_admissible (bind (eval_expr fp.jc_cx idx) (read_result fp.jc_cx))
     expr_res_ok (mid with gas_obs := [])` by
    (irule subscript_result_index_admissible >>
     goal_assum (drule_at Any) >> qexistsl_tac [`A`, `ann`] >> simp[]) >>
  `intcall_expr_res fp ce env (mid with gas_obs := []) sm t /\
   ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
   t.vs_inst_idx = LENGTH sm.cs_current_insts` by
    fs[intcall_expr_cont_def] >>
  `!x. key = Var x ==> not_fresh_at sn x` by
    (drule compile_lower_value_var >>
     fs[intcall_expr_res_def]) >>
  drule_all intcall_forced_post_outcome >> strip_tac >>
  irule intcall_mapping_key_outcome >>
  goal_assum (drule_at Any) >> simp[] >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def] >> metis_tac[]
QED
