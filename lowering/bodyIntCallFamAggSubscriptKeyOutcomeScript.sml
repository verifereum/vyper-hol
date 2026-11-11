(* Public forced-key sequencing with the joint mapping suffix post. *)
Theory bodyIntCallFamAggSubscriptKeyOutcome
Ancestors
  bodyIntCallFamAggSubscriptKeyLanding bodyIntCallJointContract
  exprSimSubscriptMap stmtSimForced gasOutcome gasSummary
  loweringPosts vyperState vyperInterpreter compileEnv venomState

Theorem intcall_mapping_key_outcome:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s0 /\
  (expr_body_pre ce fp.jc_cx env (Subscript ann obj idx) es \/
   expr_map_pre ce fp.jc_cx env (Subscript ann obj idx) es) /\
  place_type ce obj = MapPT kt vt /\
  (!tail. eval_expr fp.jc_cx obj (es with gas_obs := bs ++ tail) =
    (INL bres,em with gas_obs := tail)) /\
  intcall_expr_cont fp ce env es sa s0 em sm t /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
  (if is_bytestring_type kt then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  compile_mapping_subscript base_op hashed sp = (op,sb) /\
  fn_has_code sn sp fp.jc_func /\ fn_has_code sp sb fp.jc_func /\
  fn_inst_ids_distinct fp.jc_func /\
  (!x. key = Var x ==> not_fresh_at sn x) /\
  (!x. base_op = Var x ==> not_fresh_at sm x) /\
  (!lbl. base_op <> Label lbl) /\ eval_operand base_op t = SOME slot /\
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (bind (eval_expr fp.jc_cx idx) (read_result fp.jc_cx)) (em,t)
    (\res en s. ?kv. res = INL kv /\
      expr_post fp.jc_ctx fp.jc_func ce fp.jc_cx idx em sm sn t en kv key s /\
      intcall_expr_cont fp ce env em sm t en sn s)
    (\res en r. expr_exit res r) ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (bind (bind (eval_expr fp.jc_cx idx) (read_result fp.jc_cx))
      (\kv. select_result fp.jc_cx (expr_type obj)
        (HashMapRef tr slot kt vt) (ValueSubscript kv))) (em,t)
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
  irule forced_then_outcome >>
  conj_tac >- metis_tac[stmtSimPropsTheory.expr_exit_INR_type] >>
  qexists_tac `\kv en s.
    expr_post fp.jc_ctx fp.jc_func ce fp.jc_cx idx em sm sn t en kv key s /\
    intcall_expr_cont fp ce env em sm t en sn s` >>
  simp[] >>
  rpt gen_tac >> strip_tac >>
  `eval_expr fp.jc_cx obj (es with gas_obs := bs ++ gs) =
    (INL bres,em with gas_obs := gs)` by simp[] >>
  drule_all intcall_mapping_key_landing >>
  disch_then (qspec_then `tr` strip_assume_tac) >>
  qexistsl_tac [`INL selected`, `ee`, `OK out`] >> simp[] >>
  qexists_tac `v` >> simp[] >>
  `ee with gas_obs := [] = ee` by
    (Cases_on `ee` >>
     gvs[vyperStateTheory.recordtype_evaluation_state_seldef_gas_obs_fupd_def]) >> simp[]
QED
