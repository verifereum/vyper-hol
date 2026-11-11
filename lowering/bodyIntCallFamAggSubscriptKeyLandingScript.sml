(* Normal mapping-key callback using raw source success, not key marks. *)
Theory bodyIntCallFamAggSubscriptKeyLanding
Ancestors
  bodyIntCallFamAggSubscriptHashTail bodyIntCallJointContract
  bodyIntCallJointAggCore exprSimSubscriptMap exprBopSimProps
  exprSimSource loweringPosts exprSimHypsDefs
  vyperEvalExprPreservesScopesDom vyperState vyperInterpreter
  compileEnv context venomState finite_map

Theorem intcall_mapping_key_landing:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s0 /\
  (expr_body_pre ce fp.jc_cx env (Subscript ann obj idx) es \/
   expr_map_pre ce fp.jc_cx env (Subscript ann obj idx) es) /\
  place_type ce obj = MapPT kt vt /\
  eval_expr fp.jc_cx obj (es with gas_obs := bs) =
    (INL bres,em with gas_obs := gs) /\
  bind (eval_expr fp.jc_cx idx) (read_result fp.jc_cx)
    (em with gas_obs := gs) = (INL kv,en) /\
  intcall_expr_cont fp ce env es sa s0 em sm t /\
  intcall_expr_cont fp ce env em sm t en sn s /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
  expr_post fp.jc_ctx fp.jc_func ce fp.jc_cx idx em sm sn t en kv key s /\
  (if is_bytestring_type kt then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  compile_mapping_subscript base_op hashed sp = (op,sb) /\
  fn_has_code sn sp fp.jc_func /\ fn_has_code sp sb fp.jc_func /\
  fn_inst_ids_distinct fp.jc_func /\
  (!x. key = Var x ==> not_fresh_at sn x) /\
  (!x. base_op = Var x ==> not_fresh_at sm x) /\
  (!lbl. base_op <> Label lbl) /\ eval_operand base_op t = SOME slot ==>
  ?selected out.
    (!tail. select_result fp.jc_cx (expr_type obj) (HashMapRef tr slot kt vt)
       (ValueSubscript kv) (en with gas_obs := tail) =
       (INL selected,en with gas_obs := tail)) /\
    gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK out) /\
    intcall_expr_cont fp ce env es sa s0 en sb out /\
    eval_operand op out = SOME (hashmap_slot slot (encode_hashmap_key kt kv)) /\
    (!x. op = Var x ==> not_fresh_at sb x)
Proof
  rpt gen_tac >> strip_tac >>
  `expr_sim_inv ce fp.jc_cx env en /\ expr_type idx = kt /\
   hashmap_key_type kt /\
   ?tv. evaluate_type (get_tenv fp.jc_cx) kt = SOME tv /\ value_has_type tv kv` by
    (irule mapping_subscript_key_typed >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `MAP FDOM es.scopes = MAP FDOM em.scopes` by
    (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `MAP FDOM em.scopes = MAP FDOM en.scopes` by
    (drule (SRULE [SF ETA_ss] bop_value_scopes_dom) >> simp[]) >>
  `eval_operand base_op s = SOME slot` by
    (irule eval_operand_frame >> conj_tac >- simp[] >>
     qexistsl_tac [`sm`, `t`] >>
     fs[intcall_expr_cont_def]) >>
  `!x. base_op = Var x ==> not_fresh_at sn x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sm` >> simp[]) >>
  `intcall_expr_res fp ce env en sn s /\ ~s.vs_halted /\
   s.vs_current_bb = sn.cs_current_bb /\
   s.vs_inst_idx = LENGTH sn.cs_current_insts` by fs[intcall_expr_cont_def] >>
  drule_all intcall_hashmap_tail_cont >> strip_tac >>
  rename1 `intcall_expr_cont fp ce env en sn s en sb out` >>
  `intcall_expr_cont fp ce env es sa s0 en sn s` by
    (irule intcall_expr_cont_trans >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `intcall_expr_cont fp ce env es sa s0 en sb out` by
    (irule intcall_expr_cont_trans >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `?selected. !tail.
     select_result fp.jc_cx (expr_type obj) (HashMapRef tr slot kt vt)
       (ValueSubscript kv) (en with gas_obs := tail) =
       (INL selected,en with gas_obs := tail)` by
    (irule mapping_subscript_selection_success >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`selected`, `out`] >> simp[]
QED
