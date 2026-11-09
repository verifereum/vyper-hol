(* Counted composition of the mapping base and the forced key. *)
Theory bodyIntCallFamAggSubscriptBaseOutcome
Ancestors
  bodyIntCallFamAggSubscriptKeyProducer bodyIntCallFamAggSubscriptCompile
  bodyIntCallJointContract exprSimSubscriptMap exprSimMapKey exprOperandVar
  exprSimHyps exprSimMapDefs vyperTypeInvariants gasSummary
  loweringPosts context compileEnv

Theorem intcall_mapping_base_outcome:
  intcall_map_producer fp obj /\ intcall_forced_producer fp idx /\
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  (expr_body_pre ce fp.jc_cx env (Subscript ann obj idx) es \/
   expr_map_pre ce fp.jc_cx env (Subscript ann obj idx) es) /\
  place_type ce obj = MapPT kt vt /\
  supported_place_expr fp.jc_tops obj /\
  supportedExprs$supported_expr fp.jc_tops idx /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr obj) /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr idx) /\
  compile_expr ce ty obj sa = (bvv,sm) /\
  lower_value compile_expr ce (expr_type idx) idx sm = (key,sn) /\
  (if is_bytestring_type kt then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  compile_mapping_subscript (vv_operand bvv) hashed sp = (op,sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  gas_admissible (eval_expr fp.jc_cx (Subscript ann obj idx)) A es /\
  (!ex. A (INR ex) ==> expr_map_res_ok (INR ex)) /\
  intcall_joint_res fp ce env es sa s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_expr fp.jc_cx (Subscript ann obj idx)) (es,s0)
    (\res en out. ?tr slot kv selected tp p.
      res = INL selected /\
      storage_mapping_region fp.jc_cx tr slot (HashMapT kt vt) /\
      bvv = LocatedValue tp p /\ p.ptr_location = slot_loc tr /\
      select_result fp.jc_cx (expr_type obj) (HashMapRef tr slot kt vt)
        (ValueSubscript kv) en = (INL selected,en) /\
      eval_operand op out = SOME (hashmap_slot slot (encode_hashmap_key kt kv)) /\
      (!x. op = Var x ==> not_fresh_at sb x) /\
      intcall_expr_cont fp ce env es sa s0 en sb out)
    (\res en r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all intcall_mapping_compile_cuts >> strip_tac >>
  `expr_map_pre ce fp.jc_cx env obj es` by
    metis_tac[expr_body_pre_map_subscript_base, expr_map_pre_subscript_base] >>
  `type_place_expr env obj = SOME (HashMapT kt vt)` by
    (drule_all expr_map_pre_checked_type >> simp[]) >>
  `!lbl. vv_operand bvv <> Label lbl` by
    (drule_all compile_mapping_operand_not_label >> simp[]) >>
  `gas_admissible (eval_expr fp.jc_cx obj) expr_map_res_ok es` by
    (irule subscript_result_base_admissible >>
     qexistsl_tac [`A`, `ann`, `idx`] >> simp[]) >>
  qpat_x_assum `intcall_map_producer _ _` mp_tac >>
  rewrite_tac[intcall_map_producer_def] >> disch_then drule_all >>
  rewrite_tac[eval_subscript_bind] >>
  disch_then (mp_then Any irule gas_outcome_bind_result_exec) >>
  reverse conj_tac
  >- (conj_tac
      >- (rpt gen_tac >> Cases_on `res` >> simp[] >> rpt strip_tac >> simp[]) >>
      rpt gen_tac >> simp[] >> rpt strip_tac >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `(\res ee u. _) _ _ _` mp_tac >> simp[] >> strip_tac >>
  rename1 `v = HashMapRef tr slot bkt bvt` >>
  `bkt = kt /\ bvt = vt` by
    (`eval_expr fp.jc_cx obj
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
        (INL v, mid with gas_obs := [])` by
       (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
        pure_rewrite_tac[gas_marked_exec_def] >>
        disch_then (CONJUNCTS_THEN2 (qspec_then `[]` mp_tac) kall_tac) >> simp[]) >>
     qpat_assum `eval_expr _ _ (_ with gas_obs := _) = _`
       (mp_then Any mp_tac expr_map_pre_eval_result) >>
     disch_then (qspecl_then [`ce`, `env`] mp_tac) >>
     simp[] >> strip_tac >>
     first_x_assum (qspec_then `HashMapT kt vt` mp_tac) >>
     simp[eval_result_typed_def]) >>
  gnvs[vv_operand_def] >>
  drule_all intcall_mapping_key_producer >>
  disch_then (mp_then Any irule gas_outcome_conseq) >>
  simp[] >> rpt strip_tac >>
  qexistsl_tac [`tr`, `slot`, `kv`, `selected`] >> simp[]
QED
