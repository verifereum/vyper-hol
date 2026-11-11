(* Representation and source interfaces for the uniform struct endpoint. *)
Theory bodyPtrStructLitUniformFinalEndpoint
Ancestors bodyPtrMakeArrayPackage bodyPtrMakeArrayConsInvariant
  exprSimAggregateSource exprSimHyps valueEncoding valueEncodingDefs bodyPtrDefs
  fragGasPathPtr gasSummaryComposePtr vyperState exprSimProps compileEnv exprSimHash

Theorem structlit_uniform_endpoint_posts:
  literal_loop_frame ctx func ce cx d root aid addr capacity
    es sa s0 G0 tn0 ee sb G tn s (cells : (type_value # value # num # num) list) off /\
  expr_type e = StructT nsid /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (StructTV (ZIP (names,tvs))) /\
  LENGTH names = LENGTH tvs /\ LIST_REL value_has_type tvs vs /\
  val_wf (StructTV (ZIP (names,tvs))) (StructV (ZIP (names,vs))) /\
  type_memory_size_list tvs <= capacity /\
  type_memory_bytes ce (lowered_value_type ce e) <= capacity /\
  addr < dimword(:256) /\ post_value_type ce e = expr_type e /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    fields_in_memory (ZIP (names,vs)) (ZIP (names,tvs)) addr m) ==>
  vv_post ctx func ce cx e es sa sb s0 ee (Value (StructV (ZIP (names,vs))))
    (LocatedValue (expr_type e) (mk_ptr (Var root) LocMemory)) s /\
  ptr_vv_ok cx (expr_type e) (Value (StructV (ZIP (names,vs))))
    (LocatedValue (expr_type e) (mk_ptr (Var root) LocMemory)) ee G tn s /\
  ptr_buf_ok ce e (Var root) G s
Proof
  strip_tac >>
  `type_memory_size (StructTV (ZIP (names,tvs))) <= capacity` by
    simp[type_memory_size_def, struct_layout_size_zip] >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory (StructTV (ZIP (names,tvs))) (StructV (ZIP (names,vs))) addr m` by
    simp[val_in_memory_def] >>
  `~is_word_type (expr_type e)` by simp[is_word_type_def] >>
  `val_footprint (StructTV (ZIP (names,tvs))) (StructV (ZIP (names,vs))) <= capacity` by
    metis_tac[val_footprint_le, arithmeticTheory.LESS_EQ_TRANS] >>
  `val_in_memory (StructTV (ZIP (names,tvs))) (StructV (ZIP (names,vs))) addr s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  conj_tac >- (drule_all literal_loop_vv_post >> simp[]) >>
  drule_all literal_loop_pointer_posts >> simp[]
QED

Theorem structlit_uniform_action:
  eval_expr cx (StructLit ann nsid fields) =
  bind (eval_exprs cx (MAP SND fields))
    (return o (\vs. Value (StructV (ZIP (MAP FST fields,vs)))))
Proof
  simp[FUN_EQ_THM] >> gen_tac >>
  Cases_on `eval_exprs cx (MAP SND fields) x` >>
  drule aggregate_eval_struct >>
  disch_then (qspecl_then [`nsid`,`ann`] mp_tac) >>
  Cases_on `q` >> simp[bind_def, return_def]
QED

(* Preserve the original normal post while exposing its actual source run. *)
Theorem structlit_uniform_outcome_source_run:
  gas_outcome_ptr D tops (ctx,func) PG source (es,s,G0,tn0) Q R ==>
  gas_outcome_ptr D tops (ctx,func) PG source (es,s,G0,tn0)
    (\res ee G tn t. Q res ee G tn t /\
      ?gs. source (es with gas_obs := gs) = (res,ee)) R
Proof
  simp[gas_outcome_ptr_def] >> strip_tac >> qexists `marks`
  >- (disj1_tac >>
      qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _` mp_tac >>
      pure_rewrite_tac[gas_summary_ptr_at_def] >> strip_tac >>
      qexistsl [`res`, `es_end`, `G`, `tn`, `r`] >> simp[] >>
      first_x_assum (qspec_then `[]` assume_tac) >>
      gvs[] >> metis_tac[]) >>
  disj2_tac >> metis_tac[]
QED

(* Buffer metadata is not part of either semantic pointer observation. *)
Theorem structlit_uniform_pointer_posts_cong:
  p.ptr_operand = q.ptr_operand /\ p.ptr_location = q.ptr_location /\
  vv_post ctx func ce cx e es sa sb s0 ee raw (LocatedValue ty p) s /\
  ptr_vv_ok cx et raw (LocatedValue ty p) ee G tn s ==>
  vv_post ctx func ce cx e es sa sb s0 ee raw (LocatedValue ty q) s /\
  ptr_vv_ok cx et raw (LocatedValue ty q) ee G tn s
Proof
  strip_tac >> conj_tac >- metis_tac[vv_post_pointer_cong] >>
  gvs[ptr_vv_ok_def]
QED
