(* Tuple selections retain the owner of the actual base outcome. *)
Theory bodyIntCallPostProvenanceTupleSelector
Ancestors
  bodyIntCallPostProvenanceAttributeSelector exprSimTuple
  tupleMemoryLayout valueEncoding valueEncodingProps valueEncodingDefs
  loweringPosts context vyperAST words list typeLayoutProps exprSimProps
  stmtReasonVvMemory vyperState vyperTyping exprSimHypsDefs vyperTypeSystem
  bodyIntCallArgType bodyIntCallProducerInterface exprSimVVFrame
  bodyPtrSubscriptSeamTupleMemory bodyIntCallPostProvenanceSelectors
  compileEnv exprSimAttributeProps bodyPtrSubscriptSeamTupleSource
  exprLowering fragGasPath gasSummary gasSummaryCompose gasOutcome gasExemptCert
  gasContext fragGasMode venomInst venomState vyperInterpreter vyperValueOperation
  vyperTypeABI exprSimAttribute exprLoweringProps emitHelperProps fragExec
  placeTypingProps exprSimUnwrap

Theorem intcall_tuple_element_layout[local]:
  LENGTH vs = LENGTH tvs /\ k < LENGTH tvs /\
  val_wf (EL k tvs) (EL k vs) ==>
  sub_layout (TupleTV tvs) (ArrayV (TupleV vs))
    (SUM (TAKE k (MAP type_memory_size tvs))) (EL k tvs) (EL k vs) /\
  SUM (TAKE k (MAP type_memory_size tvs)) +
    val_footprint (EL k tvs) (EL k vs) <=
    val_footprint (TupleTV tvs) (ArrayV (TupleV vs))
Proof
  strip_tac >>
  `SUM (TAKE k (MAP type_memory_size tvs)) + type_memory_size (EL k tvs) <=
   type_memory_size_list tvs` by
    (mp_tac tuple_element_interval >>
     simp[MAP_TAKE, type_memory_size_list_sum]) >>
  conj_tac
  >- (simp[sub_layout_def, type_memory_size_def] >> rpt strip_tac >>
      gvs[val_in_memory_def, GSYM MAP_TAKE] >>
      irule tuple_in_memory_element >> simp[] >> goal_assum (drule_at Any)) >>
  drule val_footprint_le >>
  simp[val_footprint_def, type_memory_size_def]
QED

Theorem intcall_tuple_memory_provenance[local]:
  vv_post ctx func ce cx obj es sa sb s0 ee raw bvv t /\
  intcall_vv_provenance ce cx (TupleT tys) sa sb ee raw bvv t /\
  expr_sim_inv ce cx env es /\ expr_type obj = TupleT tys /\
  post_value_type ce obj = TupleT tys /\ vv_loc bvv = LocMemory /\
  OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) (EL k tys) = SOME (EL k tvs) /\
  ~dynarray_free (TupleTV tvs) /\ k < LENGTH tvs /\ LENGTH vs = LENGTH tvs /\
  read_result cx raw ee = (INL (ArrayV (TupleV vs)),ee) /\
  read_result cx result ee = (INL (EL k vs),ee) /\
  eval_operand (vv_operand bvv) t = SOME w /\
  eval_operand dst t = SOME (w + n2w (tuple_offset ce tys LocMemory k)) ==>
  intcall_vv_provenance ce cx (EL k tys) sa sb ee result
    (LocatedValue (EL k tys) (mk_ptr dst LocMemory)) t
Proof
  strip_tac >>
  `stmt_state_rel ctx func ce cx ee t /\
   vv_at ce cx (TupleT tys) sa sb ee raw bvv t` by gvs[vv_post_def] >>
  drule_all tuple_memory_child_address >> strip_tac >>
  drule_all tuple_memory_placement >> strip_tac >>
  `val_wf (EL k tvs) (EL k vs)` by
    metis_tac[tuple_child_wf] >>
  drule_all intcall_tuple_element_layout >> strip_tac >>
  irule intcall_dynamic_memory_selection >> goal_assum (drule_at Any) >>
  qexistsl_tac [`w + n2w (tuple_offset ce tys LocMemory k)`,
    `TupleT tys`, `bvv`, `vv_operand bvv`, `raw`] >> simp[] >>
  Cases_on `bvv` >>
  gvs[vv_loc_def, vv_location_def, vv_operand_def, is_word_type_def]
QED

Theorem intcall_tuple_selection_provenance[local]:
  vv_post ctx func ce cx obj es sa sb s0 ee raw bvv t /\
  intcall_vv_provenance ce cx (TupleT tys) sa sb ee raw bvv t /\
  expr_sim_inv ce cx env es /\ expr_type obj = TupleT tys /\
  post_value_type ce obj = TupleT tys /\
  OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) (EL k tys) = SOME (EL k tvs) /\
  k < LENGTH tvs /\ LENGTH vs = LENGTH tvs /\
  read_result cx raw ee = (INL (ArrayV (TupleV vs)),ee) /\
  read_result cx result ee = (INL (EL k vs),ee) /\
  ~expr_has_effect (Subscript (EL k tys) obj idx) /\
  vv_post ctx func ce cx (Subscript (EL k tys) obj idx) es sa sb s0 ee result
    (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) t /\
  eval_operand (vv_operand bvv) t = SOME w /\
  eval_operand dst t = SOME (w + n2w (tuple_offset ce tys (vv_loc bvv) k)) ==>
  intcall_vv_provenance ce cx (EL k tys) sa sb ee result
    (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) t
Proof
  strip_tac >>
  `post_value_type ce (Subscript (EL k tys) obj idx) = EL k tys` by
    simp[effect_free_post_value_type, expr_type_def] >>
  Cases_on `vv_loc bvv = LocMemory`
  >- (Cases_on `dynarray_free (TupleTV tvs)`
      >- (`dynarray_free (EL k tvs)` by
            (simp[dynarray_free_def] >> rpt strip_tac >>
             qpat_x_assum `dynarray_free (TupleTV tvs)`
               (mp_tac o REWRITE_RULE [dynarray_free_def]) >>
             disch_then (qspec_then `ValueSubscript (IntV (&k))::path` mp_tac) >>
             simp[mem_path_offset_def, mem_step_offset_def] >> metis_tac[]) >>
          qpat_x_assum `vv_post _ _ _ _ obj _ _ _ _ _ _ _ _` kall_tac >>
          qpat_x_assum `intcall_vv_provenance _ _ _ _ _ _ _ _ _` kall_tac >>
          gvs[vv_post_def, intcall_vv_provenance_def, mk_ptr_def,
              vv_at_def, expr_type_def] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
      simp[] >> irule intcall_tuple_memory_provenance >> goal_assum (drule_at Any) >> simp[] >>
      metis_tac[]) >>
  qpat_x_assum `vv_post _ _ _ _ obj _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `intcall_vv_provenance _ _ _ _ _ _ _ _ _` kall_tac >>
  gvs[vv_post_def, intcall_vv_provenance_def, mk_ptr_def, vv_holds_def,
      immutable_holds_def] >> strip_tac >> gvs[] >>
  qexistsl_tac [`name`, `off`, `itv`, `iv`, `k'`] >> simp[]
QED

Theorem intcall_tuple_summary[local]:
  expr_body_pre ce cx env (Subscript (EL k tys) obj (Literal ity (IntL (&k)))) es /\
  ~expr_has_effect (Subscript (EL k tys) obj (Literal ity (IntL (&k)))) /\
  expr_type obj = TupleT tys /\ post_value_type ce obj = TupleT tys /\
  compile_expr ce ty obj sa = (bvv,sm) /\ local_ptrs_reserved ce sa /\
  local_ptrs_reserved ce sm /\ sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [vv_operand bvv; Lit (n2w (tuple_offset ce tys (vv_loc bvv) k))]
    sm = (dst,sb) /\ fn_has_code sm sb func /\
  gas_marked_exec F (ctx,func) (eval_expr cx obj) (es,s0) marks (INL raw) fe (OK t) /\
  vv_post ctx func ce cx obj es sa sm s0 (fe with gas_obs := []) raw bvv t /\
  intcall_vv_provenance ce cx (expr_type obj) sa sm (fe with gas_obs := []) raw bvv t /\
  t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  gas_summary_at F (ctx,func) marks
    (eval_expr cx (Subscript (EL k tys) obj (Literal ity (IntL (&k))))) (es,s0)
    (\res ee u. ?tv. res = INL tv /\
      vv_post ctx func ce cx (Subscript (EL k tys) obj (Literal ity (IntL (&k))))
        es sa sb s0 ee tv (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      intcall_vv_provenance ce cx (EL k tys) sa sb ee tv
        (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) u) R
Proof
  strip_tac >>
  `eval_expr cx obj (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL raw,fe with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  drule_all intcall_attr_add_path >> strip_tac >>
  rename1 `gas_path ctx func t 0 (OK u)` >>
  `expr_body_pre ce cx env (Subscript (EL k tys) obj (Literal ity (IntL (&k))))
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  `vv_post ctx func ce cx obj
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) sa sb s0
     (fe with gas_obs := []) raw bvv u` by
    (gvs[vv_post_def, locals_kept_def, pure_frame_def, popped_kept_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all tuple_selected_source >> strip_tac >> gvs[] >>
  `expr_sim_inv ce cx env es` by gvs[expr_body_pre_def] >>
  `evaluate_type (get_tenv cx) (EL k tys) = SOME (EL k tvs)` by
    (drule exprSimAttributeFieldsTheory.opt_mmap_el >> disch_then (qspec_then `k` mp_tac) >> simp[]) >>
  drule select_result_memory_place >> strip_tac >>
  `vv_post ctx func ce cx (Subscript (EL k tys) obj (Literal ity (IntL (&k))))
     es sa sb s0 (fe with gas_obs := []) tv'
     (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) u` by
    (irule tuple_vv_post >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `intcall_vv_provenance ce cx (EL k tys) sa sb (fe with gas_obs := []) tv'
     (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) u` by
    (irule intcall_tuple_selection_provenance >> conj_tac
     >- (qexists_tac `w` >> simp[]) >>
     goal_assum (drule_at Any) >>
     simp[intcall_vv_provenance_gas_obs] >> metis_tac[]) >>
  gvs[intcall_vv_provenance_gas_obs] >>
  simp[gas_summary_at_def] >> qexistsl_tac [`INL tv'`,`fe`,`OK u`] >> simp[] >>
  `eval_expr cx (Subscript (EL k tys) obj (Literal ity (IntL (&k)))) =
   bind (eval_expr cx obj)
     (\r. select_result cx (expr_type obj) r (ValueSubscript (IntV (&k))))` by
    simp[FUN_EQ_THM, eval_expr_tuple_subscript] >>
  simp[] >>
  irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
    |> REWRITE_RULE [listTheory.APPEND_NIL]) >>
  qexistsl_tac [`fe`,`t`,`raw`] >> simp[] >>
  simp[gas_marked_exec_def, gas_marked_path_def, gas_explicit_def] >>
  drule tuple_selection_gas_obs >> simp[]
QED

Theorem intcall_tuple_exempt[local]:
  gas_exempt_cert memory tops p (ignore_bind (eval_expr cx obj) (return ()))
    start marks out endpoint ==>
  gas_exempt_cert memory tops p
    (ignore_bind (eval_expr cx (Subscript ann obj (Literal ity (IntL (&k))))) (return ()))
    start marks out endpoint
Proof
  strip_tac >>
  `eval_expr cx (Subscript ann obj (Literal ity (IntL (&k)))) =
   bind (eval_expr cx obj)
     (\r. select_result cx (expr_type obj) r (ValueSubscript (IntV (&k))))` by
    simp[FUN_EQ_THM, eval_expr_tuple_subscript] >> simp[] >>
  PairCases_on `p` >> PairCases_on `start` >>
  PairCases_on `out` >> PairCases_on `endpoint` >>
  qmatch_goalsub_abbrev_tac `bind (eval_expr cx obj) sel` >>
  `ignore_bind (bind (eval_expr cx obj) sel) (return ()) =
   bind (eval_expr cx obj) (\r. ignore_bind (sel r) (return ()))` by
    (simp[FUN_EQ_THM, ignore_bind_def, bind_def] >> gen_tac >>
     Cases_on `eval_expr cx obj x` >> Cases_on `q` >> simp[]) >>
  pop_assum SUBST1_TAC >> irule gas_exempt_cert_error_result >> simp[]
QED

Theorem intcall_tuple_subscript_outcome:
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
  expr_body_pre ce cx env (Subscript ann obj idx) es /\
  ~expr_has_effect (Subscript ann obj idx) /\ expr_type obj = TupleT tys /\
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
  strip_tac >> drule_all tuple_pre_base >> strip_tac >> gvs[] >>
  `place_type ce obj = ValPT (TupleT tys) /\ post_value_type ce obj = TupleT tys` by
    (conj_tac
     >- (qpat_assum `expr_type obj = TupleT tys` (fn th => once_rewrite_tac[GSYM th]) >>
         irule place_type_well_typed_on_defined >>
         gvs[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
     simp[effect_free_post_value_type]) >>
  drule_all compile_expr_tuple_subscript >> strip_tac >> gvs[literal_int_index_def] >>
  rename1 `compile_expr ce ty obj sa = (bvv,sm)` >>
  drule attr_extends >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `gas_admissible (eval_expr cx obj) expr_vv_res_ok es` by
    metis_tac[exprSimHypsTheory.expr_body_pre_vv_gas_admissible] >>
  `~expr_has_effect obj` by gvs[] >>
  `local_ptrs_reserved ce sm` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  first_x_assum drule_all >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >> gvs[]
      >- (irule intcall_tuple_summary >> simp[] >>
          conj_tac >- metis_tac[] >>
          qexistsl_tac [`es_end`,`tv`,`sm`,`t`,`ty`] >> simp[]) >>
      Cases_on `res` >> gvs[] >>
      simp[gas_summary_at_def] >> qexistsl_tac [`INR y`,`es_end`,`r`] >> simp[] >>
      `eval_expr cx (Subscript (EL k tys) obj (Literal ity (IntL (&k)))) =
       bind (eval_expr cx obj)
         (\v. select_result cx (expr_type obj) v (ValueSubscript (IntV (&k))))` by
        simp[FUN_EQ_THM, eval_expr_tuple_subscript] >>
      simp[] >> irule gas_marked_exec_bind_exception >> simp[]) >>
  qexists_tac `marks` >> disj2_tac >> metis_tac[intcall_tuple_exempt]
QED
